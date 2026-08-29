(() => {
  "use strict";

  /*
   * Application map
   * 1. Authenticate and keep the session only in memory.
   * 2. Resolve a profile/post, harvest accounts, and remove safety exclusions.
   * 3. Let the user review the remaining DIDs and choose a destination list.
   * 4. Persist only the resumable queue, then serialize writes with a tab lease.
   * 5. Reconcile remote state before and after uncertain writes.
   * 6. Optionally activate the finished moderation list for the signed-in user.
   *
   * Remote values are always inserted as text nodes. Credentials and access
   * tokens must never be written to browser storage.
   */

  // Bluesky service details, conservative batching limits, and local safeguards.
  const SERVICE            = "https://bsky.social";
  const PAGE_LIMIT         = 100;
  const BATCH_SIZE         = 100;
  const POINTS_PER_CREATE  = 3;
  const POINTS_PER_DELETE  = 1;
  const POINTS_BUDGET      = 4500;
  const INTER_REQUEST_MS   = 150;
  const INTER_BATCH_MS     = 1000;
  const FETCH_TIMEOUT_MS   = 30000;
  const SETTLE_MS          = 3000;
  const HARVEST_SOFT_CAP   = 5000;
  const HARVEST_HARD_CAP   = 25000;
  const QUEUE_TTL_MS       = 14 * 24 * 3600 * 1000;
  const LOCK_TTL_MS        = 20000;
  const LOCK_BEAT_MS       = 5000;
  const APP_PW_RE          = /^[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}$/;
  const HANDLE_RE          = /^([a-zA-Z0-9]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?\.)+[a-zA-Z]([a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?$/;
  const DID_RE             = /^did:(plc|web):.+$/;
  const TID_RE             = /^[234567abcdefghij][234567abcdefghijklmnopqrstuvwxyz]{12}$/;
  const TID_ALPHABET       = "234567abcdefghijklmnopqrstuvwxyz";
  const lsQueueKey = did => "modlistbuilder.queue.v4." + did;
  const lsLockKey  = did => "modlistbuilder.lock.v4."  + did;

  /*
   * AT Protocol record keys in these collections must be 13-character TIDs.
   * Newly created lists use a clock-based TID. Membership and activation keys
   * use a SHA-256-derived 63-bit value, making retries idempotent while still
   * satisfying the TID grammar. A deterministic TID's timestamp is intentionally
   * meaningless; only its stable, valid encoding matters.
   */
  async function sha256bytes(s) {
    const buf = await crypto.subtle.digest("SHA-256", new TextEncoder().encode(s));
    return new Uint8Array(buf);
  }

  function encodeTid(value) {
    let encoded = "";
    for (let index = 0; index < 13; index += 1) {
      // Prepending each low five-bit digit produces the required big-endian text.
      encoded = TID_ALPHABET[Number(value & 31n)] + encoded;
      value >>= 5n;
    }
    return encoded;
  }

  async function deterministicTid(seed) {
    const bytes = await sha256bytes(seed);
    let value = 0n;
    for (let index = 0; index < 8; index += 1) value = (value << 8n) | BigInt(bytes[index]);
    value &= (1n << 63n) - 1n; // A TID carries 63 usable bits in 13 base-32 digits.
    return encodeTid(value);
  }

  let lastTidMicros = 0n;
  function nextTid() {
    let micros = BigInt(Date.now()) * 1000n;
    if (micros <= lastTidMicros) micros = lastTidMicros + 1n;
    lastTidMicros = micros;
    const clockId = crypto.getRandomValues(new Uint16Array(1))[0] & 1023;
    return encodeTid((micros << 10n) | BigInt(clockId));
  }

  const rkeyForItem = async (listUri, did) =>
    deterministicTid("item|" + listUri + "|" + did);
  const rkeyForListblock = async listUri =>
    deterministicTid("lblk|" + listUri);
  const newListTid = () => nextTid();
  const rkeyFromAtUri = uri => uri.slice(uri.lastIndexOf("/") + 1);

  // One mutable state object makes the screen transitions and resume path explicit.
  // The queue stores only DIDs; display metadata is deliberately non-authoritative.
  const state = {
    // Authentication: these values exist only until the page is closed or reloaded.
    session: null,
    screen: "auth",

    // Read phase: resolved source and the safety-filtered account summaries.
    target: null,
    harvested: [],
    excludedFollows: 0,
    excludedExisting: 0,
    followedIncluded: 0,

    // Destination identity. pendingList* bridges a crash during list creation.
    listUri: null,
    listName: null,
    listDescription: null,
    pendingListRkey: null,
    pendingListCreatedAt: null,
    listActive: null,
    mode: null,

    // Durable execution accounting. selectedTotal equals every terminal outcome
    // plus the number of DIDs still waiting in queue.
    queue: [],
    selectedTotal: 0,
    written: 0,
    unfollowed: 0,
    skippedSafety: 0,
    conflicts: 0,
    subscribePending: false,

    // Rate-window and controller flags are maintained around every write boundary.
    pointsUsed: 0,
    pointsWindowStart: 0,
    running: false,
    runId: null,
    pauseRequested: false,
    abort: null,
  };

  const RATE = Symbol("rate");
  const el = id => document.getElementById(id);
  const screens = ["auth", "target", "fetching", "preview", "executing", "paused", "done", "error"];

  // Controller-only values below are transient and are never part of a saved run.
  let storageHealthy = true;
  let heartbeatTimer = null;
  let countdownTimer = null;
  let resumeTimer = null;
  let pauseUntil = 0;
  let pauseKind = null;
  let permanentLeaseLoss = false;
  let previewRenderToken = 0;
  let lastProgressPaint = 0;
  let errorBackScreen = "target";
  let subscriptionFailed = false;
  const listOptions = new Map();
  // Populated by the latest safety scan. Entries are consumed only by atomic
  // delete-follow/create-membership batches and are never persisted.
  const followRkeys = new Map();

  // ---------------------------------------------------------------------------
  // DOM, accessibility, and small validation helpers
  // ---------------------------------------------------------------------------

  // This is the sole screen switcher, so focus and scroll behavior stay consistent.
  function setScreen(name, { focus = true } = {}) {
    if (!screens.includes(name)) return;
    for (const screen of screens) el("screen-" + screen).hidden = screen !== name;
    state.screen = name;
    const heading = el("screen-" + name).querySelector("h2") || el("screen-" + name).querySelector("h1");
    if (heading && focus) {
      heading.tabIndex = -1;
      heading.focus({ preventScroll: true });
    }
    const reducedMotion = window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    window.scrollTo({ top: 0, behavior: reducedMotion ? "auto" : "smooth" });
  }

  function clearNode(node) {
    node.replaceChildren();
  }

  // Isolate user-controlled text bidirectionally and never interpret it as markup.
  function bdi(text) {
    const node = document.createElement("bdi");
    node.textContent = String(text ?? "");
    return node;
  }

  function setRemoteText(node, prefix, remote) {
    clearNode(node);
    if (prefix) node.append(document.createTextNode(prefix));
    node.append(bdi(remote));
  }

  // The global banner is reserved for state that applies across workflow screens.
  function showBanner(message, tone = "info") {
    const node = el("global-banner");
    node.textContent = message;
    node.dataset.tone = tone;
    node.hidden = false;
  }

  function hideBanner() {
    el("global-banner").hidden = true;
  }

  const errorControls = {
    "auth-error": ["handle-input", "password-input"],
    "target-error": ["target-input", "list-name", "list-desc", "list-select"],
  };

  // Keep the visible error, ARIA invalid state, and focus target synchronized.
  function showFieldError(id, message, invalidIds = [], focusInvalid = false) {
    const node = el(id);
    node.textContent = message;
    node.hidden = !message;
    for (const controlId of errorControls[id] ?? []) el(controlId).removeAttribute("aria-invalid");
    if (message) {
      for (const controlId of invalidIds) el(controlId)?.setAttribute("aria-invalid", "true");
      if (focusInvalid && invalidIds.length) el(invalidIds[0])?.focus();
    }
  }

  function showInlineError(id, err) {
    const node = el(id);
    clearNode(node);
    if (err?.kind === "auth") {
      node.append(document.createTextNode("Sign-in failed: "));
      node.append(bdi(err.message || "Authentication failed."));
    } else if (err?.kind === "xrpc") {
      node.append(document.createTextNode("Bluesky rejected the request ("));
      node.append(bdi(err.name || "Unknown"));
      node.append(document.createTextNode("): "));
      node.append(bdi(err.message || "Request rejected."));
    } else {
      node.textContent = describeError(err);
    }
    node.hidden = false;
  }

  // Busy state disables duplicate submissions and exposes activity to assistive tech.
  function setBusy(button, busy) {
    button.disabled = busy;
    button.setAttribute("aria-busy", String(Boolean(busy)));
  }

  function sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }

  function jitter() {
    return Math.floor(Math.random() * 1001);
  }

  // DID/URI checks defend trust boundaries; API and saved-storage values are not
  // assumed valid merely because they came from Bluesky or this application.
  function validDid(value) {
    return typeof value === "string" && DID_RE.test(value);
  }

  function validOwnListUri(value) {
    if (!state.session || typeof value !== "string") return false;
    const prefix = "at://" + state.session.did + "/app.bsky.graph.list/";
    return value.startsWith(prefix) && TID_RE.test(rkeyFromAtUri(value));
  }

  function isRecordNotFound(err) {
    return err?.kind === "xrpc" && err.name === "RecordNotFound";
  }

  // Bluesky applies different limits to encoded bytes and visible graphemes.
  function utf8Length(value) {
    return new TextEncoder().encode(value).length;
  }

  function graphemeLength(value) {
    if (typeof Intl.Segmenter === "function") {
      return [...new Intl.Segmenter(undefined, { granularity: "grapheme" }).segment(value)].length;
    }
    return [...value].length;
  }

  // Accept a Bluesky profile URL, post URL, handle, or DID and normalize its shape.
  function parseTarget(raw) {
    raw = String(raw ?? "").trim();
    let match = raw.match(/^https?:\/\/bsky\.app\/profile\/([^\/\s]+)\/post\/([a-z0-9]+)\/?(?:\?.*)?$/i);
    if (match) return { kind: "post", handle: match[1], rkey: match[2] };
    match = raw.match(/^https?:\/\/bsky\.app\/profile\/([^\/\s]+)\/?(?:\?.*)?$/i);
    if (match) return { kind: "profile", handle: match[1], rkey: null };
    raw = raw.replace(/^@/, "");
    if (HANDLE_RE.test(raw) || raw.startsWith("did:")) {
      return { kind: "profile", handle: raw, rkey: null };
    }
    return null;
  }

  // A lightweight opt-in smoke suite runs when the page is loaded with #test.
  function runSelfTests() {
    if (location.hash !== "#test") return;
    const cases = [
      ["https://bsky.app/profile/alice.bsky.social", "profile", "alice.bsky.social", null],
      ["https://bsky.app/profile/did:plc:abc/post/3kxyzq2", "post", "did:plc:abc", "3kxyzq2"],
      ["https://bsky.app/profile/alice.bsky.social/post/3kxyzq2?ref=x", "post", "alice.bsky.social", "3kxyzq2"],
      ["@alice.bsky.social", "profile", "alice.bsky.social", null],
      ["alice.bsky.social", "profile", "alice.bsky.social", null],
      ["did:plc:abc123", "profile", "did:plc:abc123", null],
    ];
    for (const [input, kind, handle, rkey] of cases) {
      const result = parseTarget(input);
      console.assert(result?.kind === kind && result?.handle === handle && result?.rkey === rkey, "parseTarget", input);
    }
    for (const input of ["https://bsky.app/hashtag/foo", "alice", "random text"]) {
      console.assert(parseTarget(input) === null, "parseTarget invalid", input);
    }
    Promise.all([
      rkeyForItem("at://did:plc:me/app.bsky.graph.list/l1", "did:plc:subject"),
      rkeyForItem("at://did:plc:me/app.bsky.graph.list/l1", "did:plc:subject"),
      rkeyForItem("at://did:plc:me/app.bsky.graph.list/l2", "did:plc:subject"),
      rkeyForListblock("at://did:plc:me/app.bsky.graph.list/l1"),
    ]).then(([a, b, c, d]) => {
      console.assert(a === b, "same list and DID must have same rkey");
      console.assert(a !== c, "same DID on different lists must have different rkeys");
      console.assert(TID_RE.test(a) && TID_RE.test(c) && TID_RE.test(d) && TID_RE.test(newListTid()), "TID rkey format");
    });
  }

  /*
   * Central XRPC transport. It owns authorization, request cancellation,
   * response parsing, rate-limit metadata, and the app's normalized error kinds.
   * Keeping those decisions here makes callers operate on predictable failures.
   */
  async function api(method, nsid, { params, body, auth = true, token } = {}) {
    const url = new URL(SERVICE + "/xrpc/" + nsid);
    if (method === "GET" && params) {
      for (const [key, value] of Object.entries(params)) {
        if (value !== undefined && value !== null) url.searchParams.set(key, String(value));
      }
    }
    const headers = {};
    if (body !== undefined) headers["Content-Type"] = "application/json";
    if (auth) {
      const bearer = token ?? state.session?.accessJwt;
      if (!bearer) throw { kind: "auth", message: "No active session." };
      headers.Authorization = "Bearer " + bearer;
    }

    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort("timeout"), FETCH_TIMEOUT_MS);
    const phaseSignal = state.abort?.signal;
    const abortPhase = () => controller.abort("phase");
    if (phaseSignal) phaseSignal.addEventListener("abort", abortPhase, { once: true });
    let response;
    let responseText;
    try {
      response = await fetch(url, {
        method,
        headers,
        body: body === undefined ? undefined : JSON.stringify(body),
        signal: controller.signal,
      });
      // Read once as text because successful endpoints may legitimately return no body.
      responseText = await response.text();
    } catch (cause) {
      throw { kind: "network", aborted: controller.signal.aborted, cause };
    } finally {
      clearTimeout(timeout);
      if (phaseSignal) phaseSignal.removeEventListener("abort", abortPhase);
    }

    const text = responseText;
    let json = {};
    if (text) {
      try {
        json = JSON.parse(text);
      } catch {
        if (response.ok) throw { kind: "badbody", nsid };
        json = { error: "Unknown", message: text.slice(0, 200) };
      }
    }
    const resetValue = Number(response.headers.get("ratelimit-reset"));
    const remainingValue = Number(response.headers.get("ratelimit-remaining"));
    const rate = {
      resetAt: Number.isFinite(resetValue) && resetValue > 0 ? resetValue * 1000 : 0,
      remaining: Number.isFinite(remainingValue) ? remainingValue : null,
    };
    if (response.ok) {
      if (json && typeof json === "object") Object.defineProperty(json, RATE, { value: rate });
      return json;
    }
    if (response.status === 429) {
      throw { kind: "ratelimit", resetAt: rate.resetAt || Date.now() + 60000 };
    }
    if (response.status === 401 && json.error === "ExpiredToken") throw { kind: "expired" };
    if ((response.status === 400 || response.status === 401) && json.error === "AuthFactorTokenRequired") {
      throw { kind: "needs2fa" };
    }
    const loginAuthError = nsid === "com.atproto.server.createSession" && response.status === 400 &&
      ["AuthenticationRequired", "AccountTakedown", "InvalidRequest"].includes(json.error);
    if (response.status === 401 || loginAuthError) {
      throw { kind: "auth", message: json.message || "Authentication failed." };
    }
    if (response.status >= 400 && response.status < 500) {
      throw { kind: "xrpc", name: json.error || "Unknown", message: json.message || "Request rejected.", status: response.status };
    }
    throw { kind: "server", status: response.status };
  }

  // Refresh an expired access token once, then replay the original operation.
  async function apiWithRefresh(method, nsid, options = {}) {
    try {
      return await api(method, nsid, options);
    } catch (err) {
      if (err?.kind !== "expired" || options.auth === false) throw err;
      try {
        const refreshed = await api("POST", "com.atproto.server.refreshSession", {
          token: state.session.refreshJwt,
          body: undefined,
        });
        state.session.accessJwt = refreshed.accessJwt;
        state.session.refreshJwt = refreshed.refreshJwt;
        return await api(method, nsid, options);
      } catch {
        throw { kind: "expired" };
      }
    }
  }

  // Retry only transient reads; writes are handled separately because their result
  // can be ambiguous after a network failure.
  async function readWithRetry(nsid, params) {
    const delays = [0, 2000, 8000];
    let lastError;
    for (let attempt = 0; attempt < delays.length; attempt += 1) {
      if (delays[attempt]) await sleep(delays[attempt] + jitter());
      try {
        return await apiWithRefresh("GET", nsid, { params });
      } catch (err) {
        lastError = err;
        if (err?.kind === "network" && err.aborted && state.abort?.signal.aborted) throw err;
        if (!(["network", "server"].includes(err?.kind))) throw err;
      }
    }
    throw lastError;
  }

  // Generic cursor pagination fails closed on repeated cursors or oversized results.
  async function paginate(nsid, params, extract, { cap = Infinity, onCount } = {}) {
    const out = [];
    let cursor;
    const seen = new Set();
    do {
      const page = await readWithRetry(nsid, {
        ...params,
        limit: PAGE_LIMIT,
        ...(cursor ? { cursor } : {}),
      });
      const items = extract(page);
      if (!Array.isArray(items)) throw { kind: "badbody", nsid };
      out.push(...items);
      if (onCount) onCount(out.length);
      if (out.length > cap) throw { kind: "toolarge", count: out.length };
      cursor = page.cursor;
      if (cursor) {
        if (seen.has(cursor)) throw { kind: "pagination", nsid };
        seen.add(cursor);
      }
      await sleep(INTER_REQUEST_MS);
    } while (cursor);
    return out;
  }

  // Translate internal error kinds into safe, user-facing recovery guidance.
  function describeError(err) {
    switch (err?.kind) {
      case "auth": return "Sign-in failed: " + (err.message || "Authentication failed.");
      case "needs2fa": return "This account requires an email code for main-password sign-in. Use an app password instead (Settings → App Passwords).";
      case "expired": return "Session expired — sign in again to resume.";
      case "ratelimit": return "Bluesky rate limit reached.";
      case "toolarge": return "More than 25,000 accounts — this tool caps runs at 25,000 to stay within Bluesky's limits.";
      case "network": return "Network problem. Progress is saved — press Resume to retry.";
      case "server": return "Bluesky server error (" + err.status + "). Progress is saved — press Resume to retry.";
      case "xrpc": return "Bluesky rejected the request (" + (err.name || "Unknown") + "): " + (err.message || "Request rejected.");
      case "badbody": return "Unexpected response from Bluesky. Try again.";
      case "pagination": return "Bluesky returned inconsistent data while listing accounts. Nothing further has been written.";
      case "toolost": return "Another tab took over this job.";
      case "locked": return "Another tab is already running this job.";
      case "storage": return err.message || "This browser cannot create the safety lock required for writing.";
      case "corrupt": return "Saved progress is inconsistent and cannot be resumed safely.";
      case "missinglist": return "That list no longer exists.";
      default: return "Unexpected problem. Please try again.";
    }
  }

  // The error screen accepts a safe return destination selected by the failed phase.
  function showError(err, backScreen = "target", override) {
    errorBackScreen = backScreen;
    const message = override || describeError(err);
    const node = el("error-text");
    if (err?.kind === "xrpc") {
      clearNode(node);
      node.append(document.createTextNode("Bluesky rejected the request ("));
      node.append(bdi(err.name || "Unknown"));
      node.append(document.createTextNode("): "));
      node.append(bdi(err.message || "Request rejected."));
    } else {
      node.textContent = message;
    }
    setScreen("error");
  }

  // ---------------------------------------------------------------------------
  // Session lifecycle and event wiring
  // ---------------------------------------------------------------------------

  // App-password validation happens before the credential is sent. The password is
  // cleared from both the form and this local variable on every exit path.
  async function login(event) {
    event.preventDefault();
    if (state.running) return;
    state.running = true;
    const button = el("login-btn");
    setBusy(button, true);
    showFieldError("auth-error", "");
    let password = el("password-input").value;
    try {
      if (!APP_PW_RE.test(password)) {
        showFieldError("auth-error", "Enter an app password (format xxxx-xxxx-xxxx-xxxx). Never use your main account password. Create one at bsky.app → Settings → App Passwords.", ["password-input"], true);
        return;
      }
      const identifier = el("handle-input").value.trim().replace(/^@/, "");
      if (!identifier) {
        showFieldError("auth-error", "Enter your Bluesky handle.", ["handle-input"], true);
        return;
      }
      const result = await api("POST", "com.atproto.server.createSession", {
        auth: false,
        body: { identifier, password },
      });
      if (!validDid(result.did) || typeof result.handle !== "string" ||
          typeof result.accessJwt !== "string" || typeof result.refreshJwt !== "string") {
        throw { kind: "badbody" };
      }
      state.session = {
        did: result.did,
        handle: result.handle,
        accessJwt: result.accessJwt,
        refreshJwt: result.refreshJwt,
      };
      setRemoteText(el("signed-in-text"), "Signed in as @", result.handle);
      hideBanner();
      resetRun();
      setScreen("target");
      checkSavedRun();
    } catch (err) {
      showInlineError("auth-error", err);
    } finally {
      el("password-input").value = "";
      password = "";
      state.running = false;
      setBusy(button, false);
    }
  }

  function logout() {
    // Reloading clears the closure, guaranteeing that token references disappear.
    stopTimers();
    state.session = null;
    location.reload();
  }

  // Reset all per-run data while preserving the current in-memory session.
  function resetRun() {
    stopTimers();
    const session = state.session;
    Object.assign(state, {
      session,
      screen: "target",
      target: null,
      harvested: [],
      excludedFollows: 0,
      excludedExisting: 0,
      followedIncluded: 0,
      listUri: null,
      listName: null,
      listDescription: null,
      pendingListRkey: null,
      pendingListCreatedAt: null,
      listActive: null,
      mode: null,
      queue: [],
      selectedTotal: 0,
      written: 0,
      unfollowed: 0,
      skippedSafety: 0,
      conflicts: 0,
      subscribePending: false,
      pointsUsed: 0,
      pointsWindowStart: 0,
      running: false,
      runId: null,
      pauseRequested: false,
      abort: null,
    });
    permanentLeaseLoss = false;
    subscriptionFailed = false;
    listOptions.clear();
    followRkeys.clear();
    el("filter-input").value = "";
    clearNode(el("preview-list"));
    updateProgress(true);
  }

  function stopTimers() {
    // Timers are process-local and must not survive a reset or account change.
    clearInterval(heartbeatTimer);
    clearInterval(countdownTimer);
    clearTimeout(resumeTimer);
    heartbeatTimer = null;
    countdownTimer = null;
    resumeTimer = null;
  }

  // Event binding is centralized so the document can keep a strict no-inline-script CSP.
  function bindEvents() {
    el("skip-link").addEventListener("click", event => {
      event.preventDefault();
      const heading = el("screen-" + state.screen).querySelector("h2, h1");
      if (heading) {
        heading.tabIndex = -1;
        heading.focus({ preventScroll: true });
        heading.scrollIntoView({ block: "start" });
      } else {
        el("app-main").focus();
      }
    });
    el("login-form").addEventListener("submit", login);
    el("logout-btn").addEventListener("click", logout);
    el("op-create").addEventListener("change", updateOperationFields);
    el("op-append").addEventListener("change", updateOperationFields);
    el("list-select").addEventListener("change", updateSelectedList);
    el("fetch-btn").addEventListener("click", startFetch);
    el("cancel-fetch-btn").addEventListener("click", cancelFetch);
    el("filter-input").addEventListener("input", filterPreview);
    el("select-shown-btn").addEventListener("click", () => setShownSelection(true));
    el("deselect-shown-btn").addEventListener("click", () => setShownSelection(false));
    el("back-btn").addEventListener("click", () => setScreen("target"));
    el("execute-btn").addEventListener("click", startExecution);
    el("pause-btn").addEventListener("click", requestPause);
    el("resume-btn").addEventListener("click", resumeExecution);
    el("resume-saved-btn").addEventListener("click", resumeSavedRun);
    el("discard-saved-btn").addEventListener("click", discardSavedRun);
    el("retry-subscribe-btn").addEventListener("click", retrySubscription);
    el("again-btn").addEventListener("click", () => { resetRun(); setScreen("target"); });
    el("error-back-btn").addEventListener("click", () => setScreen(errorBackScreen));
    for (const id of errorControls["auth-error"]) {
      el(id).addEventListener("input", event => {
        if (event.currentTarget.hasAttribute("aria-invalid")) showFieldError("auth-error", "");
      });
    }
    for (const id of errorControls["target-error"]) {
      const eventName = id === "list-select" ? "change" : "input";
      el(id).addEventListener(eventName, event => {
        if (event.currentTarget.hasAttribute("aria-invalid")) showFieldError("target-error", "");
      });
    }
    window.addEventListener("beforeunload", releaseLease);
  }

  runSelfTests();
  bindEvents();
  updateOperationFields();
  // Do not steal focus on initial page load; subsequent workflow transitions do
  // focus their heading so screen-reader users hear the new context.
  setScreen("auth", { focus: false });

  // ---------------------------------------------------------------------------
  // Destination selection
  // ---------------------------------------------------------------------------

  // Switching to append mode lazily fetches the signed-in user's eligible lists.
  async function updateOperationFields() {
    const append = el("op-append").checked;
    el("create-fields").hidden = append;
    el("append-fields").hidden = !append;
    el("subscribe-check").checked = !append;
    el("subscribe-label").hidden = false;
    if (append && state.session && listOptions.size === 0) await loadLists();
  }

  // Keep only owned moderation lists with a syntactically valid AT URI and TID key.
  async function loadLists() {
    if (state.running || !state.session) return;
    state.running = true;
    const select = el("list-select");
    const status = el("list-load-status");
    select.disabled = true;
    status.textContent = "Loading your moderation lists…";
    try {
      const lists = await paginate(
        "app.bsky.graph.getLists",
        { actor: state.session.did },
        page => page.lists,
      );
      listOptions.clear();
      clearNode(select);
      const prompt = document.createElement("option");
      prompt.value = "";
      prompt.textContent = "Choose a list";
      select.append(prompt);
      for (const list of lists.filter(item => item.purpose === "app.bsky.graph.defs#modlist" && validOwnListUri(item.uri))) {
        const option = document.createElement("option");
        option.value = list.uri;
        option.textContent = list.name + " (" + (list.listItemCount ?? 0) + ")";
        option.dir = "auto";
        select.append(option);
        listOptions.set(list.uri, list);
      }
      status.textContent = listOptions.size ? "" : "No moderation lists yet — create one instead.";
    } catch (err) {
      if (err?.kind === "expired") {
        showBanner("Session expired — sign in again to resume.", "warning");
        state.session = null;
        setScreen("auth");
        return;
      }
      clearNode(status);
      if (err?.kind === "xrpc") {
        status.append(document.createTextNode("Bluesky rejected the request ("));
        status.append(bdi(err.name || "Unknown"));
        status.append(document.createTextNode("): "));
        status.append(bdi(err.message || "Request rejected."));
      } else {
        status.textContent = describeError(err);
      }
    } finally {
      select.disabled = false;
      state.running = false;
    }
  }

  function updateSelectedList() {
    // An already blocked/muted list needs no new activation record after appending.
    const list = listOptions.get(el("list-select").value);
    state.listUri = list?.uri ?? null;
    state.listName = list?.name ?? null;
    state.listDescription = list?.description ?? "";
    state.listActive = list ? {
      blocked: Boolean(list.viewer?.blocked),
      muted: Boolean(list.viewer?.muted),
    } : null;
    const active = Boolean(state.listActive?.blocked || state.listActive?.muted);
    el("subscribe-label").hidden = active;
    if (active) el("subscribe-check").checked = false;
  }

  // Validate destination metadata against Bluesky's byte and grapheme constraints.
  function validateDestination() {
    const op = el("op-append").checked ? "append" : "create";
    const action = el("action-mute").checked ? "mute" : "block";
    const unfollowFollowed = el("unfollow-followed").checked;
    if (op === "create") {
      const name = el("list-name").value.trim();
      const description = el("list-desc").value;
      if (utf8Length(name) < 1) return { error: "Enter a list name.", field: "list-name" };
      if (utf8Length(name) > 64) return { error: "List name must be 64 UTF-8 bytes or fewer.", field: "list-name" };
      if (graphemeLength(description) > 300) return { error: "Description must be 300 graphemes or fewer.", field: "list-desc" };
      if (utf8Length(description) > 3000) return { error: "Description must be 3,000 UTF-8 bytes or fewer.", field: "list-desc" };
      return { op, action, name, description, subscribe: el("subscribe-check").checked, unfollowFollowed };
    }
    const list = listOptions.get(el("list-select").value);
    if (!list) return { error: "Choose a moderation list.", field: "list-select" };
    const active = Boolean(list.viewer?.blocked || list.viewer?.muted);
    return {
      op,
      action,
      name: list.name,
      description: list.description ?? "",
      list,
      subscribe: active ? false : el("subscribe-check").checked,
      unfollowFollowed,
    };
  }

  // Resolve the supplied handle to a stable DID; a post target retains its rkey.
  async function resolveTarget(parsed) {
    const profile = await readWithRetry("app.bsky.actor.getProfile", { actor: parsed.handle });
    if (!validDid(profile.did) || typeof profile.handle !== "string") throw { kind: "badbody", nsid: "app.bsky.actor.getProfile" };
    const target = {
      kind: parsed.kind,
      handle: profile.handle,
      did: profile.did,
      rkey: parsed.rkey,
      atUri: null,
    };
    if (parsed.kind === "post") {
      target.atUri = "at://" + profile.did + "/app.bsky.feed.post/" + parsed.rkey;
    }
    return target;
  }

  // ---------------------------------------------------------------------------
  // Candidate harvesting, safety exclusions, and review
  // ---------------------------------------------------------------------------

  /*
   * Build the preview in two stages: harvest candidate accounts from the target,
   * then subtract follows and existing destination members. No writes occur here.
   */
  async function startFetch() {
    if (state.running) return;
    state.running = true;
    const button = el("fetch-btn");
    setBusy(button, true);
    showFieldError("target-error", "");
    const parsed = parseTarget(el("target-input").value);
    const destination = validateDestination();
    if (!parsed || destination.error) {
      const invalidId = destination.error ? destination.field : "target-input";
      showFieldError(
        "target-error",
        destination.error || "Enter a bsky.app profile URL, post URL, or a handle like name.bsky.social.",
        [invalidId],
        true,
      );
      state.running = false;
      setBusy(button, false);
      return;
    }
    state.abort = new AbortController();
    setScreen("fetching");
    el("fetch-count").textContent = "Resolving the target…";
    try {
      state.target = await resolveTarget(parsed);
      state.mode = {
        op: destination.op,
        action: destination.action,
        subscribe: destination.subscribe,
        unfollowFollowed: destination.unfollowFollowed,
      };
      state.listName = destination.name;
      state.listDescription = destination.description;
      if (destination.op === "append") {
        state.listUri = destination.list.uri;
        state.listActive = {
          blocked: Boolean(destination.list.viewer?.blocked),
          muted: Boolean(destination.list.viewer?.muted),
        };
      } else {
        state.listUri = null;
        state.listActive = null;
      }
      const actors = await harvestTarget();
      const deduped = new Map();
      for (const actor of actors) {
        if (!validDid(actor?.did)) continue;
        deduped.set(actor.did, {
          did: actor.did,
          handle: actor.handle || actor.did,
          displayName: actor.displayName ?? "",
          avatar: actor.avatar ?? "",
        });
      }
      if (deduped.size > HARVEST_HARD_CAP) throw { kind: "toolarge", count: deduped.size };
      const exclusions = await buildExclusions();
      const candidates = [...deduped.values()];
      const followed = candidates.filter(item => exclusions.follows.has(item.did)).length;
      state.excludedFollows = state.mode.unfollowFollowed ? 0 : followed;
      state.excludedExisting = candidates.filter(item => exclusions.existing.has(item.did)).length;
      state.harvested = candidates
        .filter(item => !exclusions.all.has(item.did))
        .map(item => ({ ...item, isFollowed: exclusions.follows.has(item.did) }));
      // Count only followed accounts that actually survived all other exclusions.
      state.followedIncluded = state.harvested.filter(item => item.isFollowed).length;
      renderPreview();
      setScreen("preview");
    } catch (err) {
      if (err?.kind === "network" && err.aborted && state.abort?.signal.aborted) {
        state.harvested = [];
        setScreen("target");
      } else if (err?.kind === "xrpc" && err.name === "ProfileNotFound") {
        setScreen("target");
        showFieldError("target-error", "Account not found or deleted.", ["target-input"], true);
      } else if (["pagination", "badbody"].includes(err?.kind) && isSafetyNsid(err.nsid)) {
        showError(err, "target", "Could not verify all accounts you follow. Nothing has been written.");
      } else if (err?.kind === "expired") {
        showBanner("Session expired — sign in again to resume.", "warning");
        state.session = null;
        setScreen("auth");
      } else {
        showError(err, "target");
      }
    } finally {
      state.abort = null;
      state.running = false;
      setBusy(button, false);
    }
  }

  function cancelFetch() {
    // Cancelling the phase also aborts its currently active request, if any.
    if (state.abort) state.abort.abort();
  }

  // A profile means followers; a post means the union of likes and reposts.
  async function harvestTarget() {
    const onCount = count => {
      el("fetch-count").textContent = "Gathered " + count.toLocaleString() + " accounts…";
    };
    if (state.target.kind === "profile") {
      return paginate(
        "app.bsky.graph.getFollowers",
        { actor: state.target.did },
        page => page.followers,
        { cap: HARVEST_HARD_CAP, onCount },
      );
    }
    const combined = [];
    const sources = [
      ["app.bsky.feed.getLikes", page => page.likes?.map(item => item.actor)],
      ["app.bsky.feed.getRepostedBy", page => page.repostedBy],
      ["app.bsky.feed.getQuotes", page => page.posts?.map(item => item.author)],
    ];
    for (const [nsid, extract] of sources) {
      const result = await paginate(
        nsid,
        { uri: state.target.atUri },
        extract,
        { cap: HARVEST_HARD_CAP, onCount: count => onCount(combined.length + count) },
      );
      combined.push(...result);
    }
    return combined;
  }

  // Only these graph record types are relevant to the safety exclusion scan.
  function isSafetyNsid(nsid) {
    return nsid === "com.atproto.repo.listRecords" || nsid === "com.atproto.repo.getRecord";
  }

  async function fetchFollowRecords() {
    // Keep each record key because unfollowing deletes the relationship record, not
    // the subject account. A Map also gives constant-time safety lookups.
    const records = await paginate(
      "com.atproto.repo.listRecords",
      { repo: state.session.did, collection: "app.bsky.graph.follow" },
      page => page.records,
    );
    const byDid = new Map();
    for (const record of records) {
      const did = record.value?.subject;
      const rkey = typeof record.uri === "string" ? rkeyFromAtUri(record.uri) : "";
      if (validDid(did) && rkey) byDid.set(did, rkey);
    }
    return byDid;
  }

  async function fetchFollowSet() {
    return new Set((await fetchFollowRecords()).keys());
  }

  async function fetchMembershipRecords() {
    // Read repository records directly, then retain only items for this exact list.
    if (!state.listUri) return [];
    const records = await paginate(
      "com.atproto.repo.listRecords",
      { repo: state.session.did, collection: "app.bsky.graph.listitem" },
      page => page.records,
    );
    return records.filter(record => record.value?.list === state.listUri);
  }

  // Safety policy: never add accounts the operator follows, or accounts already
  // present in the destination list.
  async function buildExclusions() {
    el("fetch-count").textContent = "Checking your follows and existing list members…";
    const follows = await fetchFollowSet();
    const membership = state.mode?.op === "append" ? await fetchMembershipRecords() : [];
    const existing = new Set(membership.map(record => record.value?.subject).filter(validDid));
    // Opt-in unfollow mode keeps followed accounts eligible. They still cannot be
    // included if already present, because there would be no new membership to pair.
    const all = new Set([state.session.did, ...existing]);
    if (!state.mode?.unfollowFollowed) for (const did of follows) all.add(did);
    if (el("exclude-target").checked && state.target?.did) all.add(state.target.did);
    return { all, follows, existing };
  }

  // Render in small animation-frame batches so large previews remain responsive.
  // Rows are constructed with DOM nodes and text properties, never parsed markup.
  function renderPreview() {
    previewRenderToken += 1;
    const token = previewRenderToken;
    const container = el("preview-list");
    container.setAttribute("aria-busy", "true");
    clearNode(container);
    el("execute-btn").disabled = true;
    el("execute-btn").textContent = "Preparing account list…";
    el("preview-summary").textContent = "Found " + state.harvested.length.toLocaleString() +
      " eligible accounts. Excluded " + state.excludedFollows.toLocaleString() +
      " accounts you follow and " + state.excludedExisting.toLocaleString() + " already on the list.";
    const unfollowWarning = el("unfollow-warning");
    unfollowWarning.hidden = state.followedIncluded === 0;
    unfollowWarning.textContent = state.followedIncluded
      ? state.followedIncluded.toLocaleString() + " followed account(s) are included. Selected ones will be unfollowed as they are added to the list."
      : "";
    const hours = Math.ceil(state.harvested.length / 1500);
    el("preview-estimate").textContent = state.harvested.length > HARVEST_SOFT_CAP
      ? "~" + state.harvested.length.toLocaleString() + " accounts. Estimated time: about " + hours +
        " hour(s) due to Bluesky's write limits. Progress is saved when the build pauses."
      : "Accounts whose follow record exists at the latest safety check will not be added.";
    const active = Boolean(state.listActive?.blocked || state.listActive?.muted);
    el("active-list-warning").hidden = !active;
    if (active) {
      el("active-list-warning").textContent = "⚠ This list is already active on your account (block/mute). New members take effect as they are added.";
    }
    let offset = 0;
    const appendChunk = () => {
      if (token !== previewRenderToken) return;
      const fragment = document.createDocumentFragment();
      const end = Math.min(offset + 200, state.harvested.length);
      for (; offset < end; offset += 1) fragment.append(createAccountRow(state.harvested[offset], offset));
      container.append(fragment);
      if (offset < state.harvested.length) requestAnimationFrame(appendChunk);
      else {
        container.setAttribute("aria-busy", "false");
        filterPreview();
        updateExecuteCount();
      }
    };
    requestAnimationFrame(appendChunk);
  }

  function createAccountRow(account, index) {
    // Each row keeps its DID as inert form data; visible profile fields remain text.
    const label = document.createElement("label");
    label.className = "account-item";
    label.setAttribute("role", "listitem");
    label.setAttribute("aria-posinset", String(index + 1));
    label.setAttribute("aria-setsize", String(state.harvested.length));
    label.dataset.search = (account.handle + " " + account.displayName).toLocaleLowerCase();
    const checkbox = document.createElement("input");
    checkbox.type = "checkbox";
    checkbox.checked = true;
    checkbox.dataset.did = account.did;
    checkbox.dataset.index = String(index);
    checkbox.addEventListener("change", updateExecuteCount);
    label.append(checkbox);

    // The content policy permits only Bluesky's image CDN, so reject every other URL.
    if (typeof account.avatar === "string" && account.avatar.startsWith("https://cdn.bsky.app/")) {
      const image = document.createElement("img");
      image.className = "account-avatar";
      image.src = account.avatar;
      image.alt = "";
      image.loading = "lazy";
      image.referrerPolicy = "no-referrer";
      image.width = 24;
      image.height = 24;
      image.addEventListener("error", () => { image.hidden = true; });
      label.append(image);
    } else {
      const placeholder = document.createElement("span");
      placeholder.className = "avatar-placeholder";
      placeholder.setAttribute("aria-hidden", "true");
      label.append(placeholder);
    }

    const copy = document.createElement("span");
    copy.className = "account-copy";
    copy.id = "account-label-" + index;
    checkbox.setAttribute("aria-labelledby", copy.id);
    const handle = document.createElement("bdi");
    handle.className = "account-handle";
    handle.textContent = "@" + account.handle;
    copy.append(handle);
    if (account.displayName) {
      const name = document.createElement("bdi");
      name.className = "account-name";
      name.textContent = account.displayName;
      copy.append(name);
    }
    if (account.isFollowed) {
      const note = document.createElement("span");
      note.className = "account-note";
      note.textContent = "Currently followed — will unfollow if selected";
      copy.append(note);
    }
    label.append(copy);
    return label;
  }

  function filterPreview() {
    // Filtering changes visibility only and deliberately preserves checkbox state.
    const query = el("filter-input").value.trim().toLocaleLowerCase();
    let shown = 0;
    const rows = el("preview-list").querySelectorAll(".account-item");
    for (const row of rows) {
      row.classList.toggle("is-filtered", Boolean(query) && !row.dataset.search.includes(query));
      if (!row.classList.contains("is-filtered")) shown += 1;
    }
    el("filter-status").textContent = query
      ? shown.toLocaleString() + " of " + rows.length.toLocaleString() + " accounts shown."
      : rows.length.toLocaleString() + " accounts shown.";
  }

  function setShownSelection(selected) {
    // Bulk selection applies only to rows visible under the current search filter.
    for (const row of el("preview-list").querySelectorAll(".account-item:not(.is-filtered)")) {
      row.querySelector("input[type=checkbox]").checked = selected;
    }
    updateExecuteCount();
  }

  function selectedDids() {
    // Revalidate every value when it crosses from the document into execution state.
    return [...el("preview-list").querySelectorAll("input[type=checkbox]:checked")]
      .map(input => input.dataset.did)
      .filter(validDid);
  }

  function updateExecuteCount() {
    // The count is both user feedback and the write button's enablement rule.
    const count = selectedDids().length;
    const followedSelected = [...el("preview-list").querySelectorAll("input[type=checkbox]:checked")]
      .map(input => state.harvested[Number(input.dataset.index)])
      .filter(account => account?.isFollowed).length;
    el("execute-btn").textContent = followedSelected
      ? "Unfollow " + followedSelected.toLocaleString() + " and add " + count.toLocaleString() + " accounts"
      : "Add " + count.toLocaleString() + " accounts to list";
    el("execute-btn").disabled = count === 0;
    el("selection-status").textContent = count.toLocaleString() + " accounts selected" +
      (followedSelected ? ", including " + followedSelected.toLocaleString() + " that will be unfollowed" : "") + ".";
  }

  // ---------------------------------------------------------------------------
  // Credential-free persistence and resume validation
  // ---------------------------------------------------------------------------

  /*
   * The saved payload is intentionally minimal and credential-free. It contains
   * enough information to reconcile and resume a run after a reload or tab crash.
   */
  function queuePayload() {
    return {
      v: 4,
      ownerDid: state.session.did,
      listUri: state.listUri,
      pendingListRkey: state.pendingListRkey,
      pendingListCreatedAt: state.pendingListCreatedAt,
      listName: state.listName,
      listDescription: state.listDescription ?? "",
      op: state.mode.op,
      action: state.mode.action,
      unfollowFollowed: Boolean(state.mode.unfollowFollowed),
      subscribePending: Boolean(state.subscribePending),
      queue: [...state.queue],
      selectedTotal: state.selectedTotal,
      written: state.written,
      unfollowed: state.unfollowed,
      skippedSafety: state.skippedSafety,
      conflicts: state.conflicts,
      savedAt: Date.now(),
    };
  }

  // Membership accounting must balance before and after every persisted mutation.
  function invariantHolds() {
    return state.written + state.skippedSafety + state.conflicts + state.queue.length === state.selectedTotal;
  }

  function assertInvariant() {
    // The console assertion aids development; the thrown error protects production.
    console.assert(invariantHolds(), "Run accounting invariant failed");
    if (!invariantHolds()) throw { kind: "corrupt", message: "Run accounting is inconsistent." };
  }

  // Persist atomically at the localStorage API level; storage failure stops writes.
  function persistRun() {
    if (!state.session || !state.mode) return false;
    assertInvariant();
    try {
      localStorage.setItem(lsQueueKey(state.session.did), JSON.stringify(queuePayload()));
      storageHealthy = true;
      return true;
    } catch {
      storageHealthy = false;
      showBanner("Progress can't be saved in this browser — don't close the tab.", "warning");
      return false;
    }
  }

  function deleteSavedRun() {
    // Deleting resume data does not affect any records already committed remotely.
    if (!state.session) return;
    try {
      localStorage.removeItem(lsQueueKey(state.session.did));
    } catch {
      storageHealthy = false;
    }
    el("resume-box").hidden = true;
  }

  // Treat saved data as untrusted input, including data written by older app builds.
  function validSavedRun(data) {
    if (!data || data.v !== 4 || data.ownerDid !== state.session.did) return false;
    if (!Array.isArray(data.queue) || data.queue.some(item => !validDid(item))) return false;
    if (new Set(data.queue).size !== data.queue.length) return false;
    const counters = [data.selectedTotal, data.written, data.skippedSafety, data.conflicts];
    if (counters.some(value => !Number.isInteger(value) || value < 0)) return false;
    if (data.unfollowed !== undefined && (!Number.isInteger(data.unfollowed) || data.unfollowed < 0 || data.unfollowed > data.written + data.skippedSafety)) return false;
    if (data.written + data.skippedSafety + data.conflicts + data.queue.length !== data.selectedTotal) return false;
    if (!["create", "append"].includes(data.op) || !["block", "mute"].includes(data.action)) return false;
    // Older v4 payloads did not have this field and safely restore with opt-in off.
    if (data.unfollowFollowed !== undefined && typeof data.unfollowFollowed !== "boolean") return false;
    if (typeof data.subscribePending !== "boolean" || typeof data.savedAt !== "number") return false;
    if (Date.now() - data.savedAt > QUEUE_TTL_MS || data.savedAt > Date.now() + 60000) return false;
    if (typeof data.listName !== "string" || utf8Length(data.listName) < 1 || utf8Length(data.listName) > 64) return false;
    if (typeof data.listDescription !== "string" || graphemeLength(data.listDescription) > 300 || utf8Length(data.listDescription) > 3000) return false;
    if (data.listUri !== null) {
      const prefix = "at://" + state.session.did + "/app.bsky.graph.list/";
      if (typeof data.listUri !== "string" || !data.listUri.startsWith(prefix) || !TID_RE.test(rkeyFromAtUri(data.listUri))) return false;
    }
    if (data.op === "append" && data.listUri === null) return false;
    if (data.op === "create" && data.listUri === null) {
      if (typeof data.pendingListRkey !== "string" || !TID_RE.test(data.pendingListRkey)) return false;
      if (typeof data.pendingListCreatedAt !== "string" || !Number.isFinite(Date.parse(data.pendingListCreatedAt))) return false;
    }
    return true;
  }

  function readSavedRun() {
    // Invalid, expired, or malformed payloads are removed instead of partly restored.
    if (!state.session) return null;
    try {
      const raw = localStorage.getItem(lsQueueKey(state.session.did));
      if (!raw) return null;
      const data = JSON.parse(raw);
      if (!validSavedRun(data)) {
        localStorage.removeItem(lsQueueKey(state.session.did));
        return null;
      }
      return data;
    } catch {
      try { localStorage.removeItem(lsQueueKey(state.session.did)); } catch { /* unavailable */ }
      return null;
    }
  }

  function relativeAge(savedAt) {
    // Coarse wording avoids presenting a saved timestamp as exact progress freshness.
    const seconds = Math.max(0, Math.floor((Date.now() - savedAt) / 1000));
    if (seconds < 60) return "moments ago";
    const minutes = Math.floor(seconds / 60);
    if (minutes < 60) return minutes + " minute(s) ago";
    const hours = Math.floor(minutes / 60);
    if (hours < 48) return hours + " hour(s) ago";
    return Math.floor(hours / 24) + " day(s) ago";
  }

  // Offer resume only for the currently signed-in DID and a non-expired queue.
  function checkSavedRun() {
    const data = readSavedRun();
    const box = el("resume-box");
    box.hidden = !data;
    if (!data) return;
    const copy = el("resume-copy");
    clearNode(copy);
    copy.append(document.createTextNode("Unfinished run: "));
    copy.append(bdi(data.listName));
    copy.append(document.createTextNode(" — " + data.queue.length.toLocaleString() +
      " accounts remaining (saved " + relativeAge(data.savedAt) + ")."));
  }

  // Restore the durable state only; runtime locks and timers are always reacquired.
  function restoreSavedRun(data) {
    state.listUri = data.listUri;
    state.pendingListRkey = data.pendingListRkey;
    state.pendingListCreatedAt = data.pendingListCreatedAt;
    state.listName = data.listName;
    state.listDescription = data.listDescription;
    state.mode = {
      op: data.op,
      action: data.action,
      subscribe: data.subscribePending,
      unfollowFollowed: Boolean(data.unfollowFollowed),
    };
    state.subscribePending = data.subscribePending;
    state.queue = [...data.queue];
    state.selectedTotal = data.selectedTotal;
    state.written = data.written;
    state.unfollowed = data.unfollowed ?? 0;
    state.skippedSafety = data.skippedSafety;
    state.conflicts = data.conflicts;
    assertInvariant();
  }

  function discardSavedRun() {
    // This is a local cleanup action; it never deletes the destination list.
    deleteSavedRun();
    showBanner("Saved run discarded.");
  }

  /*
   * Cross-tab lease
   * localStorage cannot provide a true compare-and-swap, so acquisition writes a
   * random owner ID, waits briefly, and verifies ownership. A heartbeat extends the
   * lease, while every write verifies it again immediately before touching Bluesky.
   */
  function makeRunId() {
    return [...crypto.getRandomValues(new Uint8Array(16))]
      .map(byte => byte.toString(16).padStart(2, "0")).join("");
  }

  function readLease() {
    // Parsing failures are treated as inability to guarantee exclusive ownership.
    try {
      const raw = localStorage.getItem(lsLockKey(state.session.did));
      if (!raw) return null;
      const lock = JSON.parse(raw);
      if (typeof lock.runId !== "string" || typeof lock.ts !== "number") return null;
      return lock;
    } catch {
      throw { kind: "storage", message: "This browser cannot create the safety lock required for writing." };
    }
  }

  function writeLease() {
    try {
      localStorage.setItem(lsLockKey(state.session.did), JSON.stringify({ runId: state.runId, ts: Date.now() }));
    } catch {
      throw { kind: "storage", message: "This browser cannot create the safety lock required for writing." };
    }
  }

  async function acquireLease() {
    if (permanentLeaseLoss) throw { kind: "toolost" };
    state.runId = makeRunId();
    const current = readLease();
    if (current && Date.now() - current.ts <= LOCK_TTL_MS) {
      throw { kind: "locked", message: "Another tab is already running this job." };
    }
    writeLease();
    // Give a racing tab time to publish its owner ID, then resolve the winner.
    await sleep(300);
    const confirmed = readLease();
    if (!confirmed || confirmed.runId !== state.runId) {
      throw { kind: "locked", message: "Another tab is already running this job." };
    }
    heartbeatTimer = setInterval(heartbeat, LOCK_BEAT_MS);
  }

  function heartbeat() {
    // Lease loss is permanent for this execution attempt; a later resume must start
    // with a new run ID and full reconciliation.
    if (!state.runId || !state.session) return;
    let lock;
    try {
      lock = readLease();
    } catch {
      permanentLeaseLoss = true;
      return;
    }
    if (!lock || lock.runId !== state.runId) {
      permanentLeaseLoss = true;
      return;
    }
    try { writeLease(); } catch { permanentLeaseLoss = true; }
  }

  // This check sits on the write path, not just at startup or on the heartbeat.
  function ensureLease() {
    if (permanentLeaseLoss) throw { kind: "toolost" };
    const lock = readLease();
    if (!lock || lock.runId !== state.runId) {
      permanentLeaseLoss = true;
      throw { kind: "toolost" };
    }
  }

  function releaseLease() {
    // Remove only a lease still owned by this tab, never a successor tab's lease.
    clearInterval(heartbeatTimer);
    heartbeatTimer = null;
    if (!state.session || !state.runId) return;
    try {
      const lock = readLease();
      if (lock?.runId === state.runId) localStorage.removeItem(lsLockKey(state.session.did));
    } catch { /* best effort */ }
    state.runId = null;
  }

  /*
   * Pausing occurs only between remote writes. Automatic pauses use the same state
   * machine for rate-limit windows, errors, and manual user requests.
   */
  function requestPause() {
    state.pauseRequested = true;
    el("pause-btn").disabled = true;
    el("status").textContent = "Pausing after the current batch…";
  }

  function pauseRun(reason, { until = 0, kind = "manual", automatic = false } = {}) {
    // Persist before releasing exclusivity so another tab sees the newest queue.
    persistRun();
    releaseLease();
    pauseUntil = until;
    pauseKind = kind;
    el("pause-reason").textContent = reason;
    el("pause-persistence").textContent = storageHealthy
      ? "Paused. Safe to close this tab."
      : "Progress can't be saved in this browser — don't close the tab.";
    el("resume-btn").hidden = automatic;
    setScreen("paused");
    startCountdown(until);
    if (automatic && until > Date.now()) {
      resumeTimer = setTimeout(() => resumeExecution(), Math.max(0, until - Date.now() + 50));
    }
  }

  function startCountdown(until) {
    // The countdown is presentation only; resume timing uses a separate timeout.
    clearInterval(countdownTimer);
    const node = el("countdown");
    if (!until) {
      node.textContent = "";
      return;
    }
    const paint = () => {
      const remaining = Math.max(0, until - Date.now());
      const seconds = Math.ceil(remaining / 1000);
      const minutes = Math.floor(seconds / 60);
      const rest = seconds % 60;
      node.textContent = remaining > 0 ? "Resuming in " + minutes + ":" + String(rest).padStart(2, "0") : "Resuming…";
      if (remaining <= 0) clearInterval(countdownTimer);
    };
    paint();
    countdownTimer = setInterval(paint, 1000);
  }

  /*
   * Reconciliation reads authoritative repository records immediately before
   * execution. This prevents stale preview data or an uncertain prior response from
   * causing duplicate membership records or bypassing a newly followed account.
   */
  async function safetyRevalidate() {
    const follows = await fetchFollowRecords();
    const members = new Set((await fetchMembershipRecords()).map(record => record.value?.subject));
    const before = state.queue.length;
    followRkeys.clear();
    if (state.mode.unfollowFollowed) {
      // Retain followed DIDs and remember the exact relationship records that must
      // be deleted atomically with their list memberships.
      for (const did of state.queue) {
        const rkey = follows.get(did);
        if (rkey) followRkeys.set(did, rkey);
      }
      state.queue = state.queue.filter(did => !members.has(did));
    } else {
      state.queue = state.queue.filter(did => !follows.has(did) && !members.has(did));
    }
    const removed = before - state.queue.length;
    state.skippedSafety += removed;
    assertInvariant();
    if (removed) {
      const reason = state.mode.unfollowFollowed
        ? "because they are already listed"
        : "because you now follow them or they are already listed";
      showBanner("Removed " + removed + " accounts " + reason + ".", "warning");
    }
    persistRun();
  }

  async function reconcileMembership() {
    // This catches batches committed by Bluesky whose response never reached the tab.
    const present = new Set((await fetchMembershipRecords()).map(record => record.value?.subject).filter(validDid));
    const committed = state.queue.filter(did => present.has(did));
    if (committed.length) {
      const committedSet = new Set(committed);
      state.queue = state.queue.filter(did => !committedSet.has(did));
      state.written += committed.length;
    }
    assertInvariant();
    persistRun();
  }

  // Append runs must prove the selected list still exists and remains a modlist.
  async function verifyListExists() {
    if (!state.listUri) return;
    try {
      await readWithRetry("com.atproto.repo.getRecord", {
        repo: state.session.did,
        collection: "app.bsky.graph.list",
        rkey: rkeyFromAtUri(state.listUri),
      });
    } catch (err) {
      if (isRecordNotFound(err)) {
        deleteSavedRun();
        throw { kind: "missinglist" };
      }
      throw err;
    }
  }

  // Convert RecordNotFound into null while preserving every other failure.
  async function getRecordMaybe(collection, rkey) {
    try {
      return await readWithRetry("com.atproto.repo.getRecord", {
        repo: state.session.did,
        collection,
        rkey,
      });
    } catch (err) {
      if (isRecordNotFound(err)) return null;
      throw err;
    }
  }

  function listRecordMatches(result) {
    // Exact matching prevents adopting an unrelated record that happens to share a key.
    const value = result?.value;
    return value?.$type === "app.bsky.graph.list" &&
      value.purpose === "app.bsky.graph.defs#modlist" &&
      value.name === state.listName &&
      (value.description ?? "") === (state.listDescription ?? "") &&
      value.createdAt === state.pendingListCreatedAt;
  }

  // A create-list response may have been lost. Probe the deterministic pending key
  // and accept it only when its record exactly matches the intended list metadata.
  async function resolvePendingList() {
    let found = await getRecordMaybe("app.bsky.graph.list", state.pendingListRkey);
    if (found) {
      if (!listRecordMatches(found)) throw { kind: "xrpc", name: "RecordKeyConflict", message: "The pending list key contains different data." };
      state.listUri = "at://" + state.session.did + "/app.bsky.graph.list/" + state.pendingListRkey;
      state.pointsUsed += POINTS_PER_CREATE;
      persistRun();
      return true;
    }
    await sleep(SETTLE_MS);
    found = await getRecordMaybe("app.bsky.graph.list", state.pendingListRkey);
    if (found) {
      if (!listRecordMatches(found)) throw { kind: "xrpc", name: "RecordKeyConflict", message: "The pending list key contains different data." };
      state.listUri = "at://" + state.session.did + "/app.bsky.graph.list/" + state.pendingListRkey;
      state.pointsUsed += POINTS_PER_CREATE;
      persistRun();
      return true;
    }
    return false;
  }

  // Reserve and persist the list rkey before writing, making creation crash-resumable.
  async function createListIfNeeded() {
    if (state.listUri) return;
    if (!state.pendingListRkey) {
      state.pendingListRkey = newListTid();
      state.pendingListCreatedAt = new Date().toISOString();
    }
    persistRun();
    for (let attempt = 0; attempt < 3; attempt += 1) {
      await ensureWriteBudget(POINTS_PER_CREATE);
      ensureLease();
      try {
        const result = await apiWithRefresh("POST", "com.atproto.repo.createRecord", {
          body: {
            repo: state.session.did,
            collection: "app.bsky.graph.list",
            rkey: state.pendingListRkey,
            record: {
              $type: "app.bsky.graph.list",
              purpose: "app.bsky.graph.defs#modlist",
              name: state.listName,
              description: state.listDescription ?? "",
              createdAt: state.pendingListCreatedAt,
            },
          },
        });
        const expectedUri = "at://" + state.session.did + "/app.bsky.graph.list/" + state.pendingListRkey;
        if (result.uri !== expectedUri) throw { kind: "badbody", nsid: "com.atproto.repo.createRecord" };
        state.listUri = result.uri;
        state.pointsUsed += POINTS_PER_CREATE;
        persistRun();
        await maybePauseForHeaders(result[RATE], POINTS_PER_CREATE);
        return;
      } catch (err) {
        if (err?.kind === "ratelimit") {
          pauseRun("Bluesky rate limit reached.", { until: err.resetAt, kind: "rate", automatic: true });
          throw { kind: "paused" };
        }
        if (["network", "server", "badbody"].includes(err?.kind) || (err?.kind === "xrpc" && /exist/i.test(err.message || ""))) {
          try {
            if (await resolvePendingList()) return;
          } catch (verifyErr) {
            if (["network", "server"].includes(verifyErr?.kind)) {
              pauseRun("Connection lost — press Resume to retry.");
              throw { kind: "paused" };
            }
            throw verifyErr;
          }
          continue;
        }
        throw err;
      }
    }
    pauseRun("Connection lost — press Resume to retry.");
    throw { kind: "paused" };
  }

  // Respect both the app's conservative hourly point budget and server rate headers.
  async function ensureWriteBudget(cost) {
    const now = Date.now();
    if (!state.pointsWindowStart) state.pointsWindowStart = now;
    if (now - state.pointsWindowStart >= 3600000) {
      state.pointsUsed = 0;
      state.pointsWindowStart = now;
      await safetyRevalidate();
    }
    if (state.pointsUsed + cost > POINTS_BUDGET) {
      const until = state.pointsWindowStart + 3600000;
      pauseRun("Waiting for the client-side Bluesky write budget to reset.", { until, kind: "budget", automatic: true });
      throw { kind: "paused" };
    }
  }

  async function maybePauseForHeaders(rate, nextCost) {
    // The server's remaining-point signal takes precedence over local pacing.
    if (!rate || rate.remaining === null || !rate.resetAt) return;
    if (rate.remaining < nextCost && rate.resetAt > Date.now()) {
      pauseRun("Waiting for Bluesky's write allowance to reset.", { until: rate.resetAt, kind: "rate", automatic: true });
      throw { kind: "paused" };
    }
  }

  // Precompute stable record keys before a batch so retries address the same records.
  async function makeChunk() {
    const dids = state.queue.slice(0, BATCH_SIZE);
    return Promise.all(dids.map(async did => ({
      did,
      rkey: await rkeyForItem(state.listUri, did),
      followRkey: followRkeys.get(did) ?? null,
    })));
  }

  // Bluesky currently charges one point for a delete and three for a create.
  function chunkWriteCost(chunk) {
    const deletes = chunk.filter(item => item.followRkey).length;
    return chunk.length * POINTS_PER_CREATE + deletes * POINTS_PER_DELETE;
  }

  // Commit local progress only after the batch is known to exist remotely.
  function confirmChunk(chunk, points = true) {
    const dids = new Set(chunk.map(item => item.did));
    state.queue = state.queue.filter(did => !dids.has(did));
    for (const did of dids) followRkeys.delete(did);
    state.written += chunk.length;
    state.unfollowed += chunk.filter(item => item.followRkey).length;
    if (points) state.pointsUsed += chunkWriteCost(chunk);
    assertInvariant();
    persistRun();
    updateProgress();
  }

  // Classify every record after an ambiguous write as present, missing, or conflicting.
  async function inspectChunk(chunk) {
    const expected = [];
    const absent = [];
    const conflicts = [];
    for (const item of chunk) {
      const record = await getRecordMaybe("app.bsky.graph.listitem", item.rkey);
      if (!record) {
        absent.push(item);
      } else if (record.value?.subject === item.did && record.value?.list === state.listUri) {
        // An atomic unfollow/add commit must leave both sides in their expected state.
        // If membership exists but the follow record remains, do not claim success.
        const follow = item.followRkey
          ? await getRecordMaybe("app.bsky.graph.follow", item.followRkey)
          : null;
        if (follow) conflicts.push(item);
        else expected.push(item);
      } else {
        conflicts.push(item);
      }
    }
    return { expected, absent, conflicts };
  }

  function applyMixedInspection(result) {
    // Expected records count as safely settled, not newly written in this attempt;
    // conflicting deterministic keys are terminal and surfaced separately.
    const expected = new Set(result.expected.map(item => item.did));
    const conflicts = new Set(result.conflicts.map(item => item.did));
    state.queue = state.queue.filter(did => !expected.has(did) && !conflicts.has(did));
    for (const did of [...expected, ...conflicts]) followRkeys.delete(did);
    state.skippedSafety += expected.size;
    state.unfollowed += result.expected.filter(item => item.followRkey).length;
    state.conflicts += conflicts.size;
    assertInvariant();
    persistRun();
    updateProgress();
  }

  // Mixed results are resolved item-by-item; a fully missing chunk is safe to retry.
  async function resolveAmbiguousChunk(chunk) {
    await sleep(SETTLE_MS);
    let result = await inspectChunk(chunk);
    if (result.expected.length === chunk.length) {
      confirmChunk(chunk, true);
      return "committed";
    }
    if (result.absent.length === chunk.length) {
      await sleep(SETTLE_MS);
      result = await inspectChunk(chunk);
      if (result.absent.length === chunk.length) return "retry";
      if (result.expected.length === chunk.length) {
        confirmChunk(chunk, true);
        return "committed";
      }
    }
    applyMixedInspection(result);
    return "handled";
  }

  /*
   * A batch write has three outcomes: confirmed success, definite rejection, or
   * ambiguity (for example, connection loss after server commit). Ambiguity always
   * triggers repository inspection before any retry.
   */
  async function writeChunk(chunk) {
    let ambiguousCycles = 0;
    while (true) {
      const writeCost = chunkWriteCost(chunk);
      await ensureWriteBudget(writeCost);
      ensureLease();
      try {
        const result = await apiWithRefresh("POST", "com.atproto.repo.applyWrites", {
          body: {
            repo: state.session.did,
            // Deletes and creates share one transaction: an account is never
            // unfollowed unless its list membership is created successfully.
            writes: chunk.flatMap(item => [
              ...(item.followRkey ? [{
                $type: "com.atproto.repo.applyWrites#delete",
                collection: "app.bsky.graph.follow",
                rkey: item.followRkey,
              }] : []),
              {
                $type: "com.atproto.repo.applyWrites#create",
                collection: "app.bsky.graph.listitem",
                rkey: item.rkey,
                value: {
                  $type: "app.bsky.graph.listitem",
                  subject: item.did,
                  list: state.listUri,
                  createdAt: new Date().toISOString(),
                },
              },
            ]),
          },
        });
        confirmChunk(chunk, true);
        const nextMaximumCost = Math.min(BATCH_SIZE, state.queue.length) *
          (POINTS_PER_CREATE + (state.mode.unfollowFollowed ? POINTS_PER_DELETE : 0));
        await maybePauseForHeaders(result[RATE], nextMaximumCost);
        return;
      } catch (err) {
        if (err?.kind === "paused") throw err;
        if (err?.kind === "ratelimit") {
          pauseRun("Bluesky rate limit reached.", { until: err.resetAt, kind: "rate", automatic: true });
          throw { kind: "paused" };
        }
        // A follow may disappear or be recreated after revalidation. Refresh its
        // repository key and retry the still-atomic transaction.
        const staleFollow = chunk.some(item => item.followRkey) && err?.kind === "xrpc" &&
          /not.?found/i.test((err.message || "") + " " + (err.name || ""));
        if (staleFollow) {
          const currentFollows = await fetchFollowRecords();
          for (const item of chunk) item.followRkey = currentFollows.get(item.did) ?? null;
          continue;
        }
        // A transport failure does not prove the server rejected the write. Likewise,
        // an "already exists" response can mean a previous attempt actually committed.
        const ambiguous = ["network", "server", "badbody"].includes(err?.kind);
        const possibleExisting = err?.kind === "xrpc" && /exist|duplicate/i.test((err.message || "") + " " + (err.name || ""));
        if (ambiguous || possibleExisting) {
          ambiguousCycles += 1;
          try {
            const resolution = await resolveAmbiguousChunk(chunk);
            if (resolution !== "retry") return;
          } catch (verifyErr) {
            if (["network", "server"].includes(verifyErr?.kind)) {
              pauseRun("Connection lost — press Resume to retry.");
              throw { kind: "paused" };
            }
            throw verifyErr;
          }
          if (ambiguousCycles >= 3) {
            pauseRun("Connection lost — press Resume to retry.");
            throw { kind: "paused" };
          }
          continue;
        }
        throw err;
      }
    }
  }

  // The execution loop is deliberately simple: prepare, budget, write, persist,
  // then pause only at a boundary where no request is in flight.
  async function executeLoop() {
    await createListIfNeeded();
    while (state.queue.length) {
      if (permanentLeaseLoss) throw { kind: "toolost" };
      if (state.pauseRequested) {
        state.pauseRequested = false;
        el("pause-btn").disabled = false;
        pauseRun("Paused at your request.");
        throw { kind: "paused" };
      }
      el("status").textContent = "Adding accounts… " + state.queue.length.toLocaleString() + " remaining.";
      const chunk = await makeChunk();
      await writeChunk(chunk);
      await sleep(INTER_BATCH_MS);
    }
    assertInvariant();
    // Queue completion makes resume data obsolete before optional activation begins.
    deleteSavedRun();
    if (state.subscribePending) await subscribeToList();
    showDone();
    releaseLease();
  }

  // Convert checked preview rows to a DID-only durable queue and begin a fresh run.
  async function startExecution() {
    if (state.running) return;
    const dids = [...new Set(selectedDids())];
    if (!dids.length) return;
    state.running = true;
    setBusy(el("execute-btn"), true);
    state.queue = dids;
    state.selectedTotal = dids.length;
    state.written = 0;
    state.unfollowed = 0;
    state.skippedSafety = 0;
    state.conflicts = 0;
    state.subscribePending = Boolean(state.mode.subscribe);
    state.pointsUsed = 0;
    state.pointsWindowStart = Date.now();
    // Reserve creation identity before persistence so a crash cannot create two lists.
    state.pendingListRkey = state.mode.op === "create" ? newListTid() : null;
    state.pendingListCreatedAt = state.mode.op === "create" ? new Date().toISOString() : null;
    permanentLeaseLoss = false;
    persistRun();
    try {
      await acquireLease();
      setScreen("executing");
      el("pause-btn").disabled = false;
      updateProgress(true);
      // Re-scan follows immediately before the first write; the review may have
      // remained open long enough for relationships to change.
      await safetyRevalidate();
      await executeLoop();
    } catch (err) {
      await handleRunError(err);
    } finally {
      state.running = false;
      setBusy(el("execute-btn"), false);
    }
  }

  // Reloaded runs first restore data, then use the normal resume/reconcile path.
  async function resumeSavedRun() {
    if (state.running) return;
    const data = readSavedRun();
    if (!data) {
      checkSavedRun();
      return;
    }
    restoreSavedRun(data);
    await resumeExecution();
  }

  // Every resume reacquires the lease and revalidates safety before another write.
  async function resumeExecution() {
    if (state.running) return;
    if (permanentLeaseLoss) {
      showError({ kind: "toolost" }, "target");
      return;
    }
    if (["budget", "rate"].includes(pauseKind) && Date.now() < pauseUntil) return;
    state.running = true;
    clearTimeout(resumeTimer);
    clearInterval(countdownTimer);
    try {
      await acquireLease();
      setScreen("executing");
      updateProgress(true);
      // Recovery order matters: identify/create the list, verify it, account for
      // previous commits, then reapply the follow-based safety policy.
      if (!state.listUri) {
        const exists = await resolvePendingList();
        if (!exists) await createListIfNeeded();
      }
      await verifyListExists();
      await reconcileMembership();
      await safetyRevalidate();
      await executeLoop();
    } catch (err) {
      await handleRunError(err);
    } finally {
      state.running = false;
    }
  }

  // Recoverable failures preserve the queue and move to an explicit paused state.
  async function handleRunError(err) {
    if (err?.kind === "paused") return;
    if (err?.kind === "ratelimit") {
      pauseRun("Bluesky rate limit reached.", { until: err.resetAt, kind: "rate", automatic: true });
      return;
    }
    if (err?.kind === "expired") {
      persistRun();
      releaseLease();
      showBanner("Session expired — sign in again to resume.", "warning");
      state.session = null;
      setScreen("auth");
      return;
    }
    if (err?.kind === "locked") {
      releaseLease();
      showBanner("Another tab is already running this job.", "warning");
      setScreen("target");
      checkSavedRun();
      return;
    }
    if (err?.kind === "toolost") {
      permanentLeaseLoss = true;
      persistRun();
      releaseLease();
      showError(err, "target", "Another tab took over this job.");
      return;
    }
    // Missing destinations and broken accounting cannot be resumed safely.
    if (["missinglist", "corrupt"].includes(err?.kind)) {
      deleteSavedRun();
      releaseLease();
      showError(err, "target");
      return;
    }
    if (["pagination", "badbody"].includes(err?.kind)) {
      persistRun();
      releaseLease();
      showError(err, "target", "Could not verify all accounts you follow. No further accounts have been written.");
      return;
    }
    // Transient failures retain local progress and require reconciliation on resume.
    if (["network", "server"].includes(err?.kind)) {
      pauseRun(err.kind === "server"
        ? "Bluesky server error (" + err.status + ") — press Resume to retry."
        : "Network problem — press Resume to retry.");
      return;
    }
    persistRun();
    releaseLease();
    showError(err, "target");
  }

  // Throttle paint work during large runs without withholding the final update.
  function updateProgress(force = false) {
    const now = performance.now();
    if (!force && now - lastProgressPaint < 200) return;
    lastProgressPaint = now;
    const completed = state.written + state.skippedSafety + state.conflicts;
    const percent = state.selectedTotal ? Math.round(completed / state.selectedTotal * 100) : 0;
    const progress = el("progress");
    progress.value = percent;
    progress.textContent = percent + "%";
    progress.setAttribute("aria-valuetext", percent + "% complete, " + state.queue.length.toLocaleString() + " accounts remaining");
  }

  /*
   * Activation happens only after all membership records are settled. Blocking is a
   * public listblock repository record; muting is a procedural preference endpoint.
   * Activation failure never rolls back successfully created memberships.
   */
  async function subscribeToList() {
    ensureLease();
    subscriptionFailed = false;
    try {
      // Muting has no repository record to construct; blocking does.
      if (state.mode.action === "mute") {
        await apiWithRefresh("POST", "app.bsky.graph.muteActorList", { body: { list: state.listUri } });
      } else {
        const rkey = await rkeyForListblock(state.listUri);
        await ensureWriteBudget(POINTS_PER_CREATE);
        ensureLease();
        try {
          await apiWithRefresh("POST", "com.atproto.repo.createRecord", {
            body: {
              repo: state.session.did,
              collection: "app.bsky.graph.listblock",
              rkey,
              record: {
                $type: "app.bsky.graph.listblock",
                subject: state.listUri,
                createdAt: new Date().toISOString(),
              },
            },
          });
          state.pointsUsed += POINTS_PER_CREATE;
        } catch (err) {
          // As with membership batches, inspect the stable key before declaring an
          // uncertain activation attempt failed.
          if (!["network", "server", "badbody"].includes(err?.kind) && !(err?.kind === "xrpc" && /exist|duplicate/i.test((err.message || "") + (err.name || "")))) throw err;
          await sleep(SETTLE_MS);
          let record = await getRecordMaybe("app.bsky.graph.listblock", rkey);
          if (!record) {
            await sleep(SETTLE_MS);
            record = await getRecordMaybe("app.bsky.graph.listblock", rkey);
          }
          if (record?.value?.$type !== "app.bsky.graph.listblock" || record?.value?.subject !== state.listUri) throw err;
          state.pointsUsed += POINTS_PER_CREATE;
        }
      }
      state.subscribePending = false;
    } catch (err) {
      if (err?.kind === "paused") throw err;
      if (err?.kind === "expired" || err?.kind === "toolost") throw err;
      if (err?.kind === "ratelimit") {
        pauseRun("Bluesky rate limit reached.", { until: err.resetAt, kind: "rate", automatic: true });
        throw { kind: "paused" };
      }
      subscriptionFailed = true;
    }
  }

  async function retrySubscription() {
    // Retry activation independently; completed memberships are never reprocessed.
    if (state.running || !state.listUri) return;
    state.running = true;
    setBusy(el("retry-subscribe-btn"), true);
    try {
      await acquireLease();
      state.subscribePending = true;
      await subscribeToList();
      showDone();
    } catch (err) {
      await handleRunError(err);
    } finally {
      releaseLease();
      state.running = false;
      setBusy(el("retry-subscribe-btn"), false);
    }
  }

  // Present independently useful totals: added, safety-skipped, and conflicts.
  function showDone() {
    const parts = ["Added " + state.written.toLocaleString() + " accounts."];
    if (state.unfollowed) parts.push("Unfollowed " + state.unfollowed.toLocaleString() + " as they were added.");
    if (state.skippedSafety) parts.push("Skipped " + state.skippedSafety.toLocaleString() + " because you follow them or they were already on the list.");
    if (state.conflicts) parts.push(state.conflicts.toLocaleString() + " account(s) could not be added (record key conflict).");
    el("done-counts").textContent = parts.join(" ");
    el("done-subscription").hidden = !subscriptionFailed;
    el("done-subscription").textContent = subscriptionFailed ? "List built, but activating it failed." : "";
    el("retry-subscribe-btn").hidden = !subscriptionFailed;
    const link = el("list-link");
    // Bluesky's public list route uses a plain DID segment, not a percent-encoded one.
    link.href = "https://bsky.app/profile/" + state.session.did + "/lists/" + rkeyFromAtUri(state.listUri);
    setScreen("done");
  }
})();
