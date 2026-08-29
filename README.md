# Bluesky Moderation List Builder

A dependency-free, single-page utility for creating or extending Bluesky moderation lists from:

- the followers of a profile; or
- the likers, reposters, and quoters of a post.

Before writing, it reads your repository directly and excludes accounts already on the destination list. By default it also excludes accounts you follow. An explicit opt-in can instead include followed accounts, unfollowing each selected account atomically as its list membership is created. The app can activate the completed list as a block list or a private mute list.

## Run locally

Serve this directory over HTTP. Opening `index.html` directly is not supported because browser security rules differ for local files.

```sh
python3 -m http.server 8000
```

Then open `http://localhost:8000`.

There is no package installation, build command, backend, analytics service, or third-party script.

## Authentication and deployment scope

This version supports only accounts hosted by `https://bsky.social` and signs in with a Bluesky app password. Create a dedicated app password without direct-message access, use it only for this utility, and delete it when finished. Never enter your main account password.

The app is designed primarily for local and personal use. Static hosting, including GitHub Pages, is technically possible, but a public multi-user deployment should be replaced by an OAuth-based version. Current AT Protocol guidance recommends OAuth for end-user applications; password authentication is more appropriate for bot- and CLI-style tools.

App passwords grant more authority than this app needs, including posting, following, and repository writes. JavaScript can drop references to credentials after use, but it cannot guarantee memory zeroization. Use a throwaway account for development and end-to-end testing.

## Privacy

- Session tokens and passwords remain in memory only. They are never intentionally written to storage, cookies, URLs, or logs.
- A moderation list, its membership records, and a list-block subscription are public repository records.
- Muting a list is private to the account.
- An unfinished queue is saved unencrypted in this browser for up to 14 days so a paused run can resume.
- No analytics or unrelated network requests are made. Requests go only to Bluesky's service and avatar CDN.

## Safety and recovery design

- Safety-relevant reads use authoritative repository records, not lagging AppView projections.
- Every graph-record key satisfies the collection's required TID syntax. List-item TIDs are deterministic over both the destination list URI and subject DID, allowing the same account on different lists without duplicate records.
- Batches use atomic `applyWrites` transactions. Ambiguous outcomes are inspected by deterministic record key before anything is retried.
- The queue is persisted before the first write and after every confirmed batch.
- Follows and membership are rechecked on resume and at least hourly during long runs.
- Optional unfollowing uses the same atomic `applyWrites` transaction as membership creation, so a failed list-item create does not leave the account unfollowed.
- A per-account, per-origin lease prevents two tabs from writing the same queue concurrently.
- List activation happens only after all list members are reconciled.

The client uses a self-imposed 4,500-point hourly write budget below bsky.social's documented operational ceiling. Those values are service operations guidance, not protocol guarantees, and may change. Server responses remain the final rate-limit authority.

## Accessibility

The workflow uses native form controls and landmarks, labeled regions, a keyboard skip link, visible focus indicators, programmatic validation errors, screen-reader status announcements, and focus management when screens change. Candidate accounts are exposed as a labeled list with individually named checkboxes. Reduced-motion and Windows High Contrast preferences are respected.

## Development checks

Append `#test` to the local URL to run parser and deterministic-key assertions in the browser console. These self-tests make no network requests by themselves.

Security checks:

```sh
grep -RniE "https?://" index.html style.css
grep -RniE "innerHTML|outerHTML|insertAdjacentHTML|document\.write|eval\(|new Function" app.js
```

The first command should report exactly two lines in `index.html` and none in `style.css`. The second should produce no output.

Before real use, complete the acceptance checklist in `bluesky-modlist-builder-spec-v6.md` with a throwaway Bluesky account, including network interruption, tab takeover, token expiry, block, and mute scenarios.

## License

This project is released into the public domain under [The Unlicense](LICENSE). You may use, copy, modify, publish, sell, or redistribute it for any purpose. It is provided without warranty.
