# Terminal UX and explicit catalog selection

Development qualification, 10 September 2026. This does not publish RC3 or qualify
new proof-tool pins. The integration implementation is `e8988e4fab4541e95185ba8c9644ecb0e4c063e6`.

| Check | Result |
| --- | --- |
| Integration toolkit tests | 116 passed |
| Repository script tests | 87 passed |
| Focused core / proof / evidence / pages / evaluation tests | 66 / 90 / 80 / 85 / 94 passed |
| Wheel built from source distribution and installed outside checkout | Passed |
| Live fork catalog and descriptor | 5,264 declarations validated; source `947d543c20efc871fd1b28f76c29e72ebca432c8` |
| Erdős 92 browsing | Human output and JSON passed; variants, statements and source provenance retained |
| Terminal and redirected behavior | Width wrapping, literal source text, color controls, quiet/verbose, explicit pager and interruption tested |
| Catalog source boundaries | Separate caches, no implicit source substitution, invalid digest fails closed, configuration preserved on failure |

The CLI keeps argparse and adds Rich only for terminal presentation. Worker
operations can still emit plain progress without importing terminal dependencies.
Machine payload fields, exit codes and mathematical outcomes are unchanged.

`setup catalog --url HTTPS_URL` validates a sibling manifest before atomically
saving the endpoint. Workspace configuration takes precedence over user
configuration. `--catalog-url` overrides it for one command; an explicit local
`--catalog FILE` is a separate choice. Related-work feeds follow the selected site.
No upstream or user-global endpoint was changed during this qualification.

Long operations retain logs and show stages with elapsed time. Completing a stage
means the operation returned, not that mathematical verification passed. Typed
results remain authoritative. No model calls or expensive proof reruns were made
for these presentation changes. Full release acceptance remains tracked in #4394.

Final UI revision `a7e905365d9a57cf3d146c2ee3c6602ee4dae995` adds an explicit-color
regression for minimal terminals. All 117 integration toolkit tests passed.
[macOS and Linux package qualification](https://github.com/williamjblair/formal-conjectures/actions/runs/34497935615)
and [integration checks](https://github.com/williamjblair/formal-conjectures/actions/runs/34497934260)
passed on that exact revision. The release job was skipped: this is a development
branch qualification, not publication of RC3 assets.
