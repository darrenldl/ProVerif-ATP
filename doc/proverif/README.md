# ProVerif 2.00 modifications

## Notes

- As ProVerif modification itself was not the core part of the project - we only modified ProVerif to resolve issues as we went on, we did not conduct any systematic review of the entirety of ProVerif's source code. Thus we make no claims that these modifications are completely safe.

- However, we have taken care to ensure these modifications do not impact the original functionality of ProVerif, that is, if you invoke the modified ProVerif in a non-exporting mode, it should behave the same as the original version. Again, however, we cannot claim with full certainty this is the case - if you absolutely need the exact behaviour provided by the original version of ProVerif, we recommend you to use the original version directly.

## List

- [Added missing equation export](equation_export.md)

- [Disabled equation checking when output is TPTP or SPASS](equation_check.md)

- Added TPTP export module

- Automatic abstract syntax tree modification in export mode

- Added `-log-pv` and `-log-pv-only` flags
