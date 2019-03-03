# ProVerif 2.00 modifications

## Notes

- As ProVerif modification itself was not the core part of the project - we only modified ProVerif to resolve issues as we went on, we did not conduct any systematic review of the entirety of ProVerif's source code. Thus we make no claims that these modifications are completely safe.

- However, we have taken care to ensure these modifications do not impact the original functionality of ProVerif, that is, if you invoke the modified ProVerif in a non-exporting mode, it should behave the same as the original version. Again, however, we cannot claim with full certainty this is the case - if you absolutely need the exact behaviour provided by the original version of ProVerif, we recommend you to use the original version directly.

- We also note that the modifications right now assume the encoding uses only `bitstring` type, but the modifications should be extendable to accomodate other combinations of types.

## List

- [Added missing equation export](equation_export.md)

- [Disabled equation checking when output is TPTP or SPASS](equation_check.md)

- [Added TPTP export module](tptp_export.md)

  - Also added inequality declaration between constants/free variables in the module, documented in the same file

- Automatic abstract syntax tree modifications in export mode

  - [Output tagging](output_tag.md)

  - [Let binding flattening](let_binding_flatten.md)

  - [Replace let binding with equality checks with predicate](let_eq_to_pred.md)

  - [Introduction of extra constants](add_extra_consts.md)

  - [Replace if with equality checks with predicate](if_eq_to_pred.md) (implemented, but later dropped)

- [Added a pretty printer for typed pi-calculus abstract syntax tree](pitprettyprint.md)
