# Historical scaffold replay

The historical scaffold and its former dependencies belong to commit
dccff0d8fe723ec1478d1f63bbbdf648ba240bfa of
[the formal repository](https://github.com/itpplasma/symplectic-stafford-formal/tree/dccff0d8fe723ec1478d1f63bbbdf648ba240bfa).
Use that frozen checkout and its recorded Lean, Lake and dependency pins for a
historical replay. The [frozen build environment](legacy-build-environment.md)
records those exact pins and verification commands. The current release verifies the Mathlib-only Paper
development; its verifier does not offer a legacy replay mode.

The two dated endpoint lists beside this note preserve the previous endpoint
contracts as historical records. Their presence does not make them active
release obligations. The unused Lean scaffold sources remain in the current
repository for reference and are still checked by the source policy audit.
Their imports of retired dependencies are parsed during Palomar's source
header audit, without elaborating those unused files.
