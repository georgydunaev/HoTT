# [HOTT] Ticket 7437 — HoTT: Provide Default Standalone hoq-config for In-Tree hoqc Execution

**Repository:** `HoTT`  
**Global Ticket ID:** `#32`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:44:40Z`  

## Task Description
The `hoqc` compiler wrapper script exits with fatal errors when `hoq-config` does not exist. While autoconf normally produces `hoq-config` from `hoq-config.in`, developers working directly with standard Coq installations cannot run `hoqc` out of the box. Provide a fallback template or generator script that instantiates `hoq-config` with system Coq paths and proper library bindings.

## Resolution
Provided default `hoq-config` and `etc/configure_hoqc.sh` setup helper that discovers `coqc`, `coqtop`, and Coq libraries and generates a working `hoq-config`.
