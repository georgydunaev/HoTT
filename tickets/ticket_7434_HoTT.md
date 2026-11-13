# [HOTT] Ticket 7434 — HoTT: Fix Notation Associativity Conflict at Precedence Level 40 in Basics Notations

**Repository:** `HoTT`  
**Global Ticket ID:** `#29`  
**Status:** `RESOLVED`  
**Created:** `2026-11-13T21:44:28Z`  

## Task Description
In `theories/Basics/Notations.v`, line 13 declared `Reserved Infix "o*" (at level 40).` without specifying associativity, which defaults to right associativity in Coq. Line 14 declared `Reserved Infix "oL" (at level 40, left associativity).`. In modern Coq (8.10+), declaring different associativities at the same precedence level produces a fatal syntax error: `Error: Level 40 is already declared to have right associativity while it is now expected to have left associativity.`.

## Resolution
Fixed by explicitly declaring `Reserved Infix "o*" (at level 40, left associativity).`, harmonizing precedence and associativity across all level 40 composition notations (`o*`, `oL`, `oR`, and `g o f`).
