# rts
General definition for safe Regression Test Selection (RTS) algorithms, instantiated with an algorithm over JVM using the JinjaDCI JVM semantics

This repository gives a general definition for safe RTS algorithms and CollectionSemantics (the combination of a semantics with a collection function), including instantiations with class-collection-based RTS algorithms running over JVM.

This repository relies on that found at https://github.com/susannahej/jinja-dci, whose contents are expected to be in a folder named JinjaDCI (instead of jinja-dci) placed in the same folder as one containing this repository. Files in this repository are compatible with at least Isabelle2019  and Isabelle2020 (the current version as of this update).

To run this development, a setup accessing the related (non-Jinja) AFP entries is required. See https://www.isa-afp.org/using.html for directions on how to install the AFP.

Current AFP dependencies:
(only those required by JinjaDCI)

Questions related to installing this repository can be directed to sjohnsn2 (at) illinois (dot) edu.
