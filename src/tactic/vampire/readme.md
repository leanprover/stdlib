- The `vampire` tactic requires the Vampire theorem prover on your system. It has been tested with version 4.2.2 of Vampire without Z3, which you can obtain at: https://vprover.github.io/download.html

- Since there are no officially available Vampire binaries for Windows or Mac, you will have to compile Vampire from source on those systems. Keep in mind that there may be unknown issues, as the tactic has only been tested on Linux.

- The tactic also requires installation of SWI-Prolog (https://www.swi-prolog.org/Download.html) for executing the PrologScript `vampire.pl`.

- The executable file `vampire` and the PrologScript `vampire.pl` must both be available on your path. The easiest way to do this is to add `tactic/vampire` to your path and place `vampire` in it.

- When invoked, `vampire` translates the proof goal to TPTP CNF format and writes it to temporary file, which is subsequently read by Vampire. In most cases the default location for this file should work, but if necessary you can change it by modifying `temp_goal_file_path` in `main.lean`.
