#!/usr/bin/env python3

import sys

fns = sys.argv[1:]

ERR_COP = 0
ERR_IMP = 1
ERR_MOD = 2

exceptions = []

with open("scripts/copy-mod-doc-exceptions-short.txt") as f:
    lines = f.readlines()
    for line in lines:
        (fn, c, errno) = line.split()
        if errno == "ERR_COP":
            exceptions += [(ERR_COP, fn)]
        if errno == "ERR_IMP":
            exceptions += [(ERR_IMP, fn)]
        if errno == "ERR_MOD":
            exceptions += [(ERR_MOD, fn)]

new_exceptions = False

def import_only_check(lines, fn):
    import_only_file = True
    errors = []
    line_nr = 0
    for line_nr, line in enumerate(lines, 1):
        if line == "\n":
            continue
        imports = line.split()
        if imports[0] != "import":
            import_only_file = False
            break
        if len(imports) > 2:
            if imports[2] == "--":
                continue
            else:
                errors += [(ERR_IMP, line_nr, fn)]
    return (import_only_file, errors)

def regular_check(lines, fn):
    errors = []
    copy_started = False
    copy_done = False
    copy_start_line_nr = 0
    copy_lines = ""
    for line_nr, line in enumerate(lines, 1):
        if not copy_started and line == "\n":
            continue
        if not copy_started and line == "/-\n":
            copy_started = True
            copy_start_line_nr = line_nr
            continue
        if not copy_started:
            errors += [(ERR_COP, line_nr, fn)]
        if copy_started and not copy_done:
            copy_lines += line
            if line == "-/\n":
                if ((not "Copyright (c)" in copy_lines) or
                    (not "Apache" in copy_lines) or
                    (not "Author" in copy_lines)):
                    errors += [(ERR_COP, copy_start_line_nr, fn)]
                copy_done = True
            continue
        if copy_done and line == "\n":
            continue
        words = line.split()
        if words[0] != "import" and words[0] != "/-!":
            errors += [(ERR_MOD, line_nr, fn)]
            break
        if words[0] == "/-!":
            break
        # final case: words[0] == "import"
        if len(words) > 2:
            if words[2] != "--":
                errors += [(ERR_IMP, line_nr, fn)]
    return errors

def format_errors(errors):
    global new_exceptions
    for (errno, line_nr, fn) in errors:
        if (errno, fn) in exceptions:
            continue
        new_exceptions = True
        # filename first, then line so that we can call "sort" on the output
        if errno == ERR_COP:
            print("{} : line {} : ERR_COP : Malformed or missing copyright header".format(fn, line_nr))
        if errno == ERR_IMP:
            print("{} : line {} : ERR_IMP : More than one file imported per line".format(fn, line_nr))
        if errno == ERR_MOD:
            print("{} : line {} : ERR_MOD : Module docstring missing, or too late".format(fn, line_nr))

def lint(fn):
    with open(fn) as f:
        lines = f.readlines()
        (b, errs) = import_only_check(lines, fn)
        if b:
            format_errors(errs)
            return
        errs = regular_check(lines, fn)
        format_errors(errs)

for fn in fns:
    lint(fn)

# if "exceptions" is empty,
# we're trying to generate copy-mod-doc-exceptions.txt,
# so new exceptions are expected
if new_exceptions and len(exceptions) > 0:
    exit(1)
