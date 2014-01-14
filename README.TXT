# PlSheet: a SWI-Prolog library for analyzing ODF spreadsheets

PlSheet is a SWI-Prolog  library  for   analysing  ODF  spreadsheets. It
covers representing the spreadsheet as a Prolog fact base which includes
cell contents, cell types,  cell  formulas   and  cell  style (spanning,
colour, font, etc). On top of  that,   it  provides facilities to reason
about formula dependencies and discover  regions with similar properties
(e.g., a region of cells with labels).

The file test.pl contains sample toplevel  code   that  can be used as a
starting point to use the library.

## Home

PlSheet is hosted on GitHub at https://github.com/Data2Semantics/plsheet


## Documentation

The library is documented in the source using PlDoc. The simplest way to
view the documentation is by running the   command  below, which opens a
browser with interactive facilities for  exploring the documentation and
sources.

  ==
  % swipl --pldoc test.pl
  ==


## Processing MicroSoft Excel files

This library only processes ODF (Open Document Format) files. ODS is the
ODF sub-format for spreadsheets. Open Office  and Libre Office ship with
a tool called =unoconv= to do batch  conversion of MicroSoft excel files
using the following command:

  ==
  % unoconv -f ods *.xlsx
  ==

## Acknowledgements

This library was developed in the context  of COMMIT/, and in particular
the Data2Semantics project thereof.

[commit.png;height="80pt"](http://www.commit-nl.nl/)
[data2semantics.png;height="80pt",align="right"](http://www.data2semantics.org/)















