# Oxide Plugin Tutorial

Oxide is initialized with the default plugin already loaded. It provides functions to manipulate OIDs and collections

```text
 oxide > show plugins
  ---------- Plugins -------------------
  - 'default':
      -  file_io
      -  clean
      -  expand
      -  random_sample
      -  random_shuffle
      -  top_n
      -  count
      -  select
      -  export_file
      -  cat
      -  size_filter
      -  name_filter
      -  byte_filter
      -  type_filter
      -  key_filter
      -  extension_filter
      -  membership
      -  summarize
      -  intersection
  --------------------------------------
```

## Query Plugin Information

You can query information about the entire plugin or individual functions

```text
 oxide > help default



 Plugin: Utility functions for manipulating files and collections


    file_io :
        store or retrieve contents of a Python data structure
        Syntax:
            file_io <file_name> | show     # Retrieve from a file
            @<var> | file_io <file_name>   # Write to a file

    clean :
        Passes a list where empty dict keys are removed
        Syntax: <some_command> | clean | ...

        .
        .
        .

    summarize :
        Gives a summary of a set of files, including types, extensions, etc.  If no argument
                is passed, gives a summary for the entire datastore (may be very slow).
        Syntax: summarize %<oid>

    intersection :
        Returns the intersection of the collections passed in, non-collection IDs will be ignored
        Syntax: intersection &col1 &col2 ...

 oxide > help summarize

        Gives a summary of a set of files, including types, extensions, etc.  If no argument
                is passed, gives a summary for the entire datastore (may be very slow).
        Syntax: summarize %<oid>
```

## Default Plugin Functions

Oxide's default plugin contains a few helpful functions. Some examples are shown here.

### Summarize

'summarize' shows some of the properties of the OIDs in a collection

```text
 oxide > summarize &sample

Total files in set:  27

Extensions (files with multiple names counted more than once):
   None         :      7
   exe          :      6
   g0           :      5
   upx          :      3
   zip          :      2
   bz2          :      1
   gz           :      1
   v1           :      1
   so           :      1

Types:
   ELF          :      11
   PE           :      10
   ZIP          :      2
   MACHO        :      2
   BZ2          :      1
   GZIP         :      1

Sizes:
   Under 1k   : 0
   1k - 10k   : 0
   10k - 100k : 15
   100k - 1MB : 11
   1MB - 10MB : 1
   over 10 MB : 0
```

### Expand

'expand' allows you to pass a collection's OIDs one at a time to other functions

```text
 oxide > expand &sample | show
  ---------- Metadata c4bc4cceda6346956765779316c141003b35d130
  - Names: thunderbird.exe
  - Size: 399512 bytes

  - 'tags':
    - 'import_time': Thu Aug 22 16:55:51 2013
  --------------------------------------
  ---------- Metadata edec6dff47be52973da2ffe55949b33a656f3595
  - Names: bundle4.tar.bz2
  - Size: 519459 bytes

  - 'tags':
    - 'import_time': Thu Aug 22 16:55:51 2013
  --------------------------------------
  ---------- Metadata be339e5bc98caab0d6bc7d3fd97caceef2eda7d1
  - Names: ipd.pe32.v1
  - Size: 133632 bytes

  - 'tags':
    - 'import_time': Thu Aug 22 16:55:51 2013
  --------------------------------------

      .
      .
      .
```

### Cat

'cat' allows you to show the contents of a file

#### Import Dataset

```text
 oxide > import datasets/diff | collection create diffs
Processed 3/3 (100.00%)   time: 0.00m   est: 0.00m   261.74 per/s
  - 3 file(s) imported, 3 are new
  - Collection diffs created
 oxide > show &diffs --verbose
  ---------- Collection 3867075a431ec943be8df2ffae0ee3bdc849ef4c
  - 'name': diffs
  - 'notes':
  - 'num_oids': 3
  - 'oids':
    -  38dc4be7b8d2c66d8be4c5171d1923a512d285f5 : proof_text_1.txt
    -  d358b57ae3bfba8369e60fd62e51c39cbbeb6bb3 : proof_text_3.txt
    -  ed5a67d14dff962ecc704e3a4abe8d0161fba414 : proof_text_2.txt

  - 'tags':
    - 'creation_time': Thu Aug 22 17:00:28 2013
  --------------------------------------
```

#### Run cat command

```text
 oxide > cat ^proof_text_1.txt
This is a simple text document. It has no purpose
other than its simple existence.
    .
    .
    .

 oxide > cat ^proof_text_2.txt
This is a simple text document. It has no purpose
other than its simple existence.
    .
    .
    .


 oxide > cat ^proof_text_3.txt
  ShellSyntaxError: File contains non-printable characters.  Use --force to override.
 oxide > cat ^proof_text_3.txt --force
This is a simple text document. It has no purpose
other than its simple existence.

    .
```
