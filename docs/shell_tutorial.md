# Oxide Shell Overview

Install Oxide using the instructions in the README or /docs/DRIFT_Tutorial.md

## Open the Oxide shell and display the help

```text
$ ./oxide.sh
 --------   Oxide   --------
 oxide > help
  ---------- Oxide Shell Help ----------
  - Commands: bash, collection, configure, context,  
    example, exit, help, history, import, load, plugin, py,  
    run, show, tag

  - System modifiers that resolve to an oid:
        %<oid>
        &<collection>
        $<context>
        @<var>
        ^<file_name>


  - help <command> for command specific help

  - See example for further information
```

## Import the sample dataset and create a collection

```text
 oxide > import datasets/sample_dataset/ | collection create sample
Processed 26/26 (100.00%)   time: 0.02m   est: 0.00m   19.82 per/s
  - 26 file(s) imported, 26 are new
  - Collection sample created

# Display the help for the show command
 oxide > help show

    Description: Print info about an item
    Syntax:
        show &<collection> [--verbose]
        show $<context>
        show @<var>
        show %<oid>

        show modules [<module>] [--verbose]
        show collections [--verbose]
        show context
        show stats
        show orphans
        show vars
        show plugins
        show aliases
```

## Display the collections

```text
 oxide > show collections
  ---------- Collections ---------------
  - 'sample': 26
  --------------------------------------
```

Collections are persistent and are referenced with an &.

## Display the sample collection and all of its details

```text
 oxide > show &sample --verbose
  ---------- Collection 8155723f531c3ecc69d9591e472b6748609d346f
  - 'name': sample
  - 'notes':
  - 'num_oids': 26
  - 'oids':
        -  02ba7205702dbcd5c2dd50de69637b1bd6cdca80 : ipd.pe32.g0
        -  138b238aa35f66948e4b85070b8b4158618c9509 : firefox.exe
        -  20fea1314dbed552d5fedee096e2050369172ee1 : 7z-0.9.20.exe, 7z.exe
        -  4e3fc623510bf3a81e726c5a4fdb0b0df9bb7c59 : nmap.exe
        -  7193164643b1666d0fc315d21bff4a4712d1c59c : ipd.mac32.g0
        -  86a956a68e3e0ddcbfaef3c863eaa991c964c3f6 : ipd.elf64.g0
        -  8ad5832097faf9f32ec48f8ae6ce799fed668cb5 : bundle1.zip
        -  8defdf11b5ab10623c8e48c04ca79628ecde3abf : libc-2.15.so
        -  98cb27c309643e983bffc0da86199bc3b7d0fc65 : netcat
        -  a9561a12a683ec46dbff10592cc26978e619c825 : bundle3.zip
        -  ab95261b2740f15f902fa420724897152c59827a : ash
        -  add2b6bb98a432dfdce6af34067938ac40aecb01 : ipd.elf32.g0
        -  ae33ee60c7b11a31a0b7070f11fe1649454bf930 : ipd.mac64.g0
        -  af68710ffdb5654f1b46c5f2b920de920d4fbf07 : pidgin.exe
        -  b11a526d3d37be5c38e31a56ab762b9471957cca : putty.exe
        -  b8721a7d7c1e2168614fc6d5fdf09b5f477cef95 : cat
        -  be339e5bc98caab0d6bc7d3fd97caceef2eda7d1 : ipd.pe32.v1
        -  c4bc4cceda6346956765779316c141003b35d130 : thunderbird.exe
        -  d04b5122af70ec221bf43b8a94952dde94c79235 : toolbox
        -  e3371281eb9017b85fbbca553ba687ff04ed00f2 : bash
        -  ef71fa8a646851941714dc5d8993f59bcf5934bf : rm
        -  f2a3c58f62423335543fe8ffb0058b1c77d77d12 : pidgin.upx
        -  f80d016fad31324b8c31c1985f401cf4e42cedbf : 7z.upx
        -  f8ab9279a18886065ce444f869563b4af276116b : cp
        -  f8bfcc27b6604afa2fc266c292edd938c9924929 : netcat.upx
        -  ff8321e26633f09d8510005f2b3e4b3b755cdb1c : bundle2.tar.gz

  - 'tags':
        - 'creation_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
```

## Display the details of a single file  

Files are referenced by name using a ^

```text
 oxide > show ^7z.exe
  ---------- Metadata 20fea1314dbed552d5fedee096e2050369172ee1
  - Names: 7z.exe
  - Size: 163840 bytes

  - 'tags':
        - 'import_time': Wed Aug 21 12:48:34 2013
  --------------------------------------
```

## Context

The context is not persistent and is useful for referencing a small set of files or a single file

```text
 oxide > help context

    Description: Manipulate the context which is like a working set
    Syntax:
        context set %<oid> # Set context to this (e.g. clear, then add)

        context add %<oid> # Append to the current context

        context remove %<oid> # Remove this from context

        context clear # Empty out the context

        context save [<fname>] # Save a context to a file

        context load [<fname>] # Load a context from a file
```

### Set the context to the collection sample and display the context

```text
 oxide > context set &sample
  - Context cleared and set to 27 items

 oxide > show context
  ---------- Context -------------------
  0:thunderbird.exe ( PE  399512 bytes )
  1:ipd.pe32.v1 ( PE  133632 bytes )
  2:pidgin.upx ( PE  38378 bytes )
  3:bundle3.zip ( ZIP  97268 bytes )
  4:firefox.exe ( PE  924632 bytes )
  5:netcat ( ELF  48052 bytes )
  6:ipd.pe32.g0 ( PE  483933 bytes )
  7:ipd.elf32.g0 ( ELF  15010 bytes )
  8:pidgin.exe ( PE  48618 bytes )
  9:ash ( ELF  82972 bytes )
  10:cat ( ELF  71641 bytes )
  11:ipd.mac64.g0 ( MACHO  21200 bytes )
  12:bundle2.tar.gz ( GZIP  100387 bytes )
  13:libc-2.15.so ( ELF  1730024 bytes )
  14:toolbox ( ELF  103248 bytes )
  15:cp ( ELF  124863 bytes )
  16:ipd.elf64.g0 ( ELF  21070 bytes )
  17:nmap.exe ( PE  748032 bytes )
  18:7z-0.9.20.exe,7z.exe ( PE  163840 bytes )
  19:7z.upx ( PE  77824 bytes )
  20:bundle1.zip ( ZIP  67854 bytes )
  21:netcat.upx ( ELF  20432 bytes )
  22:rm ( ELF  82264 bytes )
  23:bash ( ELF  725136 bytes )
  24:putty.exe ( PE  483328 bytes )
  25:ipd.mac32.g0 ( MACHO  18908 bytes )
  --------------------------------------
```

### Save the context

So it can be loaded if we exit and restart the shell

```text
 oxide > context save
  - Context saved to file .context.save
oxide > exit
```

```text
$ ./oxide.sh
 --------   Oxide   --------
 oxide > context load
  - Context loaded from file .context.save
```

### Display context items

Context items are referenced with $

```text
 oxide > show $0
  ---------- Metadata c4bc4cceda6346956765779316c141003b35d130
  - Names: thunderbird.exe
  - Size: 399512 bytes

  - 'tags':
        - 'import_time': Wed Aug 21 12:48:36 2013
  --------------------------------------
```

Slicing is supported when referencing context items
Multiple items can be referenced on the same line

```text
 oxide > show $:3 $8 $25:
  ---------- Metadata c4bc4cceda6346956765779316c141003b35d130
  - Names: thunderbird.exe
  - Size: 399512 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
  ---------- Metadata be339e5bc98caab0d6bc7d3fd97caceef2eda7d1
  - Names: ipd.pe32.v1
  - Size: 133632 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
  ---------- Metadata f2a3c58f62423335543fe8ffb0058b1c77d77d12
  - Names: pidgin.upx
  - Size: 38378 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
  ---------- Metadata af68710ffdb5654f1b46c5f2b920de920d4fbf07
  - Names: pidgin.exe
  - Size: 48618 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
  ---------- Metadata 7193164643b1666d0fc315d21bff4a4712d1c59c
  - Names: ipd.mac32.g0
  - Size: 18908 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
```

## Piping and variable assignment

Variables are referenced with @

```text
 oxide > $:3 | @x

 oxide > show vars
  ---------- Variables -----------------
  - 'x':
        -  be339e5bc98caab0d6bc7d3fd97caceef2eda7d1
        -  c4bc4cceda6346956765779316c141003b35d130
        -  f2a3c58f62423335543fe8ffb0058b1c77d77d12

  ---------- Plugin Variables ----------
  <EMPTY>

 oxide > show @x
 ---------- Metadata c4bc4cceda6346956765779316c141003b35d130
  - Names: thunderbird.exe
  - Size: 399512 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
  ---------- Metadata be339e5bc98caab0d6bc7d3fd97caceef2eda7d1
  - Names: ipd.pe32.v1
  - Size: 133632 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
  ---------- Metadata f2a3c58f62423335543fe8ffb0058b1c77d77d12
  - Names: pidgin.upx
  - Size: 38378 bytes

  - 'tags':
        - 'import_time': Thu Aug 28 09:42:05 2014
  --------------------------------------
```

## Invoking Python Shell

A Python shell can be invoked from the Oxide shell
Variables from each are present in the other

```text
 oxide > py
Python 2.7.2 (v2.7.2:8527427914a2, Jun 11 2011, 15:22:34)
[GCC 4.2.1 (Apple Inc. build 5666) (dot 3)] on darwin
Type "help", "copyright", "credits" or "license" for more information.
(Python Interactive Shell which shares state with Oxide)

>>> x
['be339e5bc98caab0d6bc7d3fd97caceef2eda7d1', 'c4bc4cceda6346956765779316c141003b35d130', 'edec6dff47be52973da2ffe55949b33a656f3595']
>>> y = 123
>>> exit()

 oxide > show @y
  ---------- Info ----------------------
 123
  --------------------------------------
```

## Bash Commands

Bash shell commands can be executed from the Oxide shell

```text
 oxide > bash ls
core        db      ida_plugins modules     plugins     shell.py        utils
datasets    docs        localstore  oxide.sh    scratch     test        web_interface
```

## Plugins

Only the default plugin is initially loaded

```text
 oxide > show plugins
  ---------- Plugins -------------------
  - 'default':
        -  membership
        -  summarize
        -  intersection
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
  --------------------------------------

 oxide > help plugin

    Description: Load a plugin file
    Syntax: plugin <plugin_file>
    Note: the file needs the .py extention but .py is dropped when executing the command
```

The default plugin is loaded at startup and contains many useful functions.

## Type Filter

Use the type_filter function to determine how many pe files are in the sample collection

```text
 oxide > help type_filter

        Plugin: Use without args to find all files with that type, use with args to filter
        Syntax: type_filter %<oid> --type=[ PE | ELF | PDF | etc...]

 oxide > type_filter &sample --type=PE | count
 - Received:  10  args.
```

Create a new collection with the pe files that are in the sample collection

```text
 oxide > type_filter &sample --type=PE | collection create sample_pes
  - Collection sample_pes created

 oxide > show collections
  ---------- Collections ---------------
  - 'sample': 26
  - 'sample_pes': 10
  --------------------------------------

 oxide > show &sample_pes --verbose
  ---------- Collection 32d79ff725f6536eb33a4aaf05773bbfd4e883d1
  - 'name': sample_pes
  - 'notes':
  - 'num_oids': 10
  - 'oids':
        -  02ba7205702dbcd5c2dd50de69637b1bd6cdca80 : ipd.pe32.g0
        -  138b238aa35f66948e4b85070b8b4158618c9509 : firefox.exe
        -  20fea1314dbed552d5fedee096e2050369172ee1 : 7z.exe
        -  4e3fc623510bf3a81e726c5a4fdb0b0df9bb7c59 : nmap.exe
        -  af68710ffdb5654f1b46c5f2b920de920d4fbf07 : pidgin.exe
        -  b11a526d3d37be5c38e31a56ab762b9471957cca : putty.exe
        -  be339e5bc98caab0d6bc7d3fd97caceef2eda7d1 : ipd.pe32.v1
        -  c4bc4cceda6346956765779316c141003b35d130 : thunderbird.exe
        -  f2a3c58f62423335543fe8ffb0058b1c77d77d12 : pidgin.upx
        -  f80d016fad31324b8c31c1985f401cf4e42cedbf : 7z.upx

  - 'tags':
        - 'creation_time': Wed Aug 21 13:09:04 2013
  --------------------------------------
```

## Summarize function

The summarize function gives more information about the types of files found in a collection.

```text
 oxide > summarize &sample

Total files in set:  26

Extensions (files with multiple names counted more than once):
   exe      :      7
   None     :      6
   g0       :      5
   upx      :      3
   zip      :      2
   gz       :      1
   v1       :      1
   so       :      1

Types:
   ELF          :          11
   PE           :          10
   MACHO        :          2
   ZIP          :          2
   GZIP         :          1

Sizes:
   Under 1k   : 0
   1k - 10k   : 0
   10k - 100k : 15
   100k - 1MB : 10
   1MB - 10MB : 1
   over 10 MB : 0
```

## Running Modules

Modules are typically run indirectly by using plugins, but they can be accessed directly as well using the run command.  

Example:

Run and display the byte_histogram module over the the collection sample_pes

```text
 oxide > run byte_histogram &sample_pes | show
  - Running byte_histogram over 1 items
Processed 10/10 (100.00%)   time: 0.01m   est: 0.00m   14.10 per/s

  ---------- Info ----------------------
  - '\x00': 812765
  - '\x01': 36410
  - '\x02': 20330
  - '\x03': 23889
  - '\x04': 26948
  - '\x05': 11721
  - '\x06': 11042
...

  - '\xfd': 11229
  - '\xfe': 15303
  - '\xff': 319449
  --------------------------------------
```

## Save Results

### Save Results to a variable

Run the same command but save the results to a variable

```text
 oxide > run byte_histogram &sample_pes | @bytes
  - Running byte_histogram over 1 items
Processed 10/10 (100.00%)   time: 0.00m   est: 0.00m   3358.94 per/s
```

### Save Results to a file

The file_io command can be used to save the contents of a variable out to a file  

This uses the built-in python pickle library to save python objects and load them.

```text
 oxide > help file_io

        Plugin: store or retrieve contents of a file
        Syntax:
            file_io <file_name> | show     # Retrieve from a file
            @<var> | file_io <file_name>   # Write to a file
```

### Write a variable to a file

```text
 oxide > @bytes | file_io my_bytes
```

### Read from files

```text
Read the variable back in from the file.
 oxide > file_io my_bytes | @more_bytes
```

## Load Plugins

### Load a plugin using the plugin command

Tab-complete should show a list of possible
plugins after the plugin command is typed.  
Let's look at bin_tools.

```text
 oxide > plugin bin_tools

 oxide > show plugins
  ---------- Plugins -------------------
  - 'bin_tools':
        -  diff
        -  match_arch
        -  simple_diff
        -  run_compare_gui
        -  strings
        -  common_bytes
        -  find_segments
        -  val_search
        -  hex_dec
        -  dec_hex
        -  hex_view
  - 'default':
        -  membership
        -  summarize
        -  intersection
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
  --------------------------------------
```

## Strings

Strings will show all of the strings in a file with the associated offsets.

```text
 oxide > strings $25
Strings in  ipd.mac32.g0
8__PAGEZERO0:
    00000058: H__TEXT
    0000008C: __text__TEXT
    000000B0: `
               __cstring
    000000E0: __TEXT,+
    000000F4: >,__StaticInit
. . .
    00004857: __ZNSolsEi__ZNSt8ios_base4InitC1Ev
    0000487B: __ZNSt8ios_base4InitD1Ev__ZSt3cin
    0000489E: __ZSt4cout__ZSt4endlIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_
    000048E5: __ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc__ZStlsIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_St5_Setw
    0000495F: __ZTVN10__cxxabiv117__class_type_infoE__ZTVN10__cxxabiv120__si_class_type_infoE
    000049B0: ___cxa_atexit___gxx_personality_v0
    000049D4: _exit
```

This concludes the shell tutorial.  Please look at the other tutorials in this directory and the developer guide for more details.
