Oxide is a flexible, modular, distributed framework for performing analysis of
executable code. It separates the user interface components from the storage
components and from the analysis components. The system is designed such that a
module writer who is a domain expert in the specific area of the module does not
need much knowledge of the rest of the system. The same modules work no matter
how or where the data is stored or what sort of interface the user is seeing.

# Decoders

## How to get Capstone to work

Capstone is an open-source, multi-platform, multi-architecture decoder.

Installation is accomplished through pip

```
pip install capstone
```

## How to get XED to work

XED is intel's reference x86 instruction decoder.

XED has python bindings mantained here:
    * https://github.com/huku-/pyxed

```
python3 setup.py build
python3 setup.py install

python3
>>> import pyxed
```

# Disassemblers

## How to get Ghidra to work
Ghidra is an open-source software RE tool designed to disassemble many different architectures and extensible through tweaking or creating sleigh files that define ABI of architecture.

https://github.com/NationalSecurityAgency/ghidra/releases

Ghidra runs in Java and requires Java JDK 11, *https://jdk.java.net/*


## How to get IDA to work

IDAPro is one of the most prevalent disassemblers, with the Hex-Rays decompilers on the
market. Once purchased the IDAPATH must be set in the configuration file.

## How to get Radare2
Radare is a command line software reverse engineering tool, with capstone backend.

Installation is accomplished through running install script from within the radare directory. Furthermore, a python interface is required.
* https://github.com/radareorg/radare2

```
./sys/install.sh
pip3 install r2pipe
```

## How to get Pharos to work

Pharos is a front end for the ROSE Compiler, from Lawrence Livermore National Labratory,
which configures the callbacks to get information out. Pharos is a suite of utilities 
built on this such as disassembly and OOAnalyzer.

Assuming docker is configured and installed. The easiest interface is the pre-built docker image.

```
docker pull seipharos/pharos
```

....


## How to get angr to work

angr is a symbolic execution and program analysis open source project from UCSB under Vigna and Kruegel.

```
pip3 install angr
```

## How to get Capa to work

Capa is an open source tool used to analyze executable files and provide a list of capabilities.

```
pip install flare-capa
```

## How to get Binary Ninja to work

Binary Ninja is an interactive disassembler, decompiler, and reverse engineering platform created by Vector35 (former Raytheon/SI Gov).

This requires a commercial license or headless license of binary ninja.

```
python3 <binary ninja home>/scripts/install_api.py
```


# Miscellaneous Packages in Modules/Plugins

pip3 install
* Termcolor
* Networkx
* numpy
* graphviz
* pydot
* matplotlib
* scipy
* py-tlsh
* pyahocorasick
* opencv-python
* prettytable

If you are using **MacOS**, you will need to install GNU objdump.
With Brew, `brew install binutils` and symlink `gobjdump` to `/usr/local/bin/gobjdump`

If you are using **linux** and want to print a call graph, you may need to install 'python3-tk'
.....


# Remote Shell

Launch a server like:

`Python3 utils/server.py -l 127.0.0.1:1492`

Then, in another shell connect with:

`Python3 rshell.py -r 127.0.0.1:1492`
