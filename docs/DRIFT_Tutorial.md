
# DRIFT Tutorial

DRIFT is an Automated Firmware Analysis Tool that ...

## Getting Started with OXIDE

DRIFT was created as a plugin for oxide, so it depends on oxide's core functionality

1. **Download Oxide**  
```git clone https://github.com/Program-Understanding/oxide.git```

2. **Set up a new virtual Environment** ***(Recommended)***
    1. Navigate into oxide directory
    2. Create a new virtual environment  
    ```python3 -m venv .venv```
    3. Activate virtual enviroment  
    ```source .venv/bin/activate```

3. **Install Dependancies**  
    DRIFT relies on existing tools to perform it's analysis this includes various python packages and Ghidra  

    **Python Packages**  
    ```pip3 install Termcolor Networkx numpy graphviz pydot matplotlib scipy pytlsh pyahocorasick opencv-python prettytable```  

    **Ghidra**  
    1. Install Ghidra's [Latest Release](https://github.com/NationalSecurityAgency/ghidra/releases)

    2. Ensure you have Java JDK 11 or higher installed

    3. Ensure Ghidra works by starting the program with ghidrarun

4. **Run Oxide**
