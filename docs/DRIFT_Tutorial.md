
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
    DRIFT relies on existing tools to perform it's analysis, including various python packages and [Ghidra](https://github.com/NationalSecurityAgency/ghidra)  

    **Python Packages**  
    ```pip3 install Termcolor Networkx numpy graphviz pydot matplotlib scipy pytlsh pyahocorasick opencv-python prettytable```  

    **Ghidra**  
    1. Install Ghidra's [Latest Release](https://github.com/NationalSecurityAgency/ghidra/releases)

    2. Ensure you have Java JDK 11 or higher installed

    3. Ensure Ghidra works by navigating to ghidra's directory and starting the program with ```./ghidraRun```

4. **Test Oxide**  
    After all dependancies are installed:  

    navigate to the oxide directory with your virtual
    enviroment active and launch oxide with ```./oxide.sh```  

    The first time you launch oxide, you are given the opportunity to select where to store oxide's configuration file and cache.

    By default, the config file is stored in your user's home directory ```~/.config/oxide/.config.txt```

5. **Add Ghidra to Oxide .config.txt**
    1. Open ```~/.config/oxide/.config.txt``` with your favorite text editor  

    2. navigate to the line "ghidra_path" and add the path to the ***directory*** containing ghidraRun

6. **Add files to Oxide's datastore**
