
# DRIFT Tutorial

DRIFT is a tool for automated firmware triaging that identifies matched, modified, and unmatched components across firmware versions.

## Getting Started with OXIDE

DRIFT was created as a plugin for oxide, so it depends on oxide's core functionality

### Install and Configure Oxide

1. **Download Oxide**

    ```text
    git clone https://github.com/Program-Understanding/oxide.git
    ```

2. **Set up a new virtual Environment** ***(Recommended)***
    1. Navigate into oxide directory
    2. Create a new virtual environment  
    ```python3 -m venv .venv```
    3. Activate virtual enviroment  
    ```source .venv/bin/activate```

3. **Install Dependancies**  
    DRIFT relies on existing tools to perform it's analysis, including various python packages and [Ghidra](https://github.com/NationalSecurityAgency/ghidra)  

    **Python Packages**  

    ```shell
    pip install flare-capa
    ```  

    ```shell
    pip3 install Termcolor Networkx numpy graphviz pydot matplotlib scipy pyahocorasick opencv-python prettytable tabulate pandas
    ```  

    *pytlsh is required, but sometimes fails to install properly, for easier debugging install it seperately*

    ```shell
    pip3 install pytlsh
    ```

    **Ghidra**  
    1. Install Ghidra's [Latest Release](https://github.com/NationalSecurityAgency/ghidra/releases)

    2. Ensure you have Java JDK 11 or higher installed

    3. Ensure Ghidra works by navigating to ghidra's directory and starting the program with ```./ghidraRun```

4. **Initialize Oxide**  
    After all dependancies are installed:  

    navigate to the oxide directory with your virtual
    enviroment active and launch oxide with ```./oxide.sh```  

    The first time you launch oxide, you are given the opportunity to select where to store oxide's configuration file and cache.

    By default, the config file is stored in your user's home directory ```~/.config/oxide/.config.txt```

5. **Add Ghidra to Oxide .config.txt**
    1. Open ```~/.config/oxide/.config.txt``` with your favorite text editor  

    2. navigate to the line "ghidra_path" and add the path to the ***directory*** containing ghidraRun

        *It should look something like this:*
        ```/home/user/ghidra_11.3.1_PUBLIC_20250219/ghidra_11.3.1_PUBLIC```

        Try to avoid having any spaces in your filepath

### Using Oxide

1. **Add files to Oxide's datastore**  
    By default, oxide's datastore is in the following directory:  
    ```/home/(current_user)/.local/share/oxide```

    1. Add your desired set of files to the "datasets" directory.

    2. With oxide running, import your dataset with:  
    ```import path/to/dataset```  

        This imports a "collection" in oxide. Collections can be listed with the command ```show collections```

        You can list the file contents of a collection with  
        ```show &(collection) --verbose```

    3. Test ghidra disasm with a file oid:
    ```run ghidra_disasm %(oid)```

    If these commands don't throw any errors, you have successfully installed and configured oxide with ghidra.

## Running DRIFT

DRIFT is a plugin in oxide, so it is run from within the oxide interactive shell.

1. **Download and Install [Dataset(s)](https://github.com/Program-Understanding/Firmware-Dataset)**  
    Dataset I: OpenWRT  
    Dataset II: Commercial Firmware  
    Dataset III: Backdoored vs. Normal OpenWRT

2. **Load DRIFT Into Oxide**  
    Use the command ```plugin drift``` to load the drift plugin into oxide

3. **Run DRIFT**  
Drift has three possible commands:

    1. **import_product:**  
    imports every firmware image for a given product into oxide as collections.  

        Each Firmware version is imported as it's own collection.

        Usage:  
        ```import_product /path/to/product```

    2. **compare_collections:**  
    Compares two specified collections  

        Usage:  

        ```text
        compare_collections &target &baseline
        compare_collections &target &baseline --view=modified
        compare_collections &target &baseline file --view=modified
        compare_collections &target &baseline file --function=function_name
        ```

        *Remember, you can see all of the collections in Oxide with*  
        ```show collections```

    3. **compare_collections_series:**  
    Iterates through and compares every collection that shares the specified product name

        Usage:  
    ```compare_collections_series --filter=<product_prefix>```
