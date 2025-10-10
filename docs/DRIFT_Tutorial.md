
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

DRIFT is a plugin, so it is used from the Oxide interactive shell.

1. **Download and Install Datasets**  
   Example datasets: [DRIFT-Dataset](https://github.com/Program-Understanding/DRIFT-Dataset)

   - **Dataset I:** OpenWRT (multi-version evolution)
   - **Dataset II:** WAGO PLC (clean vs. backdoored Dropbear)

2. **Load DRIFT**

   ```text
   plugin drift
   ```

3. **Run DRIFT Commands**

### 3.1 `compare_collections`

Compares two firmware collections and classifies **files** and **functions** as matched, modified, or unmatched.

**Usage:**

```text
compare_collections &target &baseline
compare_collections &target &baseline --view=FILE_CLASSIFICATIONS
compare_collections &target &baseline --view=FUNCTION_CLASSIFICATION
compare_collections &target &baseline --filter=Structurally_Modified
compare_collections &target &baseline --filter=Control_Call_Modified
```

**Views:**
- `FILE_CLASSIFICATIONS` - summary of matched, modified, added, and removed files.
- `FUNCTION_CLASSIFICATION` - counts per function category.

**Filters:**  
DRIFT now includes feature-based filters to refine which functions are flagged as modified:
- `Structurally_Modified`: triggered by control-flow graph structure changes.
- `Control_Call_Modified`: triggered by both structural and call-level changes.

**Examples:**

```text
compare_collections &v2 &v1
compare_collections &v2 &v1 --filter=Structurally_Modified
```

**Output:** Structured dict containing file-level and function-level counts, plus filtered modifications when specified.

---

### 3.2 `compare_all_collections`

Runs `compare_collections` sequentially over all versions in a predefined series (e.g., OpenWRT releases), generating a **CSV** and **stacked bar charts**.

**Usage:**

```text
compare_all_collections --csv_path=output.csv --func_chart_path=func.png --file_chart_path=file.png
```

**Outputs:**
- `compare_all_collections.csv` - summary table with file/function diffs per version.
- `function_classification.png` - stacked bar chart of function classifications.
- `file_classification.png` - stacked bar chart of file classifications.

**Default series includes**:
```
22.03.0 -> 24.10.2
```

(Adjustable in the plugin code if needed.)

---

### 3.3 `compare_collections_series` *(legacy)*

Iterates through and compares every collection matching a product prefix.

```text
compare_collections_series --filter=<product_prefix>
```

---

## Classification and Filtering Details

DRIFT uses Oxide’s binary diffing and semantic analysis features to classify changes:

| Category                | Description                                                   |
|--------------------------|----------------------------------------------------------------|
| `matched`                | Identical functions/files across versions                      |
| `modified`               | Changed functions with similarity < 1.0                         |
| `unmatched_target`       | Added in the target firmware                                   |
| `unmatched_baseline`     | Removed from the baseline firmware                             |
| `Structurally_Modified`  | Modified functions with structural CFG or call changes         |
| `Control_Call_Modified`  | Modified functions with combined structural and call changes   |

Filtering uses feature thresholds on function-level diff metadata:
- Basic Block nodes/edges
- Function calls added/removed
- Control flow structure changes

---

## Example Workflow

```text
plugin drift
compare_collections &23.05.5 &23.05.4 --filter=Structurally_Modified
compare_all_collections --csv_path=out.csv --func_chart_path=funcs.png --file_chart_path=files.png
```

This:
1. Loads DRIFT
2. Compares two versions with structural filtering
3. Runs an entire version series comparison
4. Produces summary CSV and visualization charts.

---

## Output Files

- `compare_all_collections.csv` — tabular summary of diff results.
- `function_classification.png` — stacked bar chart of modified/matched/unmatched functions.
- `file_classification.png` — stacked bar chart of file-level changes.

---

## Notes

- Results are cached locally for speed; reruns are fast once a diff has been computed.
- To change the filtering rules, edit the `rules` dictionary in the plugin source.
- Ghidra analysis must be working for function-level diffing to succeed.
