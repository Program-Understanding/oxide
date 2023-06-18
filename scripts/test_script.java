import ghidra.app.script.GhidraScript;

import java.lang.*;
import java.util.*;

public class test_script extends GhidraScript {

    public void run() throws Exception {
        System.out.println(Arrays.toString(getScriptArgs()));
    }
}
