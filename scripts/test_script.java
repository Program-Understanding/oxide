import ghidra.app.script.GhidraScript;

public class test_script extends GhidraScript {

    public void run() throws Exception {
        System.out.println(getScriptArgs().toString());
    }
}
