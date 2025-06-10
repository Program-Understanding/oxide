import java.io.File;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.AddressSetView;
import com.google.security.binexport.BinExportExporter;

public class ExportBinDiffScript extends GhidraScript {
    @Override
    protected void run() throws Exception {
        String[] args = getScriptArgs();
        if (currentProgram == null) {
            println("No program loaded.");
            return;
        }

        if (args == null || args.length < 1) {
            println("Usage: ExportBinDiffScript.java <output-file>");
            return;
        }

        File exportFile = new File(args[0]);
        AddressSetView addressSet = currentProgram.getMemory();

        BinExportExporter exporter = new BinExportExporter();
        boolean success = exporter.export(exportFile, currentProgram, addressSet, monitor);

        if (success) {
            println("Export complete: " + exportFile.getAbsolutePath());
        } else {
            println("Export failed.");
        }
    }
}
