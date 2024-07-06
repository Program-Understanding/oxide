import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.correlate.Hash;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.PcodeBlock;
import ghidra.program.model.pcode.PcodeBlockBasic;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.app.decompiler.*;
import generic.json.Json;
import java.lang.*;
import java.util.*;


public class ghidra_pcode_extract extends GhidraScript {

    public void run() throws Exception {
        HashMap<String, Object> result = new HashMap<String, Object>();
        DecompInterface ifc = new DecompInterface();
        ifc.openProgram(currentProgram);
        
        HashMap<String, Object> highFunctionMap = new HashMap<String, Object>();
        FunctionIterator fi = currentProgram.getListing().getFunctions(true);
        for (Function f : fi) {
            print(f.getName() + "\n");
            if (f.isExternal()) {
                continue;
            }
            DecompileResults res = ifc.decompileFunction(f, 0, null);
            HighFunction hf = res.getHighFunction();
            if (hf == null) {
                continue;

            }

            HashMap<String, Object> pcodeBlockMap = new HashMap<String, Object>();
            for (PcodeBlockBasic pb : hf.getBasicBlocks()) {

                Iterator<PcodeOp> poi = pb.getIterator();
                HashMap<String, String> pcodeOpMap = new HashMap<String, String>();
                while (poi.hasNext()) {
                    
                    PcodeOpAST po = (PcodeOpAST) poi.next();
                    pcodeOpMap.put(po.getSeqnum().toString(), po.toString());
                }
                pcodeBlockMap.put(pb.getStart().toString(), pcodeOpMap);
            }
            highFunctionMap.put(f.getName(), pcodeBlockMap);
        }
        result.put("test", highFunctionMap);
        print("Script Finished");
    }
    
}
