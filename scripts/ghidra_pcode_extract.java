// Todo:: this is still a current wip, the offsets will be wrong, and the output is not in the same format as the other scripts.

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.PcodeBlockBasic;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.SequenceNumber;

import com.google.gson.Gson;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.Iterator;

import java.util.Map;




public class ghidra_pcode_extract extends GhidraScript {

    public void run() throws Exception {
        String[] scriptArgs = getScriptArgs();
        Map<String, Object> result = new HashMap<>();
        DecompInterface ifc = new DecompInterface();
        ifc.openProgram(currentProgram);

        Map<String, Object> highFunctionMap = new HashMap<>();
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

            Map<String, Object> functionDetails = new HashMap<>();
            Map<String, Object> blocksMap = new HashMap<>();
           
            for (PcodeBlockBasic pb : hf.getBasicBlocks()) {
                Iterator<PcodeOp> poi = pb.getIterator();
                // List<Map<String, Object>> opsList = new ArrayList<>();
                Map<String, Object> opsMap = new HashMap<>();

                while (poi.hasNext()) {
                    PcodeOpAST po = (PcodeOpAST) poi.next();
                    Map<String, Object> opDetails = new HashMap<>();
                    SequenceNumber seqNum = po.getSeqnum();
                    opDetails.put("seqnum", seqNum.toString());
                    opDetails.put("operation", po.toString());
                    opDetails.put("mnemonic", po.getMnemonic());
                    opsMap.put(seqNum.getTarget().toString(), opDetails);
                }

                Map<String, Object> blockDetails = new HashMap<>();
                blockDetails.put("ops", opsMap);
                blocksMap.put(pb.getStart().toString(), blockDetails);
            }
            functionDetails.put("blocks", blocksMap);
            functionDetails.put("name", f.getName());
            highFunctionMap.put(f.getEntryPoint().toString(), functionDetails);
        }
        result.put("functions", highFunctionMap);

        Gson gson = new Gson();

        try (Writer writer = new FileWriter(scriptArgs[0])) {

            // Convert the Java object `person` into a JSON data and write to a file
            gson.toJson(result, writer);

        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }
}