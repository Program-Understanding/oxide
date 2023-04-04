/*
Copyright 2023 National Technology & Engineering Solutions
of Sandia, LLC (NTESS). Under the terms of Contract DE-NA0003525 with NTESS,
the U.S. Government retains certain rights in this software.

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE. 
*/

import java.util.Iterator;

import ghidra.app.script.GhidraScript;
import ghidra.program.model.mem.*;
import ghidra.program.model.lang.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.util.*;
import ghidra.program.model.reloc.*;
import ghidra.program.model.data.*;
import ghidra.program.model.block.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.scalar.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.address.*;

import ghidra.app.decompiler.*;

public class ghidra_extract extends GhidraScript {

    Address baseAddress;
    public String fixAddress(Address a) {
        return "" + a.subtract(baseAddress);
    }

    public void run() throws Exception {
        SimpleBlockModel sbm = new SimpleBlockModel(currentProgram);

        // Set up decompiler interface for our program
        DecompInterface ifc = new DecompInterface();
        ifc.openProgram(currentProgram);

        baseAddress = currentProgram.getImageBase();
        String format = currentProgram.getExecutableFormat();
        println("\nFile format: " + format + "\nImage base: " + currentProgram.getImageBase());

        // Process Instructions and dump with RESULTI
        InstructionIterator ii = currentProgram.getListing().getInstructions(true);
        print ( "\nRESULTM: [\"" + currentProgram.getImageBase() + "\"]\n\n");
        while (ii.hasNext() ) {
            Instruction in = ii.next();
            String output = "[";
            output += "\"" + in.getAddress() + "\", \"";
            String mnemonic = in.getMnemonicString();
            for (int i = 0; i < in.getNumOperands(); i++) {
                if (i == 0) {
                    mnemonic += "  ";
                } else {
                    mnemonic += ",";
                }

                mnemonic += in.getDefaultOperandRepresentation(i);
            }
            output += mnemonic + "\", ";

            // Add basic block parent to instruction
            output += "\"" + fixAddress(sbm.getFirstCodeBlockContaining(in.getAddress(), monitor).getFirstStartAddress()) + "\"]";
            print ( "\nRESULTI: " + output + "\n\n");
        }

        CodeBlockIterator cbi = sbm.getCodeBlocks(monitor);
        boolean first = true;
        // Process Basic Block and dump with RESULTB
        while (cbi.hasNext() ) {
            CodeBlock in = cbi.next();
            String output = "[";

            output += "\"" + in.getFirstStartAddress() + "\"" + ", [";
            first = true;  // Used to track comma printing
            CodeBlockReferenceIterator cbDests = in.getDestinations(monitor);
            Address recent = this.toAddr(0);
            while (cbDests.hasNext()) {
                CodeBlockReference cbr = cbDests.next();

                // Hack: singleton BBs seem to emit two duplicate destinations; squash one
                if (cbr.getDestinationAddress() != recent) {
                    if (!first) {
                        output += ", ";
                    }
                    first = false;

                    output += "\"" + cbr.getDestinationAddress() + "\"";
                }
                recent = cbr.getDestinationAddress();
            }

            output += "], [";

            first = true;
            Address cba = in.getFirstStartAddress();
            while (in.contains(cba)) {
                if (!first) {
                    output += ", ";
                }
                first = false;
                output += "\"" + cba + "\"";
                cba = currentProgram.getListing().getCodeUnitAfter(cba).getAddress();
            }

            output += "]]\n";

            print ( "\nRESULTB: " + output + "\n");
        }

        // loop through program functions
        Function function = getFirstFunction();

        while (function != null) {
            // Fill out parameter information
            String Parms = "[";

            // var.getOrdinal, may want to ensure in order
            first = true;
            for (Parameter var : function.getParameters()) {
                if (first == false) { Parms += ", "; }
                first = false;
                Parms += "\"" + var.getFormalDataType() + "\"";
            }

            Parms += "]";

            String Blocks = "[";
            DecompileResults res = ifc.decompileFunction(function, 0, null);
            HighFunction hf = res.getHighFunction();
            first = true;
            for (PcodeBlockBasic var : hf.getBasicBlocks()){
                if (first == false) { Blocks += ", "; }
                first = false;
                Blocks += Long.parseLong(var.getStart()+ "", 16);
            }
            Blocks += "]";

            print("\nRESULTF: {\"name\":\"" + function.getName() + "\","          +
                "\"vaddr\":\"" + function.getEntryPoint() + "\","    +
                "\"blocks\":" + Blocks + ","                         +
                "\"params\": " + Parms + ","                         + //list of parameters, iterator?
                "\"retType\": \"" +function.getReturn() + "\","      +  // return type of function
                "\"signature\": \"" +function.getSignature() + "\"," +
                "\"returning\": \"" + !function.hasNoReturn() + "\"}" + "\n\n");

            function = getFunctionAfter(function);
        }
    }
}
