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

import java.util.*;

import org.apache.commons.lang3.ObjectUtils.Null;
import org.tukaani.xz.check.None;

import ghidra.app.script.GhidraScript;
import ghidra.program.model.mem.*;
import ghidra.program.model.lang.*;
import ghidra.program.model.pcode.*;
import ghidra.program.model.util.*;
import ghidra.program.util.DefinedDataIterator;
import ghidra.program.util.ProgramLocation;
import ghidra.program.model.reloc.*;
import ghidra.program.model.data.*;
import ghidra.program.model.block.*;
import ghidra.program.model.symbol.*;
import ghidra.program.model.scalar.*;
import ghidra.program.model.listing.*;
import ghidra.program.model.address.*;
import ghidra.app.util.XReferenceUtils.*;
import ghidra.app.util.XReferenceUtils;
import ghidra.app.util.XReferenceUtil.*;
import ghidra.app.decompiler.*;

public class string_reference extends GhidraScript {

    
    Address baseAddress;
    public String fixAddress(Address a) {
        return "" + a.subtract(baseAddress);
    }

    public String getStringAtAddr(Address addr) {
        Data data = getDataAt(addr);
        if (data != null) {
            DataType dt = data.getDataType();
            if (dt instanceof StringDataType) {
                return data.getDefaultValueRepresentation();
            }
        }
        return null;
    }
    public void run() throws Exception {
        InstructionIterator ii = currentProgram.getListing().getInstructions(true);
        while (ii.hasNext() ) {
            Instruction in = ii.next();
            int numOperands = in.getNumOperands();
            for (int i = 0; i < numOperands; i++) {
               Reference[] opRefs = in.getOperandReferences(i);
                for (Reference reference : opRefs) {
                    if (reference.getReferenceType().isData()) {
                        
                        String str = getStringAtAddr(reference.getToAddress());
                        if (str != null) {
                            print("\nRESULTS: " +  "[\"" + in.getAddress() + "\", \""  + reference.getToAddress().toString() + "\", " + str + "]\n\n");
                        }
                    }
                }
            }
        }
    }
}
