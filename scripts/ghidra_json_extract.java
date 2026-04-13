import java.io.FileWriter;
import java.io.PrintWriter;

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSetView;
import ghidra.program.model.block.CodeBlock;
import ghidra.program.model.block.CodeBlockIterator;
import ghidra.program.model.block.CodeBlockReference;
import ghidra.program.model.block.CodeBlockReferenceIterator;
import ghidra.program.model.block.SimpleBlockModel;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Instruction;
import ghidra.program.model.listing.InstructionIterator;
import ghidra.program.model.listing.Parameter;

public class ghidra_json_extract extends GhidraScript {
    private static String json(String value) {
        if (value == null) {
            return "null";
        }

        StringBuilder escaped = new StringBuilder();
        escaped.append('"');
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '\\':
                    escaped.append("\\\\");
                    break;
                case '"':
                    escaped.append("\\\"");
                    break;
                case '\n':
                    escaped.append("\\n");
                    break;
                case '\r':
                    escaped.append("\\r");
                    break;
                case '\t':
                    escaped.append("\\t");
                    break;
                default:
                    escaped.append(c);
                    break;
            }
        }
        escaped.append('"');
        return escaped.toString();
    }

    private String instructionText(Instruction instruction) {
        String text = instruction.getMnemonicString();
        for (int i = 0; i < instruction.getNumOperands(); i++) {
            if (i == 0) {
                text += "  ";
            } else {
                text += ",";
            }
            text += instruction.getDefaultOperandRepresentation(i);
        }
        return text;
    }

    public void run() throws Exception {
        String[] args = getScriptArgs();
        if (args.length < 1) {
            throw new IllegalArgumentException("Expected output JSON path as first script argument");
        }

        String outputPath = args[0];
        SimpleBlockModel blockModel = new SimpleBlockModel(currentProgram);
        StringBuilder out = new StringBuilder();

        out.append("{");
        out.append("\"meta\":{");
        out.append("\"format\":").append(json(currentProgram.getExecutableFormat())).append(",");
        out.append("\"image_base\":").append(json(currentProgram.getImageBase().toString()));
        out.append("},");

        out.append("\"instructions\":[");
        InstructionIterator instructions = currentProgram.getListing().getInstructions(true);
        boolean firstInstruction = true;
        while (instructions.hasNext()) {
            Instruction instruction = instructions.next();
            CodeBlock block = blockModel.getFirstCodeBlockContaining(instruction.getAddress(), monitor);

            if (!firstInstruction) {
                out.append(",");
            }
            firstInstruction = false;

            out.append("{");
            out.append("\"address\":").append(json(instruction.getAddress().toString())).append(",");
            out.append("\"text\":").append(json(instructionText(instruction))).append(",");
            out.append("\"block\":").append(json(block == null ? null : block.getFirstStartAddress().toString()));
            out.append("}");
        }
        out.append("],");

        out.append("\"blocks\":[");
        CodeBlockIterator blocks = blockModel.getCodeBlocks(monitor);
        boolean firstBlock = true;
        while (blocks.hasNext()) {
            CodeBlock block = blocks.next();

            if (!firstBlock) {
                out.append(",");
            }
            firstBlock = false;

            out.append("{");
            out.append("\"address\":").append(json(block.getFirstStartAddress().toString())).append(",");

            out.append("\"dests\":[");
            CodeBlockReferenceIterator dests = block.getDestinations(monitor);
            boolean firstDest = true;
            while (dests.hasNext()) {
                CodeBlockReference dest = dests.next();
                if (!firstDest) {
                    out.append(",");
                }
                firstDest = false;
                out.append(json(dest.getDestinationAddress().toString()));
            }
            out.append("],");

            out.append("\"members\":[");
            Address address = block.getFirstStartAddress();
            boolean firstMember = true;
            while (block.contains(address)) {
                if (!firstMember) {
                    out.append(",");
                }
                firstMember = false;
                out.append(json(address.toString()));
                address = currentProgram.getListing().getCodeUnitAfter(address).getAddress();
            }
            out.append("]");
            out.append("}");
        }
        out.append("],");

        out.append("\"functions\":[");
        Function function = getFirstFunction();
        boolean firstFunction = true;
        while (function != null) {
            if (!firstFunction) {
                out.append(",");
            }
            firstFunction = false;

            out.append("{");
            out.append("\"name\":").append(json(function.getName(true))).append(",");
            out.append("\"vaddr\":").append(json(function.getEntryPoint().toString())).append(",");

            out.append("\"blocks\":[");
            AddressSetView addresses = function.getBody();
            CodeBlockIterator functionBlocks = blockModel.getCodeBlocksContaining(addresses, monitor);
            boolean firstFunctionBlock = true;
            while (functionBlocks.hasNext()) {
                if (!firstFunctionBlock) {
                    out.append(",");
                }
                firstFunctionBlock = false;
                out.append(json(functionBlocks.next().getFirstStartAddress().toString()));
            }
            out.append("],");

            out.append("\"params\":[");
            boolean firstParam = true;
            for (Parameter parameter : function.getParameters()) {
                if (!firstParam) {
                    out.append(",");
                }
                firstParam = false;
                out.append(json(parameter.getFormalDataType().toString()));
            }
            out.append("],");

            out.append("\"retType\":").append(json(function.getReturn().toString())).append(",");
            out.append("\"signature\":").append(json(function.getSignature().toString())).append(",");
            out.append("\"returning\":").append(!function.hasNoReturn());
            out.append("}");

            function = getFunctionAfter(function);
        }
        out.append("]");
        out.append("}");

        try (PrintWriter writer = new PrintWriter(new FileWriter(outputPath))) {
            writer.print(out.toString());
        }
    }
}