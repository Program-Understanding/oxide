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

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import ghidra.app.decompiler.ClangLine;
import ghidra.app.decompiler.ClangToken;
import ghidra.app.decompiler.ClangTokenGroup;
import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.decompiler.component.DecompilerUtils;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;
import ghidra.program.model.listing.FunctionManager;

public class decompile_mapping extends GhidraScript {

    private static final String SCRIPT_NAME = "decompile_mapping.java";

    private void log(String message) {
        println(SCRIPT_NAME + ": " + message);
    }

    private String hexEscape(String input) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < input.length(); i++) {
            char c = input.charAt(i);
            if (c >= 32 && c <= 126) {
                sb.append(c);
            }
            else {
                sb.append(String.format("\\x%02x", (int) c));
            }
        }
        return sb.toString();
    }

    @SuppressWarnings("unchecked")
    private void addLineEntry(Map<String, Object> funcMap, String addrKey, String taggedLine, String tokenText) {
        Map<String, Object> entry = (Map<String, Object>) funcMap.get(addrKey);
        if (entry == null) {
            entry = new LinkedHashMap<String, Object>();
            funcMap.put(addrKey, entry);
        }

        List<String> lines = (List<String>) entry.get("line");
        if (lines == null) {
            lines = new ArrayList<String>();
            entry.put("line", lines);
        }
        if (!lines.contains(taggedLine)) {
            lines.add(taggedLine);
        }

        if (tokenText != null) {
            List<String> tokens = (List<String>) entry.get("tokens");
            if (tokens == null) {
                tokens = new ArrayList<String>();
                entry.put("tokens", tokens);
            }
            tokens.add(tokenText);
        }
    }

    @SuppressWarnings("unchecked")
    private Map<String, Object> buildMapping() throws Exception {
        log("buildMapping() starting");

        DecompInterface decomp = new DecompInterface();
        decomp.openProgram(currentProgram);

        FunctionManager functionManager = currentProgram.getFunctionManager();
        int functionCount = functionManager.getFunctionCount();
        log("opened program '" + currentProgram.getName() + "' with " + functionCount + " functions");

        Map<String, Object> outputMap = new LinkedHashMap<String, Object>();
        Map<String, Object> meta = new LinkedHashMap<String, Object>();
        Map<String, Object> functionMeta = new LinkedHashMap<String, Object>();
        outputMap.put("meta", meta);
        meta.put("load_addr", currentProgram.getImageBase().toString());
        meta.put("functions", functionMeta);
        meta.put("function_count", Integer.valueOf(functionCount));

        int processedCount = 0;
        int failedCount = 0;
        List<String> failedFunctions = new ArrayList<String>();

        FunctionIterator functionIter = functionManager.getFunctions(true);
        while (functionIter.hasNext()) {
            Function function = functionIter.next();
            if (function == null) {
                continue;
            }

            String funcName = function.getName(true);
            Map<String, Object> funcMap = (Map<String, Object>) outputMap.get(funcName);
            if (funcMap == null) {
                funcMap = new LinkedHashMap<String, Object>();
                outputMap.put(funcName, funcMap);

                Map<String, Object> funcMeta = new LinkedHashMap<String, Object>();
                funcMeta.put("entry", function.getEntryPoint().toString());
                functionMeta.put(funcName, funcMeta);
            }

            try {
                DecompileResults results = decomp.decompileFunction(function, 120, monitor);
                if (results == null || !results.decompileCompleted()) {
                    log("decompilation did not complete for " + funcName);
                    continue;
                }

                ClangTokenGroup markup = results.getCCodeMarkup();
                if (markup == null) {
                    log("no C markup returned for " + funcName);
                    continue;
                }

                List<ClangLine> lines = DecompilerUtils.toLines(markup);
                for (int i = 0; i < lines.size(); i++) {
                    ClangLine line = lines.get(i);
                    String escapedLine = hexEscape(line.toString());
                    if (escapedLine.length() > 30 && escapedLine.substring(0, 30).contains("WARNING:")) {
                        continue;
                    }

                    String taggedLine = Integer.toString(i + 1) + ": " + escapedLine;
                    boolean lineAdded = false;

                    List<ClangToken> tokens = line.getAllTokens();
                    if (tokens != null) {
                        for (ClangToken token : tokens) {
                            if (token == null) {
                                continue;
                            }

                            Address minAddr = token.getMinAddress();
                            if (minAddr == null) {
                                continue;
                            }

                            addLineEntry(funcMap, minAddr.toString(), taggedLine, hexEscape(token.toString()));
                            lineAdded = true;
                        }
                    }

                    if (!lineAdded) {
                        addLineEntry(funcMap, "None", taggedLine, null);
                    }
                }

                processedCount += 1;
            }
            catch (Exception e) {
                log("ERROR in function " + funcName + ": " + e);
                e.printStackTrace();
                failedFunctions.add(funcName);
                failedCount += 1;
            }
        }

        meta.put("processed_functions", Integer.valueOf(processedCount));
        meta.put("failed_function_count", Integer.valueOf(failedCount));
        if (!failedFunctions.isEmpty()) {
            meta.put("failed_functions", failedFunctions);
        }

        log("buildMapping() finished: processed=" + processedCount + " failed=" + failedCount);
        return outputMap;
    }

    @SuppressWarnings("unchecked")
    private String toJson(Object value) {
        if (value == null) {
            return "null";
        }
        if (value instanceof String) {
            return "\"" + escapeJson((String) value) + "\"";
        }
        if (value instanceof Number || value instanceof Boolean) {
            return value.toString();
        }
        if (value instanceof Map<?, ?>) {
            StringBuilder sb = new StringBuilder();
            sb.append("{");
            boolean first = true;
            for (Map.Entry<Object, Object> entry : ((Map<Object, Object>) value).entrySet()) {
                if (!first) {
                    sb.append(",");
                }
                first = false;
                sb.append(toJson(entry.getKey().toString()));
                sb.append(":");
                sb.append(toJson(entry.getValue()));
            }
            sb.append("}");
            return sb.toString();
        }
        if (value instanceof List<?>) {
            StringBuilder sb = new StringBuilder();
            sb.append("[");
            boolean first = true;
            for (Object item : (List<Object>) value) {
                if (!first) {
                    sb.append(",");
                }
                first = false;
                sb.append(toJson(item));
            }
            sb.append("]");
            return sb.toString();
        }
        return "\"" + escapeJson(value.toString()) + "\"";
    }

    private String escapeJson(String value) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            switch (c) {
                case '\\':
                    sb.append("\\\\");
                    break;
                case '"':
                    sb.append("\\\"");
                    break;
                case '\b':
                    sb.append("\\b");
                    break;
                case '\f':
                    sb.append("\\f");
                    break;
                case '\n':
                    sb.append("\\n");
                    break;
                case '\r':
                    sb.append("\\r");
                    break;
                case '\t':
                    sb.append("\\t");
                    break;
                default:
                    if (c < 32) {
                        sb.append(String.format("\\u%04x", (int) c));
                    }
                    else {
                        sb.append(c);
                    }
            }
        }
        return sb.toString();
    }

    private void writeJson(Path outputPath, Map<String, Object> payload) throws Exception {
        Path parent = outputPath.getParent();
        if (parent != null) {
            Files.createDirectories(parent);
        }
        Files.write(outputPath, toJson(payload).getBytes(StandardCharsets.UTF_8));
    }

    public void run() throws Exception {
        log("script started");
        String[] args = getScriptArgs();
        log("args = " + java.util.Arrays.toString(args));

        if (args == null || args.length == 0) {
            throw new RuntimeException("No output path argument provided");
        }

        Path outputPath = Paths.get(args[0]);
        Map<String, Object> payload;
        try {
            payload = buildMapping();
        }
        catch (Exception e) {
            log("ERROR while building mapping: " + e);
            e.printStackTrace();
            payload = new LinkedHashMap<String, Object>();
            Map<String, Object> meta = new LinkedHashMap<String, Object>();
            meta.put("error", e.toString());
            meta.put("exception_type", e.getClass().getName());
            payload.put("meta", meta);
        }

        log("writing JSON to " + outputPath);
        writeJson(outputPath, payload);
        log("successfully wrote JSON output");
    }
}
