
from oxide.core.oxide import api

def pipeline_tag(args, opts) -> None:
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)

    
    for oid in oids:
        tags = {"triage_tags": {}}
        
        
        triage_tags= tags["triage_tags"]
        # Tag the source type
        src_type = api.get_field("src_type", oid, "type")
        if "ELF" in src_type:
            triage_tags["SRC_TYPE"] = "ELF"
        elif "PE" in src_type:
            tags["SRC_TYPE"] = "PE"
        elif "MACHO" in src_type:
            tags["SRC_TYPE"] = "MACHO"
        else:
            tags["SRC_TYPE"] = "UNKNOWN"
        
        
        # Is it firmware - No module?
            # Tag it as firmware
            
            
            
            # Can we get the data sheet. Dont have a module to harvest data sheets.
                # Do we have the memory map?
                    # Tag it
                # Do we know the base address? Dont have a module for this.
                    # Tag it
        # What is the architecture? Grayson's module/ Prob disasm / ghidra / binja / radare /
            # Tag the arch
        
        # Is it packed - 
            # If so tag it as packed
        
        # Can we unpack it? - binwalk module / ghidra / unblob / autopsy / ...
            # If so tag it as unpackable
            
        

            
        # Grayson's Module
        # Do we know the hardware? Grayson's module / 
            # Tag the hardware
            
            
        
            
        # Ahmed's work
        # Is this a somewhat know file? There is not a module for this.
            # Tag original file oid? Yes? Safe? No?
            
        # 
        api.apply_tags(oid, tags)    
        
exports = [pipeline_tag]