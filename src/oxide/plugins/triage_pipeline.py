
from oxide.core.oxide import api
from cpu_rec import cpu_rec
import pprint
def pipeline_tag(args, opts) -> None:
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)

    
    for oid in oids:
        header = api.get_field("object_header", oid, oid)
        data = api.get_field(api.source(oid), oid, "data", {}) 
        file_name = api.get_field("file_meta", oid, "names").pop()
        f_name = api.tmp_file(file_name, data) 
        tags = {"triage_tags": {}}
        
        
        triage_tags= tags["triage_tags"]
        # Tag the source type
        src_type = api.get_field("src_type", oid, "type")
            
        if "ELF" in src_type:
            triage_tags["SRC_TYPE"] = "ELF"
        elif "PE" in src_type:
            triage_tags["SRC_TYPE"] = "PE"
        elif "MACHO" in src_type:
            triage_tags["SRC_TYPE"] = "MACHO"
        else:
            triage_tags["SRC_TYPE"] = "UNKNOWN"
        
        #Tag the architecture  
        if triage_tags["SRC_TYPE"] == "ELF"  or triage_tags["SRC_TYPE"] == "PE":
            if header:
                arch = header.machine
                triage_tags["ARCH"] = arch
        elif triage_tags["SRC_TYPE"] == "UNKNOWN":
            
            cpu_rec_result = cpu_rec.which_arch(open(f_name, "rb").read())
            if cpu_rec_result:
                triage_tags["ARCH"] = cpu_rec_result
            else:
                triage_tags["ARCH"] = "UNKNOWN"
            
            
            # Can we get the data sheet. Dont have a module to harvest data sheets.
                # Do we have the memory map?
                    # Tag it
                # Do we know the base address? Dont have a module for this.
                    # Tag it


        # Tag if its packed
        packed_result = api.retrieve("packer_detect", oid)[oid]
        if packed_result != None:
            is_packed = packed_result["likely_packed"]
            if is_packed:
                triage_tags["PACKED"] = True
            else:
                triage_tags["PACKED"] = False
        else:
            triage_tags["PACKED"] = "ERROR"
            
        # Does it contain high entropy sections?
        binwalk_results = api.retrieve("binwalk_utils", oid)
        sigs = binwalk_results["signature"]
        entropies = binwalk_results["entropy"]
        
        sig_tags = []
        if sigs:
            for offset, sig in sigs.items():
                sig_tags.append(sig)
            triage_tags["SIGNATURES"] = sig_tags
        else:
            triage_tags["SIGNATURES"] = "ERROR"
            
        if entropies:
            for offset, entropy in entropies.items():
                if entropy > 0.9:
                    triage_tags["HIGH_ENTROPY"] = True
                    break
            else:
                triage_tags["HIGH_ENTROPY"] = False
        else:
            triage_tags["HIGH_ENTROPY"] = "ERROR"
            
        
        
        # Grayson's Module
        # Do we know the hardware? Grayson's module / 
            # Tag the hardware
            
            
        
            
        # Ahmed's work
        # Is this a somewhat know file? There is not a module for this.
            # Tag original file oid? Yes? Safe? No?
            
        # 
        api.apply_tags(oid, tags)    
        
def get_pipeline_tag(args, opts):
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)
    
    for oid in oids:
        file_name = api.get_field("file_meta", oid, "names").pop()
        tags = api.get_tags(oid)
        print(f"\noid - {oid}\nfile name - {file_name}\ntags -")
        pprint.pprint(tags)
    
    return True

def clear_pipeline_tag(args, opts):
    valid, invalid = api.valid_oids(args)
    oids = api.expand_oids(valid)
    
    for oid in oids:
        original_time = api.get_tags(oid)["creation_time"]
        api.local_delete_data("tags", oid)
    return True

exports = [pipeline_tag, get_pipeline_tag, clear_pipeline_tag]