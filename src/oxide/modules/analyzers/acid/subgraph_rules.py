rule_groupings = {
    "Grabs a DNS and sends a HTTP Request to it": ["resolve DNS", "send HTTP request"],
    "Sends encoded data over a socket": [
        "encode data using XOR",
        "send data on socket",
    ],
    "Sends encoded data over a socket": [
        "encode data using Base64",
        "send data on socket",
    ],
    "Sends encoded data over a socket": [
        "encode data using SHA256",
        "send data on socket",
    ],
    "Gathering Machine Information": [
        "get hostname",
        "get OS information",
        "get number of processors",
        "get networking interfaces",
        "get kernel version",
        "get system information on Windows",
        "get session user name",
        "get geographical location",
        "get OS version",
    ],
    "Checks to see if it is already running, if it isn't, then it will run": [
        "check mutex",
        "create mutex",
    ],
    "Remote Access": ["open network connection", "accept command line input"],
    "Gathering User Information": ["get session user name", "get token membership"],
    "Run the specified file on startup": [
        "write file on Windows",
        "persist via Run registry key",
    ],
    "Creates a new file and deletes itself": [
        "self delete",
        "write file on linux",
        "write file on Windows",
    ],
    "Open a file and write information to it": [
        "write file on Linux",
        "create or open file",
    ],
    "Finding and terminating a process": [
        "terminate process via kill",
        "enumerate processes",
    ],
    "Hashing file data": ["enumerate files", "hash data using SHA256"],
    "Obfuscating commands": ["refrence Base64 string", "decode Base64 string"],
    "Gain access to a file and run it": [
        "change file permission on Linux",
        "start process",
    ],
    "Pre-execution check": ["check for software breakpoints", "get OS information"],
    "Anti-debugging": [
        "check for software breakpoints",
        "reference anti-VM strings targeting VMWare",
        "reference analysis tools strings",
    ],
    "Overwriting Registry Value": ["delete registry value", "write registry value"],
    "Create file backups": ["create directory", "copy file"],
    "Escalating Privileges to drop a file": [
        "modify access privileges",
        "create or open file",
    ],
    "Check to see if it is the right operating system and remove itself if not": [
        "check OS version",
        "self delete",
    ],
    "Check to see if it is in the correct region and remove itself if not": [
        "get geographic location",
        "self delete",
    ],
    "Check to see if it has already copied itself and remove itself if so": [
        "query registry key",
        "self delete",
    ],
    "Write information to a pipe": ["create pipe", "write data to pipe"],
    "": [],
}