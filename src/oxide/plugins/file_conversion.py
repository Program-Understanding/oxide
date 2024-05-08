""" 
  Plugin: Conversions for file formats
  Requirements:

  pip3 install bincopy
  Supported Formats
    iHex
"""
import sys
import os
import bincopy
import argparse
from pathlib import Path
def convert_ihex(args, opts):
    """
        Converts ihex to 
        Syntax: convert_ihex file_path
        Options: 
          -d: convert all ihex files in a directory
          -r: recursively convert all ihex files in a directory
    """ 
  
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('-h' , '--help', help = 'show this help', action='store_true')
    parser.add_argument('-d', '--directory', action='store_true', help="Converts ihex files in a given directory")
    parser.add_argument('-r', '--recursive', action='store_true', help="Recursively converts ihex files in a given directory")
    parser.add_argument('-i', '--input', dest="input_filepath", help="Path to the input file or directory")
    parser.add_argument('-o', '--output', dest="output_filepath", help="Path to the output directory")

    parse_args = parser.parse_args(args)
    if parse_args.help:
        parser.print_help()
        return 
    elif not parse_args.input_filepath:
        print("Missing input filepath to file or directory\n")
        parser.print_help()
    elif not parse_args.output_filepath:
        print("Missing output filepath to a directory\n")

    validated_output_dir = valid_dir(parse_args.output_filepath)

    if parse_args.recursive:
        print("Working")
    elif parse_args.directory:       
        print("Working")
    else:
        validated_input_file = valid_file(parse_args.input_filepath)
        if validated_input_file:
            convert(validated_input_file, validated_output_dir)
        else:
            print(parse_args.input_filepath + "is not a valid file.\n")
  

exports = [convert_ihex]

def convert(input_path, output_path):
    ipt = bincopy.BinFile(str(input))
    f = open("{output_path}{input_path.name}_ihex.bin", "x") 
    f.write(ipt.as_binary(), 'wb')

def valid_file(filepath):
    if (path:= Path(filepath).is_file()):
        return path
    else:
        raise FileNotFoundError

def valid_dir(filepath):
    if (path:= Path(filepath).is_dir()):
        return path
    else:
        raise FileNotFoundError

