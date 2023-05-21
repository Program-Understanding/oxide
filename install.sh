#!/bin/bash

# Check if the script is executed as sudo
if [[ $EUID -eq 0 ]]; then
   echo "This script should not be run as root" 
   exit 1
fi

# Check if python3 is installed
if ! command -v python3 &> /dev/null
then
    echo "Python3 is not installed. Installing..."
    sudo apt-get update
    sudo apt-get install -y python3
fi

# Check if pip3 is installed
if ! command -v pip3 &> /dev/null
then
    echo "pip3 is not installed. Installing..."
    sudo apt-get install -y python3-pip
fi

# Check if numpy is installed
if ! python3 -c "import numpy" &> /dev/null
then
    echo "Numpy is not installed. Installing..."
    pip3 install numpy
fi

# Check if git is installed
if ! command -v git &> /dev/null
then
    echo "git is not installed. Installing..."
    sudo apt-get install -y git
fi

# Check to see if the current directory is the oxide.git repository
if [[ "$(git rev-parse --show-toplevel)" != "$HOME/oxide" ]]; then
    cd $HOME
    if [ ! -d "$HOME/oxide" ]; then
        git clone https://github.com/Program-Understanding/oxide.git
    else
        cd oxide
        git pull
    fi
else
    git pull
fi

# Add a symlink of shell.py in the git repository to /usr/bin/oxide
if [ -f "$HOME/oxide/shell.py" ]; then
    sudo ln -s "$HOME/oxide/shell.py" /usr/bin/oxide
else
    echo "File shell.py does not exist in the oxide repository."
fi

chmod +x $HOME/oxide/shell.py
