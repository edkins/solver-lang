import os
import sys
sys.path.insert(0, os.path.dirname(os.path.dirname(__file__)))
from thin2.process import process

with open(sys.argv[1]) as f:
    text = f.read()
    print(process(text))
