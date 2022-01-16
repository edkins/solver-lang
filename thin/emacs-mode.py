import sys

linenum = 1
for line0 in open(sys.argv[1]):
    line = line0.strip()
    if line != "":
        if len(line) >= 4:
            status = 'ok'
        else:
            status = 'bad'
        print(f"line {linenum} {status}")
    linenum += 1
