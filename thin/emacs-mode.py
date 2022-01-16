import sys

with open(sys.argv[1]) as f:
    text = f.read()
    pos = 1
    for line in text.split('\n'):
        if line != "":
            if len(line) >= 4:
                status = 'ok'
            else:
                status = 'bad'
            print(f"range {pos} {pos+len(line)} {status}")
        pos += len(line) + 1
