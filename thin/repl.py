import readline
import sys
import traceback
from thin.session import Session
from thin.errors import Mistake

def main():
    global grammar
    session = Session(sys.stdout, True)
    while True:
        text = input(session.prompt())
        try:
            session.parse_and_process(text)
        except Mistake as ex:
            traceback.print_exc()

if __name__ == '__main__':
    main()

