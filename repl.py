import readline
import traceback
from z3lang.session import Session
from z3lang.errors import Mistake

def main():
    global grammar
    session = Session()
    while True:
        text = input(session.prompt())
        try:
            session.parse_and_process(text)
        except Mistake as ex:
            traceback.print_exc()

if __name__ == '__main__':
    main()
