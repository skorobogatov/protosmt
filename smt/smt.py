from argparse import ArgumentParser

from smt.interpreters import Position, MessageSet, Smtlib


parser = ArgumentParser(description='Experimental SMT solver.')
parser.add_argument('files', metavar='File', type=str, nargs='+',
                    help='a file in SMTLIB language')

args = parser.parse_args()
ms = MessageSet()
interpreter = Smtlib(ms)
for filename in args.files:
    pos = Position.beginning_of(filename)
    interpreter.execute(pos)
    if len(ms) > 0:
        for m in ms:
            print(m)
        ms.clear()
