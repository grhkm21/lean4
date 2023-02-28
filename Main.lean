import Lean4.Hello

def main (args : List String) : IO Unit :=
  if args.length = 0 then
    IO.println s!"No arguments, so hello, grhkm!"
  else
    IO.println s!"Hello, {hello2}!"
