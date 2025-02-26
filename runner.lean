import Problems.P10

def main : IO Unit :=
  -- Define a list of names
  let inputs := [200, 2000, 20000, 200000, 2000000, 20000000, 200000000] -- 2000000000 does not work
  for input in inputs do
    IO.println input
    IO.println (S_impl input)
    -- IO.println (S input)

-- #eval main
-- lake build runner
-- .lake/build/bin/runner
