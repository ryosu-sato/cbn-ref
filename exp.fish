#!/usr/bin/env fish

if count $argv >/dev/null
  set FILES $argv
else
  set FILES benchmark/*.in
end

for i in $FILES
  echo -n "$i, "

  # Ours
  set _started_at (date +'%s.%3N')
  set R (src/main.exe $i -exp)
  set _ended_at (date +'%s.%3N')
  set _elapsed (echo "scale=3; $_ended_at - $_started_at" | bc)
  echo -n "$R, "
  echo -n "$_elapsed, "
  set hs (string replace .in .hs (string replace benchmark benchmark/LiquidHaskell $i))

  # LiquidHaskell
  set _started_at (date +'%s.%3N')
  set R (liquid $hs)
  set _ended_at (date +'%s.%3N')
  set RR (echo $R | grep LIQUID | sed -r 's/^.* (.?.?SAFE) .*$/\1/')
  echo -n "$RR, "
  set _elapsed (echo "scale=3; $_ended_at - $_started_at" | bc)
  echo -n "$_elapsed, "

  # LiquidHaskell-nt
  set _started_at (date +'%s.%3N')
  set R (liquid $hs --notermination)
  set _ended_at (date +'%s.%3N')
  set RR (echo $R | grep LIQUID | sed -r 's/^.* (.?.?SAFE) .*$/\1/')
  echo -n "$RR, "
  set _elapsed (echo "scale=3; $_ended_at - $_started_at" | bc)
  echo "$_elapsed"
end
