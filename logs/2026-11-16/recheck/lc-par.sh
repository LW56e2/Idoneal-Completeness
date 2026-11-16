#!/bin/sh
ulimit -n 65536
export PATH=/root/.elan/bin:$PATH
cd /root/idoneal-lean
LP=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$LP"
BIN=/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/leanchecker
mkdir -p /root/lc; rm -f /root/lc/*.out
S=$(date +%s)
for m in $(cat /root/lc.mods); do
  ( T=$(date +%s); timeout 1800 $BIN $m > /root/lc/$m.out 2>&1; echo "exit $? seconds $(( $(date +%s) - T ))" >> /root/lc/$m.out ) &
done
wait
echo "all done seconds $(( $(date +%s) - S ))" > /root/lc.summary
touch /root/lc.done
