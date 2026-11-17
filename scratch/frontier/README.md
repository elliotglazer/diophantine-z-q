# scratch/frontier

Scripts and outputs of the frontier report, `docs/research/frontier.md` (its header lists the files).

Run `chain.py` from the repository root:

```
python3 scratch/frontier/chain.py        # scenarios A and F
python3 scratch/frontier/chain.py onep   # ZInQ.OneProof.frozenTarget against scenario A
python3 scratch/frontier/chain.py doc    # the report's rows against scenario F
```

`chainlib.py` reads files with `git -C .`, so from any other directory the text of `ZInQKernel/OneProof/H/` comes
back empty without an error, and the definition checks give wrong verdicts ("DIFFERENT or missing"). `chain_out.txt`
is the output of the three commands above, in that order.
