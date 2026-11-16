"""Count reduced residuals without expanding their sum of squares."""
import importlib.util
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'
spec=importlib.util.spec_from_file_location('compiler', BASE/'compiler/compile_ir.py')
mod=importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
data=json.loads((HERE/'raw-translated-ir.json').read_text())
c=mod.Compiler(data)
reduction=c.reduce()
active=set().union(*(mod.variables(r) for r in c.rows.values()))
report={'raw':data['counts'],'reduction':reduction,'reduced_coordinates':len(c.coordinates),'active_coordinates':len(active),'reduced_residuals':len(c.rows),'maximum_residual_degree':max(map(mod.degree,c.rows.values()))}
(HERE/'measured.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
