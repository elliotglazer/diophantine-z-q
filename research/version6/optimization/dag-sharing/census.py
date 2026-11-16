from pathlib import Path
import importlib.util,json,hashlib,sys
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'
spec=importlib.util.spec_from_file_location('compiler',BASE/'compiler/compile_ir.py')
c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
OUT=Path(sys.argv[1]) if len(sys.argv)>1 else HERE
path=OUT/'raw-translated-ir.json'
data=json.loads(path.read_text()); compiler=c.Compiler(data,c.digest(path))
reduction=compiler.reduce(); compiler.normalize()
out=compiler.output(); active=set().union(*(c.variables(p) for p in compiler.rows.values()))
report={'raw':data['counts'],'reduction':reduction,'activeCoordinates':len(active),'residuals':len(compiler.rows),'maximumResidualDegree':max(map(c.degree,compiler.rows.values())),'quarticDegree':4,'savingsFrom1272':1272-len(active)}
for name,obj in [('compiled-ir.json',out),('reduction-certificate.json',compiler.certificate),('measured-census.json',report)]:
 (OUT/name).write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(report,indent=2))
