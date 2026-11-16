from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'
text=(BASE/'builder/build_source.cjs').read_text()
old='let points={};for(let n of names)points[n]=double(n,half[n],true);'
assert text.count(old)==1
text=text.replace(old,(HERE/'point-replacement.cjs').read_text())
text=text.replace("n+'.half.x0'","n+'.chart.t0'").replace("n+'.half.x1'","n+'.chart.t1'").replace("n+'.half.y0'","n+'.chart.h0'").replace("n+'.half.y1'","n+'.chart.h1'")
text=text.replace("const inputSource=path.resolve(__dirname,'..',sourceName);",f"const inputSource={str(BASE/'sources/diophantine_optimization_20261106_v3.tex')!r};")
out=HERE/'point-candidate';out.mkdir(exist_ok=True)
(out/'build_source.cjs').write_text(text)
