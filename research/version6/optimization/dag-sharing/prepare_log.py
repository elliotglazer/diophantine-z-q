from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]/'quartic-version5-release/repository/quartics/quartic-1272'
text=(BASE/'builder/build_source.cjs').read_text()
start=text.index('function log(name,p,e){')
end=text.index('const LU=',start)
text=text[:start]+(HERE/'log-replacement.cjs').read_text()+text[end:]
text=text.replace("const inputSource=path.resolve(__dirname,'..',sourceName);",f"const inputSource={str(BASE/'sources/diophantine_optimization_20261106_v3.tex')!r};")
out=HERE/'log-candidate';out.mkdir(exist_ok=True)
text=text.replace("console.log(JSON.stringify({counts:data.counts,census},null,2));", "fs.writeFileSync(path.join(OUT,'square-completion.json'),JSON.stringify({a:aCoeffs.map(qstr),q:squareQ.map(qstr),r:squareR.map(qstr)},null,2));console.log(JSON.stringify(data.counts));")
(out/'build_source.cjs').write_text(text)
