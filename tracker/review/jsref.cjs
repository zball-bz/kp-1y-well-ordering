const Y1 = require(process.env.Y1_ENGINE || '/home/dev/ggg/1Y-Well-Ordering-Lean/y1/engine.js');
let data=''; process.stdin.on('data',d=>data+=d); process.stdin.on('end',()=>{
  const tests = JSON.parse(data); const out = [];
  for (const [s,n] of tests) { try { out.push(Y1.expand(s.map(BigInt), n).result.map(Number)); } catch(e) { out.push(null); } }
  console.log(JSON.stringify(out));
});
