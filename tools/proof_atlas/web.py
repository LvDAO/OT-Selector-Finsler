"""Small read-only loopback explorer; proof execution is an explicit CLI action."""

from __future__ import annotations

from http.server import BaseHTTPRequestHandler, HTTPServer
import json
from urllib.parse import parse_qs, urlparse

from .manifest import source_manifest
from .retrieval import search
from .verify import load_patterns


PAGE = """<!doctype html><html lang="zh"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Lean Proof Atlas</title><style>
body{font:16px system-ui;background:#f4f2ec;color:#18252b;margin:0;padding:24px}
main{max-width:1400px;margin:auto}h1{font-size:26px}input,select,button{font:inherit;padding:9px;border:1px solid #bbc4bf;border-radius:5px;background:white}
input{width:min(620px,70%)}button{cursor:pointer}#results{display:flex;gap:20px;margin-top:20px}aside{width:28%;min-width:220px}
article{flex:1;min-width:0}pre{white-space:pre-wrap;overflow-wrap:anywhere;font-size:13px;background:#fff;padding:16px;border-radius:6px;max-height:65vh;overflow:auto}
aside:empty{display:none}
.columns{display:grid;grid-template-columns:1fr 1fr;gap:14px}.proof{grid-column:1/-1}.hit{display:block;text-align:left;width:100%;margin:7px 0;font-size:13px;overflow-wrap:anywhere}
.graph{max-height:440px;overflow:auto;background:white;border-radius:6px}.graph svg{min-width:720px;width:100%;display:block}
.muted{color:#53645f;font-size:13px}h2{font-size:18px}h3{font-size:14px}a{color:#25654f}@media(max-width:850px){#results{display:block}aside{width:100%}.columns{display:block}}
</style><main><h1>Lean Proof Atlas</h1><p>条件 · 对象 · 证明细节</p>
<form id="form"><input id="query" placeholder="输入目标、数学方法或 Lean 标识符" required>
<select id="view"><option value="">所有视图</option><option>conditions</option><option>objects</option><option>proof_detail</option><option>proof_state</option><option>full_proof</option></select>
<button>检索</button></form><p id="status" class="muted">读取本地索引…</p>
<div id="results"><aside id="hits"></aside><article id="detail"></article></div></main>
<script>
const el=id=>document.getElementById(id);
async function get(path,params={}){let r=await fetch(path+'?'+new URLSearchParams(params));let d=await r.json();if(!r.ok)throw Error(d.error);return d;}
function box(parent,title,text,cls=''){let d=document.createElement('section');d.className=cls;let h=document.createElement('h3');h.textContent=title;let p=document.createElement('pre');p.textContent=typeof text==='string'?text:JSON.stringify(text,null,2);d.append(h,p);parent.append(d);}
function graphBox(parent,g){let h=document.createElement('h3');h.textContent='依赖 DAG · 蓝色 type_ref · 绿色 proof_ref'+(g.truncated?' · 已限制显示范围':'');parent.append(h);let wrap=document.createElement('div');wrap.className='graph';parent.append(wrap);const ns='http://www.w3.org/2000/svg',make=(tag,attrs={})=>{let x=document.createElementNS(ns,tag);for(let[k,v]of Object.entries(attrs))x.setAttribute(k,v);return x;};let cs=g.components,ind=cs.map(()=>0),rank=cs.map(()=>0),out=cs.map(()=>[]);for(let e of g.edges){ind[e.target]++;out[e.source].push(e.target);}let queue=cs.filter(c=>!ind[c.id]).map(c=>c.id);for(let i=0;i<queue.length;i++)for(let t of out[queue[i]]){rank[t]=Math.max(rank[t],rank[queue[i]]+1);if(!--ind[t])queue.push(t);}let levels=new Map(),pos=new Map();for(let c of cs){let r=rank[c.id],row=levels.get(r)||0;levels.set(r,row+1);pos.set(c.id,[r*265+20,row*48+24]);}let width=(Math.max(0,...rank)+1)*265+20,height=Math.max(100,...Array.from(levels.values()).map(n=>n*48+40));let svg=make('svg',{viewBox:`0 0 ${width} ${height}`,role:'img','aria-label':'Lean declaration dependency DAG'});wrap.append(svg);let defs=make('defs'),marker=make('marker',{id:'dagArrow',viewBox:'0 0 10 10',refX:9,refY:5,markerWidth:5,markerHeight:5,orient:'auto-start-reverse'});marker.append(make('path',{d:'M 0 0 L 10 5 L 0 10 z',fill:'#536b60'}));defs.append(marker);svg.append(defs);for(let e of g.edges){let [x,y]=pos.get(e.source),[u,v]=pos.get(e.target);svg.append(make('path',{d:`M ${x+230} ${y+15} C ${x+250} ${y+15} ${u-20} ${v+15} ${u} ${v+15}`,fill:'none',stroke:e.kind==='type_ref'?'#688fbe':'#3c876b','stroke-width':1.3,'marker-end':'url(#dagArrow)'}));}for(let c of cs){let[x,y]=pos.get(c.id),node=make('g',{transform:`translate(${x},${y})`,style:'cursor:pointer'}),root=c.members.includes(g.root);node.append(make('rect',{width:230,height:31,rx:5,fill:root?'#ddede1':'#f5f6f2',stroke:c.recursive?'#b57940':'#a8b9af'}));let label=make('text',{x:8,y:20,'font-size':11,fill:'#20352c'}),name=c.members[0];label.textContent=(name.length>32?'…'+name.slice(-31):name)+(c.members.length>1?' +'+(c.members.length-1):'');let title=make('title');title.textContent=c.members.join('\\n');node.append(label,title);node.onclick=()=>show(c.members[0]);svg.append(node);}}
function binders(bs){return bs.length?bs.map(b=>`${b.id} [${b.binder_mode}] ${b.binder_mode==='instance'?'':b.name+' : '}${b.type_text}`).join('\\n'):'无额外命题假设';}
async function show(name,fragment){try{let data=await get('/api/show',{name});let a=el('detail');a.replaceChildren();let h=document.createElement('h2');h.textContent=name;a.append(h);let t=data.triad;
let src=document.createElement('p');src.className='muted';src.textContent=data.declaration.source_path+' · '+(data.declaration.source_hash||'').slice(0,12);a.append(src);
if(t){box(a,t.target_text_status==='unavailable'?'声明（完整类型）':'目标',t.target_text_status==='unavailable'?data.declaration.type_text:t.target_text);let c=document.createElement('div');c.className='columns';a.append(c);box(c,'条件',binders(t.ordered_telescope.filter(b=>b.role==='condition')));box(c,'对象',binders(t.ordered_telescope.filter(b=>b.role==='object')));box(c,'证明细节',data.proof_source?.text||t.proof_skeleton?.expression_text||'', 'proof');}
if(fragment){let f=await get('/api/fragment',{id:fragment});box(a,'命中的证明片段',f.source);box(a,'入口状态',f.goals_before_text);box(a,'出口状态',f.goals_after_text);}
let g=await get('/api/graph',{name});graphBox(a,g); }catch(e){el('status').textContent=e.message;}}
function showPattern(p){let a=el('detail');a.replaceChildren();let h=document.createElement('h2');h.textContent=p.title;a.append(h);box(a,'条件',p.conditions);box(a,'对象',p.objects);box(a,'证明细节',p.proof_detail);box(a,'应用模板',p.application_template);}
el('form').onsubmit=async e=>{e.preventDefault();el('status').textContent='正在检索…';try{let d=await get('/api/search',{q:el('query').value,view:el('view').value});el('hits').replaceChildren();for(let lane of ['semantic','lexical']){let hs=Array.isArray(d[lane])?d[lane]:(d[lane]?.items||[]);if(!hs.length)continue;let h=document.createElement('h3');h.textContent=lane;el('hits').append(h);for(let hit of hs){let b=document.createElement('button');b.className='hit';b.textContent=hit.name+' · '+hit.view;b.onclick=()=>show(hit.name,hit.metadata?.fragment_id);el('hits').append(b);}}
let seen=new Set();for(let lane of ['semantic','lexical'])for(let hit of (d.patterns?.[lane]||[])){if(seen.has(hit.id))continue;seen.add(hit.id);let b=document.createElement('button');b.className='hit';b.textContent='模式 · '+hit.title;b.onclick=()=>showPattern(hit.pattern);el('hits').append(b);}
el('status').textContent=d.semantic_status?.status==='stale'?'语义索引待更新；当前显示关键词结果。':'检索结果需要结合类型、前提及 Lean 检查判断能否复用。';}catch(e){el('status').textContent=e.message;}};
const initial=new URLSearchParams(location.search);if(initial.get('name'))show(initial.get('name'));if(initial.get('q')){el('query').value=initial.get('q');el('form').requestSubmit();}
get('/api/stats').then(d=>{el('status').textContent=`${d.declarations} 个声明 · ${d.triads} 个三元组 · ${d.fragments} 个证明状态片段`;}).catch(e=>el('status').textContent=e.message);
</script></html>"""


def serve(args, store):
    from .cli import _client
    client = _client(args) if args.semantic else None
    if client:
        from .vectors import VectorIndex
        index = VectorIndex(args.data_dir)
    else:
        index = None

    class Handler(BaseHTTPRequestHandler):
        def log_message(self, *args):
            pass

        def do_GET(self):
            parsed = urlparse(self.path)
            values = parse_qs(parsed.query)
            q = lambda name, default="": values.get(name, [default])[0]
            try:
                if parsed.path == "/":
                    body = PAGE.encode()
                    self.send_response(200)
                    self.send_header("Content-Type", "text/html; charset=utf-8")
                    self.send_header("Content-Length", str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)
                    return
                current = store.snapshot_status(source_manifest(args.project_root))
                if current.get("stale") is not False:
                    raise ValueError("source index is stale; rebuild before querying")
                if parsed.path == "/api/search":
                    data = search(store, q("q"), limit=10, view=q("view") or None,
                                  vector_index=index, client=client)
                elif parsed.path == "/api/show":
                    data = {"declaration": store.get_decl(q("name")), "triad": store.get_triad(q("name")),
                            "proof_source": store.get_proof_text(q("name"))}
                elif parsed.path == "/api/fragment":
                    data = store.get_fragment(int(q("id")))
                elif parsed.path == "/api/graph":
                    data = store.dag(q("name"), depth=1, limit=60)
                elif parsed.path == "/api/stats":
                    data = store.stats()
                    data.pop("snapshot", None)
                elif parsed.path == "/api/patterns":
                    data = load_patterns()
                else:
                    self._json({"error": "route not found"}, 404)
                    return
                self._json(data)
            except (ValueError, RuntimeError, OSError) as exc:
                self._json({"error": str(exc)}, 400)

        def _json(self, value, status=200):
            body = json.dumps(value, ensure_ascii=False).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

    server = HTTPServer(("127.0.0.1", args.port), Handler)
    print(f"Proof Atlas: http://127.0.0.1:{args.port}", flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()
        if hasattr(client, "close"):
            client.close()
    return {"status": "stopped"}
