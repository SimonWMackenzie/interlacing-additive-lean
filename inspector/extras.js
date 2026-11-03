/* Companion-specific controls; the reference template owns graph/tracer/cards. */
window.ExplorerExtras = (() => {
  'use strict';
  let api, dialog, sourceSelect, sourceSearch, sourceCode, sourceTitle, currentModule, showExplanations=false, overviewHighlight=null;
  const $ = id => document.getElementById(id);
  const button = (text, action, cls='') => {const b=document.createElement('button');b.type='button';b.textContent=text;b.className=cls;b.addEventListener('click',action);return b;};
  const el = (tag, cls, text) => {const e=document.createElement(tag);e.className=cls||'';if(text!==undefined)e.textContent=text;return e;};
  const escape = s => String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;');
  const sourceCache=new Map();

  // Selected manuscript proof dependencies, independently reviewed against v44.
  // These grouped steps are NOT the cyclic compiler-recorded reference relation.
  const proofOverview={
    layerNames:['Starting ingredients','The first communication gap','Increase the gap','Keep the table small','Main conclusions'],
    nodes:[
      {id:'coloring',layer:0,column:0,span:3,title:'A hard graph-coloring problem',description:'Start with a graph whose colorability encodes satisfiability.',statements:['src:gap-colouring']},
      {id:'rank',layer:0,column:3,span:1,title:'Count protocols using rank',description:'Bound how many different protocol behaviors must survive sampling.',statements:['thm:rank-count'],track:'random'},
      {id:'arrays',layer:0,column:4,span:1,title:'An explicit list of arrays',description:'A separate construction for strict alternation.',statements:['yao:array-list'],track:'alternating'},
      {id:'encoding',layer:1,column:0,span:3,title:'Encode the graph in a communication table',description:'A coloring gives a short protocol. Without a coloring, every protocol needs more communication.',statements:['src:upper','src:near-full']},
      {id:'sampling',layer:1,column:3,span:1,title:'Sample rows and columns',description:'Preserve the lower bound in a smaller table.',statements:['thm:compression'],track:'random'},
      {id:'amplification',layer:2,column:0,span:3,title:'Interlace repeatedly to enlarge the gap',description:'The one-round amplifier and its iteration turn the initial separation into any required fixed gap.',statements:['thm:amplifier','prop:iteration']},
      {id:'alternating',layer:2,column:4,span:1,title:'Encode hard hypergraph coloring',description:'Apply the array construction to obtain a gap for alternating protocols.',statements:['yao:source','yao:lift'],track:'alternating'},
      {id:'explicit',layer:3,column:0,span:2,title:'Construct the table deterministically',description:'Explicit input lists keep the reduction polynomial for every fixed gap.',statements:['det:reduction']},
      {id:'sampled',layer:3,column:2,span:2,title:'Sample once after amplification',description:'A smaller randomized reduction gives a stronger relation between error and running time.',statements:['thm:uniform-reduction'],track:'random'},
      {id:'fixed',layer:4,column:0,span:1,title:'Unrestricted protocols',description:'NP-hardness for every fixed additive error.',statements:['intro:deterministic'],terminal:true},
      {id:'deterministic-time',layer:4,column:1,span:1,title:'Deterministic running time',description:'A quantitative implication from estimation to faster 3-SAT.',statements:['det:time'],terminal:true},
      {id:'general-time',layer:4,column:2,span:1,title:'The general running-time tradeoff',description:'Convert an approximation algorithm into a 3-SAT algorithm.',statements:['thm:time-tradeoff'],terminal:true},
      {id:'randomized-time',layer:4,column:3,span:1,title:'Randomized running time',description:'The sharper quantitative implication from the sampled construction.',statements:['thm:quantitative'],terminal:true,track:'random'},
      {id:'strict',layer:4,column:4,span:1,title:'Strict alternation',description:'Fixed additive hardness, including Yao’s final-receiver convention.',statements:['yao:main','yao:bpp'],terminal:true,track:'alternating',comparison:'yao:comparison'}
    ],
    edges:[['coloring','encoding'],['encoding','amplification'],['rank','sampling'],['arrays','alternating'],
      ['amplification','explicit'],['amplification','sampled'],['sampling','sampled'],
      ['explicit','fixed'],['explicit','deterministic-time'],['explicit','general-time'],
      ['sampled','general-time'],['sampled','randomized-time'],['alternating','strict']]
  };
  const endpointIds=new Set(proofOverview.nodes.filter(n=>n.terminal).flatMap(n=>n.statements));
  const numberOf=n=>n.paper?n.paper.env[0].toUpperCase()+n.paper.env.slice(1)+' '+n.paper.num:'Construction';
  function referenceGroups(data,view,route,id){
    const visible=new Set(data.nodes.filter(n=>view==='full'||n.spine||n.id===id).map(n=>n.id));
    const edges=(route==='paper'?data.edgesPaperFull:data.edgesFull).filter(([a,b])=>a!==b&&visible.has(a)&&visible.has(b));
    const incoming=new Set(edges.filter(e=>e[1]===id).map(e=>e[0]));
    const outgoing=new Set(edges.filter(e=>e[0]===id).map(e=>e[1]));
    return {incoming:data.nodes.filter(n=>incoming.has(n.id)),outgoing:data.nodes.filter(n=>outgoing.has(n.id)),mutual:new Set([...incoming].filter(k=>outgoing.has(k)))};
  }
  function statementLink(id,short=false,paper=false){
    const n=api.DATA.nodes.find(n=>n.id===id);if(!n)throw Error('Unknown overview statement: '+id);
    const label=short?numberOf(n).replace('Theorem','Thm.').replace('Proposition','Prop.').replace('Corollary','Cor.').replace('Lemma','Lem.'):numberOf(n)+' · '+n.title;
    const b=button(label,()=>paper?api.openTrace(id):api.select(id,true),'statement-link');
    b.dataset.statement=id;b.title=(paper?'Open paper and Lean proof: ':'Show recorded references: ')+n.title;return b;
  }
  function traceOverview(id){
    overviewHighlight=id;
    const board=$('proof-board');if(!board)return;
    const keep=new Set([id]);
    function visit(start,reverse){for(const [a,b] of proofOverview.edges){const from=reverse?b:a,to=reverse?a:b;if(from===start&&!keep.has(to)){keep.add(to);visit(to,reverse);}}}
    visit(id,true);visit(id,false);
    board.querySelectorAll('[data-proof-node]').forEach(e=>{e.classList.toggle('map-dim',!!id&&!keep.has(e.dataset.proofNode));e.classList.toggle('map-selected',e.dataset.proofNode===id);});
    board.querySelectorAll('[data-proof-edge]').forEach(e=>e.classList.toggle('map-dim',!!id&&!(keep.has(e.dataset.from)&&keep.has(e.dataset.to))));
  }
  function drawProofArrows(){
    const board=$('proof-board'),svg=$('proof-arrows');if(!board||!svg)return;
    const origin=board.getBoundingClientRect();if(!origin.width)return;
    svg.setAttribute('viewBox',`0 0 ${board.offsetWidth} ${board.offsetHeight}`);
    svg.setAttribute('width',board.offsetWidth);svg.setAttribute('height',board.offsetHeight);
    svg.innerHTML='<defs><marker id="proof-arrow-tip" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M 0 0 L 10 5 L 0 10 z" fill="#94b9cf"/></marker></defs>';
    proofOverview.edges.forEach(([from,to])=>{
      const a=board.querySelector(`[data-proof-node="${from}"]`).getBoundingClientRect(),b=board.querySelector(`[data-proof-node="${to}"]`).getBoundingClientRect();
      const outs=proofOverview.edges.filter(e=>e[0]===from).map(e=>e[1]),ins=proofOverview.edges.filter(e=>e[1]===to).map(e=>e[0]);
      const sx=board.offsetWidth/origin.width,sy=board.offsetHeight/origin.height;
      const x1=(a.left-origin.left+a.width*(outs.indexOf(to)+1)/(outs.length+1))*sx,y1=(a.bottom-origin.top)*sy+2;
      const x2=(b.left-origin.left+b.width*(ins.indexOf(from)+1)/(ins.length+1))*sx,y2=(b.top-origin.top)*sy-4;
      // Every edge moves downward; skipped layers use their empty column.
      const mid=(y1+y2)/2,p=document.createElementNS('http://www.w3.org/2000/svg','path');
      // Separate curved branches do not overlap into a misleading junction.
      p.setAttribute('d',`M ${x1} ${y1} C ${x1} ${mid} ${x2} ${mid} ${x2} ${y2}`);
      p.setAttribute('marker-end','url(#proof-arrow-tip)');p.dataset.proofEdge=from+'→'+to;p.dataset.from=from;p.dataset.to=to;
      svg.append(p);
    });
    traceOverview(overviewHighlight);
  }
  function renderOverview(host){
    const intro=el('div','map-heading');
    intro.append(el('div','map-kicker','PROOF DEPENDENCIES · SELECTED STATEMENTS'),el('h2','','Follow the proof down to its main conclusions'),
      el('p','map-intro','Arrows lead downward from proof ingredients to the final results. Select a heading to highlight its path, or a theorem number to open the paper and Lean proof.'));
    const actions=el('div','map-actions');
    const explain=button(showExplanations?'Hide explanations':'Show explanations',()=>{showExplanations=!showExplanations;board.classList.toggle('with-explanations',showExplanations);explain.textContent=showExplanations?'Hide explanations':'Show explanations';explain.setAttribute('aria-pressed',String(showExplanations));requestAnimationFrame(drawProofArrows);});explain.setAttribute('aria-pressed',String(showExplanations));
    actions.append(explain,button('Jump to conclusions ↓',()=>board.querySelector('.final-layer').scrollIntoView({block:'end'})),button('Reset highlighting',()=>traceOverview(null)));intro.append(actions,el('p','map-small-screen','Scroll sideways across the diagram. Text stays at a readable size.'));host.append(intro);
    const scroll=el('div','proof-scroll');scroll.tabIndex=0;scroll.setAttribute('aria-label','Layered proof diagram. Scroll horizontally on a narrow screen.');
    const board=el('div','proof-board');board.id='proof-board';board.classList.toggle('with-explanations',showExplanations);
    const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');svg.id='proof-arrows';svg.setAttribute('aria-hidden','true');board.append(svg);
    proofOverview.layerNames.forEach((name,layer)=>{
      const row=el('section','proof-layer'+(layer===4?' final-layer':''));row.dataset.layer=layer;row.setAttribute('aria-label',name);
      row.append(el('h3','layer-label',(layer+1)+'  '+name));
      const grid=el('div','proof-layer-grid');
      proofOverview.nodes.filter(n=>n.layer===layer).forEach(n=>{
        const card=el('article','proof-card'+(n.terminal?' terminal':'')+(n.track?' track-'+n.track:''));card.dataset.proofNode=n.id;card.style.gridColumn=`${n.column+1} / span ${n.span}`;
        if(n.terminal)card.append(el('div','terminal-label','FINAL RESULT'));
        const title=button(n.title,()=>traceOverview(n.id),'proof-node-title');title.setAttribute('aria-label','Highlight proof path: '+n.title);card.append(title,el('p','',n.description));
        const links=el('div','proof-node-links');n.statements.forEach(id=>links.append(statementLink(id,true,true)));card.append(links);
        if(n.comparison){const relation=el('div','output-convention');relation.append(el('span','','Theorem 1.2 → Corollary 1.3, using '),statementLink(n.comparison,true,true));card.append(relation);}
        grid.append(card);
      });
      row.append(grid);board.append(row);
    });
    scroll.append(board);host.append(scroll,el('p','map-caption','This overview follows the manuscript’s proofs; intermediate lemmas are omitted. The strict-alternation argument is separate from interlacing. Recorded Lean references are available through “Statement references” and search.'));
    requestAnimationFrame(drawProofArrows);
  }
  function renderReferences(host,state){
    const n=api.DATA.nodes.find(n=>n.id===state.statement);if(!n){renderOverview(host);return;}
    const groups=referenceGroups(api.DATA,state.view,state.route,n.id);
    host.append(el('div','map-kicker','RECORDED REFERENCES'),el('h2','',numberOf(n)+' · '+n.title),
      el('p','map-intro',state.route==='paper'?'Cross-references recorded in the manuscript statements. Proof citations in surrounding prose may not appear here.':'Compiler-recorded source references, including references through helper declarations. These can be mutual; they do not define a proof order.'));
    const columns=el('div','reference-columns');
    function side(title,nodes,cls){
      const box=el('section','reference-column '+cls);box.append(el('h3','',title+' ('+nodes.length+')'));
      const list=el('div','reference-list');nodes.forEach(item=>{const link=statementLink(item.id);if(endpointIds.has(item.id))link.append(el('small','result-badge','Main result'));if(groups.mutual.has(item.id))link.append(el('small','mutual-badge','Referenced in both directions'));list.append(link);});
      if(!nodes.length)list.append(el('p','reference-empty','No references recorded in this direction and scope.'));
      box.append(list);return box;
    }
    const center=el('section','reference-selected');center.append(el('div','map-kicker',endpointIds.has(n.id)?'SELECTED MAIN RESULT':'SELECTED STATEMENT'),el('h3','',numberOf(n)),el('p','',n.title));
    if(n.paper)center.append(button('Open paper & Lean proof',()=>api.openTrace(n.id),'open-proof'));
    else{
      center.append(el('p','reference-direction','This construction has no single highlighted statement in the PDF. Open its linked Lean declarations below.'));
      (n.leanDeclarations||[]).forEach(d=>center.append(button(d.name,()=>openSource(d.file,d.line),'open-proof construction-source')));
    }
    center.append(el('p','reference-direction','“Referenced items” lists what this statement refers to. “Referenced by” lists the items that refer to this statement.'),button('← Back to proof overview',()=>api.setGraphFocus(false),'overview-back'));
    columns.append(side('Referenced items →',groups.incoming,'reference-inputs'),center,side('→ Referenced by',groups.outgoing,'reference-users'));host.append(columns);
  }
  function renderReadableGraph(model){
    const host=$('readable-map');if(!host)return;
    const oldMode=host.dataset.mode,mode=model.focused?'references':'overview',top=host.scrollTop;
    document.body.classList.toggle('results-overview',!model.focused);
    host.replaceChildren();host.dataset.mode=mode;
    if(model.focused)renderReferences(host,api.navigationState());else renderOverview(host);
    host.scrollTop=mode===oldMode?top:0;
  }

  // The projected reference map can contain cycles: it is not a proof-order DAG.
  // Work from the selected route's actual edges, never another route's coordinates.
  function graphModel(data, view, route, selected) {
    let nodes=data.nodes.filter(n=>view==='full'||n.spine);
    if(route==='paper')nodes=nodes.filter(n=>n.paper||(n.paperDeps||[]).length||(n.paperDependents||[]).length||n.id===selected);
    const ids=new Set(nodes.map(n=>n.id));
    let edges=(route==='paper'?data.edgesPaperFull:data.edgesFull).filter(([a,b])=>a!==b&&ids.has(a)&&ids.has(b));
    const positions={}, width=218, stepX=300, stepY=68;
    if(selected&&ids.has(selected)){
      edges=edges.filter(([a,b])=>a===selected||b===selected);
      const incoming=new Set(edges.filter(e=>e[1]===selected).map(e=>e[0]));
      const outgoing=new Set(edges.filter(e=>e[0]===selected).map(e=>e[1]));
      const left=nodes.filter(n=>incoming.has(n.id));
      const right=nodes.filter(n=>outgoing.has(n.id)&&!incoming.has(n.id));
      nodes=nodes.filter(n=>n.id===selected||incoming.has(n.id)||outgoing.has(n.id));
      const rows=Math.max(left.length,right.length,1), middle=46+(rows-1)*stepY/2;
      positions[selected]={x:46+stepX,y:middle};
      [left,right].forEach((group,column)=>group.forEach((n,i)=>{positions[n.id]={x:46+(column?2:0)*stepX,y:middle+(i-(group.length-1)/2)*stepY};}));
    }else{
      // A stable grid is deliberate. Source references include mutual references,
      // so an invented topological order would suggest a false proof hierarchy.
      const columns=Math.max(1,Math.ceil(Math.sqrt(nodes.length*1.45)));
      nodes.forEach((n,i)=>{positions[n.id]={x:46+(i%columns)*stepX,y:46+Math.floor(i/columns)*stepY};});
    }
    if(selected&&nodes.length){const shift=Math.min(...nodes.map(n=>positions[n.id].x))-46;nodes.forEach(n=>{positions[n.id].x-=shift;});}
    const right=Math.max(...nodes.map(n=>positions[n.id].x+width),264);
    const bottom=Math.max(...nodes.map(n=>positions[n.id].y+42),160);
    return {nodes,edges,positions,width:right+46,height:bottom+46,focused:!!(selected&&ids.has(selected))};
  }
  function graphPath(a,b,reverse=false){
    const w=218,h=42,offset=reverse?5:0;
    let x1,x2,y1=a.y+h/2-offset,y2=b.y+h/2-offset;
    if(b.x>a.x){x1=a.x+w;x2=b.x;}
    else if(b.x<a.x){x1=a.x;x2=b.x+w;y1+=2*offset;y2+=2*offset;}
    else {x1=a.x+w;x2=b.x+w;const bend=x1+55;return `M${x1} ${y1} C${bend} ${y1} ${bend} ${y2} ${x2} ${y2}`;}
    const middle=(x1+x2)/2;
    return `M${x1} ${y1} C${middle} ${y1} ${middle} ${y2} ${x2} ${y2}`;
  }
  function graphFit(width,height,viewportWidth,viewportHeight,padding={left:20,right:20,top:50,bottom:90}){
    if(viewportWidth<=0||viewportHeight<=0)return null;
    const availableWidth=Math.max(1,viewportWidth-padding.left-padding.right);
    const availableHeight=Math.max(1,viewportHeight-padding.top-padding.bottom);
    const scale=Math.min(1.1,availableWidth/Math.max(width,1),availableHeight/Math.max(height,1));
    return {scale,tx:padding.left+(availableWidth-width*scale)/2,ty:padding.top+(availableHeight-height*scale)/2};
  }
  function graphChanged(model){
    if(!$('graph-status'))return;
    const state=api.navigationState();
    const selected=api.DATA.nodes.find(n=>n.id===state.statement);
    $('graph-status').textContent=model.focused?'Recorded references · full titles, no zooming needed':'Top → bottom · five final result cards';
    $('graph-focus').classList.toggle('on',model.focused);
    $('graph-focus').setAttribute('aria-pressed',String(model.focused));
    $('graph-overview').classList.toggle('on',!model.focused);
    $('graph-overview').setAttribute('aria-pressed',String(!model.focused));
    ['m-spine','m-full','r-lean','r-paper'].forEach(id=>$(id).setAttribute('aria-pressed',String($(id).classList.contains('on'))));
    renderReadableGraph(model);
  }
  function encodeNavigation(state){
    const hash=new URLSearchParams();
    if(state.statement)hash.set('statement',state.statement);
    hash.set('view',state.screen);hash.set('scope',state.view);hash.set('route',state.route);hash.set('focus',state.focus?'1':'0');
    return '#'+hash.toString();
  }
  function decodeNavigation(hash,data){
    const p=new URLSearchParams(hash.replace(/^#/,''));
    const id=p.get('statement');
    const screen=p.get('view')==='paper'||(!p.has('view')&&p.has('statement'))?'paper':'graph';
    return {statement:data.nodes.some(n=>n.id===id)?id:(screen==='paper'?(data.paperIndex[0]?.id||null):null),screen,view:p.get('scope')==='full'?'full':'spine',route:p.get('route')==='paper'?'paper':'lean',focus:p.get('focus')!=='0'};
  }
  let restoring=false, navigationPending=false;
  function navigationChanged(){
    if(!api||restoring||navigationPending)return;
    navigationPending=true;
    queueMicrotask(()=>{navigationPending=false;if(restoring)return;const hash=encodeNavigation(api.navigationState());if(location.hash!==hash)history.pushState(null,'',hash);});
  }
  function restoreNavigation(){
    restoring=true;
    api.restoreNavigation(decodeNavigation(location.hash,api.DATA));
    requestAnimationFrame(()=>requestAnimationFrame(()=>{restoring=false;history.replaceState(null,'',encodeNavigation(api.navigationState()));}));
  }
  function renderGraphSearch(hits,query){
    const results=$('graph-search-results');if(!results)return;
    results.replaceChildren();results.hidden=!query;
    $('q').setAttribute('aria-expanded',String(!!query));
    if(!query)return;
    results.append(el('p','search-count',hits.length?hits.length+' matching items'+(hits.length>12?' · first 12 shown':''):'No matching items'));
    hits.slice(0,12).forEach(n=>{
      const item=button(n.title||n.id,()=>{api.select(n.id,true);results.hidden=true;});
      const where=n.paper?n.paper.env+' '+n.paper.num+' · PDF page '+n.paper.page:'Construction entry';
      item.append(el('small','',where));results.append(item);
    });
  }
  // A release's asset hashes prevent a fresh page from reusing an older
  // browser-cached PDF, rendered page, proof index, or Lean source module.
  const assetUrl = (path, digest) => {
    const hash=digest || window.InspectorAssetHashes[path];
    if(!/^[0-9a-f]{64}$/.test(hash || ''))throw Error('Missing asset version: '+path);
    return path+'?v='+hash;
  };
  const readerScope = () => api.DATA.meta.counts.pending === 0
    ? 'Explore the paper alongside its Lean proofs, including the running-time results. Cited source reductions remain explicit hypotheses.'
    : api.PAYLOAD.verification.scope;
  function decorateTokens(root){if(!root?.querySelectorAll)return;root.querySelectorAll('[data-t],[data-k],[data-push],[data-push0],.gnode,.gdt').forEach(x=>{x.tabIndex=0;x.setAttribute('role','button');x.setAttribute('aria-label',x.matches('.gnode')?'Open statement in graph':x.matches('.gdt')?'Show source documentation':'Explain '+x.textContent);});}
  async function openSource(module, line=1) {
    const info=api.PAYLOAD.modules[module];
    if(!info)return;
    if(!Array.from(sourceSelect.options).some(o=>o.value===module)){sourceSearch.value='';moduleList();}
    currentModule=module;if(!dialog.open)dialog.showModal();dialog.append($('gwrap'),$('ghover'));sourceSelect.value=module;
    sourceTitle.textContent=module+' · '+info.lines+' lines';
    sourceCode.textContent='Loading exact source…';
    $('source-copy').textContent='Copy source';$('source-download').href=assetUrl(info.url,info.sha256);
    try {
      let text=sourceCache.get(module);
      if(text===undefined){const r=await fetch(assetUrl(info.url,info.sha256));if(!r.ok)throw Error('HTTP '+r.status);text=await r.text();sourceCache.set(module,text);}
      if(currentModule!==module)return;
      // Line by line avoids accidentally putting markup inside lexical comments across lines.
      sourceCode.innerHTML=text.split('\n').map((s,i)=>'<span class="source-row'+(i+1===Number(line)?' chosen-line':'')+'" id="source-line-'+(i+1)+'"><span class="line-number">'+(i+1)+'</span><span>'+api.hlLean(s)+'</span></span>').join('');
      decorateTokens(sourceCode);
      sourceCode.querySelector('.chosen-line')?.scrollIntoView({block:'center'});
      $('source-origin').textContent=info.file+' · SHA-256 '+info.sha256;
      $('source-download').href=assetUrl(info.url,info.sha256);
    } catch(e) {if(currentModule===module)sourceCode.textContent='Source could not be loaded: '+e.message;}
  }
  function moduleList(filter='') {
    const selected=sourceSelect.value;sourceSelect.replaceChildren();
    const names=Object.keys(api.PAYLOAD.modules).filter(n=>n.toLowerCase().includes(filter.toLowerCase()));
    for(const name of names){const o=el('option','',name);o.value=name;sourceSelect.append(o);}
    if(names.includes(selected))sourceSelect.value=selected;
    $('source-result-count').textContent=names.length+' modules';
  }
  function createSourceViewer() {
    dialog=el('dialog','source-dialog');dialog.setAttribute('aria-labelledby','source-title');
    dialog.innerHTML='<header><h2 id="source-title">Lean source</h2><button id="source-close" aria-label="Close source viewer">Close ✕</button></header><div class="source-controls"><label>Find module <input id="source-search" type="search" placeholder="Search all source modules"></label><span id="source-result-count"></span><label class="module-select">Module <select id="source-select"></select></label><a id="source-download" download>Download module</a><button id="source-copy">Copy source</button></div><p id="source-origin"></p><pre id="source-code" tabindex="0"></pre>';
    document.body.append(dialog);sourceSelect=$('source-select');sourceSearch=$('source-search');sourceCode=$('source-code');sourceCode.className='code';sourceTitle=$('source-title');
    const lookup=el('div','declaration-search');
    lookup.innerHTML='<label>Find declaration <input id="declaration-query" type="search" placeholder="Name or part of a Lean declaration"></label><label>Matches <select id="declaration-results" aria-label="Matching Lean declarations"><option value="">Type a name to search</option></select></label>';
    $('source-origin').before(lookup);
    const declarationNames=Object.keys(api.PAYLOAD.glossary.decls);
    $('declaration-query').addEventListener('input',()=>{
      const query=$('declaration-query').value.trim().toLowerCase(),results=$('declaration-results');results.replaceChildren();
      const hits=query.length>=2?declarationNames.filter(n=>n.toLowerCase().includes(query)):[];
      const hint=el('option','',query.length<2?'Enter at least two characters':hits.length+' matches'+(hits.length>80?' · showing first 80':''));hint.value='';results.append(hint);
      for(const name of hits.slice(0,80)){const o=el('option','',name);o.value=name;results.append(o);}
    });
    $('declaration-results').addEventListener('change',()=>{const d=api.PAYLOAD.glossary.decls[$('declaration-results').value];if(d)openSource(d.file,d.line);});
    moduleList();sourceSearch.addEventListener('input',()=>moduleList(sourceSearch.value));
    sourceSelect.addEventListener('change',()=>openSource(sourceSelect.value));
    $('source-close').addEventListener('click',()=>dialog.close());
    dialog.addEventListener('close',()=>{document.body.append($('gwrap'),$('ghover'));});
    $('source-copy').addEventListener('click',async()=>{try{await navigator.clipboard.writeText(sourceCache.get(currentModule)||'');$('source-copy').textContent='Copied';}catch{$('source-copy').textContent='Select source to copy';}});
    // Native dialog keeps keyboard focus bounded and supports Escape.
    document.addEventListener('click',e=>{const b=e.target.closest('[data-module]');if(b){e.preventDefault();openSource(b.dataset.module,b.dataset.line||1);}});
    document.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches('[data-t],[data-k],[data-push],[data-push0],.gnode,.gdt')){e.preventDefault();e.target.click();}});
  }
  function openVerification(){
    let v=$('verification-dialog');
    if(!v){
      v=el('dialog','verification-dialog');v.id='verification-dialog';v.setAttribute('aria-labelledby','verification-title');
      const head=el('header');const title=el('h2','','Verification and assumptions');title.id='verification-title';head.append(title,button('Close ✕',()=>v.close()));v.append(head);
      const body=el('div','verification-body');v.append(body);const data=api.PAYLOAD.verification;
      body.append(el('p','',readerScope()||'Read the linked verification record for this source snapshot.'));
      if(data.build){
        body.append(el('h3','','Recorded build'));
        if(data.build.canonical_checked_build_complete===true)body.append(el('p','','The recorded canonical build and axiom audits passed for the checked Lean source release. Correspondence with the displayed manuscript is recorded separately for each item.'));
        if(data.build.public_package_replay_complete===false)body.append(el('p','','This release does not claim a fresh rebuild of the entire development. Unchanged inherited sources reuse the earlier verified build.'));
        if(data.build.public_package_replay_complete===true)body.append(el('p','','A separate recorded replay rebuilt the local project sources in a fresh checkout.'));
        body.append(el('p','source-scope','Proof-source commit: '+data.build.code_commit));
        if(data.build.checked_build_receipt_url){const record=el('a','','Read the canonical build record');record.href=data.build.checked_build_receipt_url;record.target='_blank';record.rel='noopener';body.append(record);}
      }
      body.append(el('h3','','What the colors mean'));
      const list=el('ul');for(const text of ['Checked correspondence: the recorded review links this manuscript item to its Lean proof.','Definition: notation or a construction represented in the formal development.','External input: an assumption or cited result used at the stated boundary.','Pending: correspondence with this manuscript is not yet complete; any linked declaration is a candidate.'])list.append(el('li','',text));body.append(list);
      body.append(el('h3','','Lean axioms recorded in the audit'),el('p','',Array.isArray(data.axioms)?data.axioms.join(' · '):'Read the linked audit.'));
      body.append(el('p','','Mathematical source hypotheses can also appear as explicit parameters of a theorem. An axiom list alone does not show that those hypotheses have been independently proved.'));
      if(data.assumptions){body.append(el('h3','','External mathematical inputs'));const ul=el('ul');for(const x of data.assumptions)ul.append(el('li','',typeof x==='string'?x:JSON.stringify(x)));body.append(ul);}
      body.append(el('h3','','Source correspondence and graphs'),el('p','','The paper highlights delimit statements, not complete proofs. Lean arrows show compiler-recorded references projected through helper declarations. The paper route shows recorded cross-references. These are different forms of evidence, and neither is a browser execution of Lean.'));
      body.append(el('p','',api.DATA.meta.nodes+' manuscript and construction items · '+Object.keys(api.PAYLOAD.modules).length+' source modules in the recorded development.'));
      const link=el('a','','Download verification record');link.href='verification.json';link.download='verification.json';body.append(link);
      const coordinate=el('a','','Statement-coordinate check');coordinate.href='coordinate-verification.json';coordinate.target='_blank';coordinate.rel='noopener';body.append(coordinate);
      document.body.append(v);
    }
    v.showModal();
  }
  function renderSources(n, hostId) {
    const host=$(hostId);let box=host.parentElement.querySelector('.linked-sources');
    if(box)box.remove();box=el('div','linked-sources');host.after(box);
    const links=n.leanDeclarations||[];
    if(links.length>1){
      const label=el('label','','Linked declarations ');const choose=el('select');choose.setAttribute('aria-label','Choose linked Lean declaration');
      for(const d of links){const option=el('option','',d.name);option.value=d.name;choose.append(option);}
      label.append(choose);box.append(label);
      choose.addEventListener('change',()=>{const d=links.find(x=>x.name===choose.value);host.classList.remove('hasgut');host.innerHTML='<pre class="code">'+api.hlLean(d.code)+'</pre>';decorateTokens(host);detail.replaceChildren();addSourceButtons(detail,d,n.scope_note);});
    }
    const detail=el('div','linked-detail');box.append(detail);
    if(n.proof_role)box.append(el('p','proof-role',n.proof_role));
    if(links[0])addSourceButtons(detail,links[0],n.scope_note);
    if(n.status==='pending')box.prepend(el('p','pending-note',links.length?'Candidate correspondence. This link has not yet been checked against this manuscript.':'Correspondence is not yet complete. No Lean declaration is currently linked to this manuscript statement.'));
    decorateTokens(host);
    decorateTokens($(hostId==='td-code'?'td-chips':'i-chips'));
  }
  function addSourceButtons(box,d,scope=''){
    box.append(button('Full source · line '+d.line+' →',()=>openSource(d.file,d.line),'source-link'));
    box.append(button('Copy declaration',async(e)=>{const b=e.currentTarget;try{await navigator.clipboard.writeText(d.code);b.textContent='Copied';}catch{b.textContent='Select text to copy';}},'source-link'));
    if(d.explanation&&!scope.includes(d.explanation))box.append(el('p','source-scope',d.explanation));
  }
  function init(a){
    api=a;createSourceViewer();
    $('td-graph').textContent='Open statement references →';
    const graphControls=el('div','graph-controls');
    const focus=button('Statement references',()=>api.setGraphFocus(true));focus.id='graph-focus';focus.title='Show the selected statement and its immediate recorded references';
    const overview=button('Proof overview',()=>api.setGraphFocus(false));overview.id='graph-overview';overview.title='Read the layered proof diagram, ending with the main results';
    graphControls.append(overview,focus);
    const status=el('span','', '');status.id='graph-status';status.setAttribute('role','status');graphControls.append(status);
    document.querySelector('.graphwrap').prepend(graphControls);
    const readable=el('div','readable-map');readable.id='readable-map';readable.tabIndex=0;document.querySelector('.graphwrap').append(readable);
    new ResizeObserver(()=>requestAnimationFrame(drawProofArrows)).observe(readable);
    const graphZoomOut=button('−',()=>api.zoomGraph(1/1.25));graphZoomOut.setAttribute('aria-label','Zoom reference graph out');
    const graphZoomIn=button('+',()=>api.zoomGraph(1.25));graphZoomIn.setAttribute('aria-label','Zoom reference graph in');
    document.querySelector('.fab').prepend(graphZoomOut,graphZoomIn);
    const explanation=el('p','graph-explanation','Arrows point from a referenced item to the item that uses it. Mutual references are possible; this is a reference map, not a proof-order graph.');
    document.querySelector('.graphwrap').append(explanation);
    $('graph').setAttribute('aria-label','Recorded references between manuscript statements');
    $('m-spine').textContent='Paper statements';$('m-full').textContent='All entries';$('m-full').title='Include the additional construction entries';
    document.querySelector('.stats').title='Totals for all '+api.DATA.nodes.length+' paper and construction entries; shown counts the current graph';
    $('q').placeholder='Find a statement or PDF page';
    $('q').setAttribute('aria-label','Find a graph statement');$('pq').setAttribute('aria-label','Filter paper statements');
    const searchResults=el('div','graph-search-results');searchResults.id='graph-search-results';searchResults.hidden=true;searchResults.setAttribute('aria-label','Graph search results');
    $('q').parentElement.append(searchResults);$('q').setAttribute('aria-controls',searchResults.id);$('q').setAttribute('aria-expanded','false');
    const clearSearch=button('×',()=>{$('q').value='';$('q').dispatchEvent(new Event('input'));$('q').focus();});clearSearch.setAttribute('aria-label','Clear graph search');$('q').after(clearSearch);
    $('q').parentElement.addEventListener('keydown',event=>{
      const items=[...searchResults.querySelectorAll('button')],current=items.indexOf(document.activeElement);
      if(event.key==='ArrowDown'&&items.length){event.preventDefault();items[(current+1)%items.length].focus();}
      if(event.key==='ArrowUp'&&items.length){event.preventDefault();items[(current-1+items.length)%items.length].focus();}
      if(event.key==='Escape'&&!searchResults.hidden){event.preventDefault();event.stopPropagation();$('q').value='';$('q').dispatchEvent(new Event('input'));$('q').focus();}
    });
    document.addEventListener('click',event=>{if(!$('q').parentElement.contains(event.target)){searchResults.hidden=true;$('q').setAttribute('aria-expanded','false');}});
    document.querySelector('.modes').setAttribute('role','group');
    new MutationObserver(records=>records.forEach(r=>r.addedNodes.forEach(node=>decorateTokens(node)))).observe($('gwrap'),{childList:true});
    const pageNote=el('span','','Page numbers include the title page.');
    pageNote.id='page-number-note';pageNote.title='All page links and filters use the PDF page number, counting the title page; the printed footer is one lower.';
    document.querySelector('.sheet-head .t').append(pageNote);
    $('pq').title=pageNote.title;$('q').title=pageNote.title;
    $('scope-note').textContent=readerScope()||'Read each item’s correspondence status and the recorded verification scope.';
    $('axiom-footprint').textContent='Recorded axiom audit: '+(Array.isArray(api.PAYLOAD.verification.axioms)?api.PAYLOAD.verification.axioms.join(' · '):'see verification record');
    $('s-proved').textContent=api.DATA.meta.counts.proved;
    $('s-reused').textContent=api.DATA.meta.counts.reused;
    $('s-axioms').textContent=api.DATA.meta.counts.axioms;
    $('s-pending').textContent=api.DATA.meta.counts.pending;
    $('f-count').textContent=api.DATA.nodes.length;
    const sourceButton=button('Lean source',()=>openSource(Object.keys(api.PAYLOAD.modules)[0]));sourceButton.id='browse-source';
    document.querySelector('.modes').append(sourceButton);
    const paperLink=el('a','paper-download','Paper PDF ↓');paperLink.href=assetUrl('paper.pdf');paperLink.target='_blank';paperLink.rel='noopener';document.querySelector('.modes').append(paperLink);
    const downloads=button('Lean code ↓',()=>$('dl-lean').click(),'trace-download');document.querySelector('.sheet-head').insertBefore(downloads,$('o-close'));
    const controls=el('div','proof-shortcuts');controls.setAttribute('aria-label','Proof shortcuts');
    [...endpointIds].forEach(id=>{const n=api.DATA.nodes.find(n=>n.id===id);const b=button(numberOf(n),()=>api.openTrace(id));b.title=n.title;controls.append(b);});
    document.querySelector('#app header').after(controls);
    document.getElementById('r-lean').title='Compiler-recorded source references projected through helper declarations; not kernel proof-term dependencies';
    document.getElementById('r-paper').title='Cross-references in the recorded paper statements; incomplete as a proof dependency graph';
    // Keep correspondence provenance one click away in both views.
    const provenance=button('Verification and assumptions',openVerification,'verification-link');document.querySelector('.sheet-head').insertBefore(provenance,$('o-close'));
    document.querySelector('footer .axfoot').addEventListener('click',e=>{e.preventDefault();openVerification();});
    // The source viewer is above the paper overlay; definition windows must remain above it.
    const oldOpen=api.openWin;api.openWin=(...args)=>oldOpen(...args);
  }
  function ready(){
    $('load-progress').hidden=true;
    restoreNavigation();
    window.addEventListener('popstate',restoreNavigation);
    window.addEventListener('hashchange',()=>{if(!restoring)restoreNavigation();});
  }
  return {proofOverview,referenceGroups,init,ready,renderSources,openSource,assetUrl,graphModel,graphPath,graphFit,graphChanged,renderGraphSearch,navigationChanged,encodeNavigation,decodeNavigation};
})();
