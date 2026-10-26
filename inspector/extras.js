/* Companion-specific controls; the reference template owns graph/tracer/cards. */
window.ExplorerExtras = (() => {
  'use strict';
  let api, dialog, sourceSelect, sourceSearch, sourceCode, sourceTitle, currentModule;
  const $ = id => document.getElementById(id);
  const button = (text, action, cls='') => {const b=document.createElement('button');b.type='button';b.textContent=text;b.className=cls;b.addEventListener('click',action);return b;};
  const el = (tag, cls, text) => {const e=document.createElement(tag);e.className=cls||'';if(text!==undefined)e.textContent=text;return e;};
  const escape = s => String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;');
  const sourceCache=new Map();
  function decorateTokens(root){if(!root?.querySelectorAll)return;root.querySelectorAll('[data-t],[data-k],[data-push],[data-push0],.gnode,.gdt').forEach(x=>{x.tabIndex=0;x.setAttribute('role','button');x.setAttribute('aria-label',x.matches('.gnode')?'Open statement in graph':x.matches('.gdt')?'Show source documentation':'Explain '+x.textContent);});}
  async function openSource(module, line=1) {
    const info=api.PAYLOAD.modules[module];
    if(!info)return;
    if(!Array.from(sourceSelect.options).some(o=>o.value===module)){sourceSearch.value='';moduleList();}
    currentModule=module;if(!dialog.open)dialog.showModal();dialog.append($('gwrap'),$('ghover'));sourceSelect.value=module;
    sourceTitle.textContent=module+' · '+info.lines+' lines';
    sourceCode.textContent='Loading exact source…';
    try {
      let text=sourceCache.get(module);
      if(text===undefined){const r=await fetch(info.url);if(!r.ok)throw Error('HTTP '+r.status);text=await r.text();sourceCache.set(module,text);}
      if(currentModule!==module)return;
      // Line by line avoids accidentally putting markup inside lexical comments across lines.
      sourceCode.innerHTML=text.split('\n').map((s,i)=>'<span class="source-row'+(i+1===Number(line)?' chosen-line':'')+'" id="source-line-'+(i+1)+'"><span class="line-number">'+(i+1)+'</span><span>'+api.hlLean(s)+'</span></span>').join('');
      decorateTokens(sourceCode);
      sourceCode.querySelector('.chosen-line')?.scrollIntoView({block:'center'});
      $('source-origin').textContent=info.file+' · SHA-256 '+info.sha256;
      $('source-download').href=info.url;
    } catch(e) {sourceCode.textContent='Source could not be loaded: '+e.message;}
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
      body.append(el('p','',data.scope||'Read the linked verification record for this source snapshot.'));
      if(data.build){
        body.append(el('h3','','Recorded build'));
        if(data.build.canonical_checked_build_complete===true)body.append(el('p','','The recorded canonical build and axiom audits passed for this source snapshot.'));
        if(data.build.public_package_replay_complete===false)body.append(el('p','','This release does not claim a fresh rebuild of the entire development. Unchanged inherited sources reuse the earlier verified build.'));
        if(data.build.public_package_replay_complete===true)body.append(el('p','','A separate recorded replay rebuilt the local project sources in a fresh checkout.'));
        body.append(el('p','source-scope','Proof-source commit: '+data.build.code_commit));
        if(data.build.checked_build_receipt_url){const record=el('a','','Read the canonical build record');record.href=data.build.checked_build_receipt_url;record.target='_blank';record.rel='noopener';body.append(record);}
      }
      body.append(el('h3','','What the colors mean'));
      const list=el('ul');for(const text of ['Checked correspondence: the recorded review links this manuscript item to its Lean proof.','Definition: notation or a construction represented in the formal development.','External input: an assumption or cited result used at the stated boundary.','Pending: an older or candidate link that still needs current-source review.'])list.append(el('li','',text));body.append(list);
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
    if(n.status==='pending')box.prepend(el('p','pending-note','Candidate correspondence. This link has not yet been checked against this manuscript.'));
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
    new MutationObserver(records=>records.forEach(r=>r.addedNodes.forEach(node=>decorateTokens(node)))).observe($('gwrap'),{childList:true});
    const pageNote=el('span','','Page numbers include the title page.');
    pageNote.id='page-number-note';pageNote.title='All page links and filters use the PDF page number, counting the title page; the printed footer is one lower.';
    document.querySelector('.sheet-head .t').append(pageNote);
    $('pq').title=pageNote.title;$('q').title=pageNote.title;
    $('scope-note').textContent=api.PAYLOAD.verification.scope||'Read each item’s correspondence status and the recorded verification scope.';
    $('axiom-footprint').textContent='Recorded axiom audit: '+(Array.isArray(api.PAYLOAD.verification.axioms)?api.PAYLOAD.verification.axioms.join(' · '):'see verification record');
    $('s-proved').textContent=api.DATA.meta.counts.proved;
    $('s-reused').textContent=api.DATA.meta.counts.reused;
    $('s-axioms').textContent=api.DATA.meta.counts.axioms;
    $('s-pending').textContent=api.DATA.meta.counts.pending;
    $('f-count').textContent=api.DATA.nodes.length;
    const sourceButton=button('Lean source',()=>openSource(Object.keys(api.PAYLOAD.modules)[0]));sourceButton.id='browse-source';
    document.querySelector('.modes').append(sourceButton);
    const paperLink=el('a','paper-download','Paper PDF ↓');paperLink.href='paper.pdf';paperLink.target='_blank';paperLink.rel='noopener';document.querySelector('.modes').append(paperLink);
    const downloads=button('Lean code ↓',()=>$('dl-lean').click(),'trace-download');document.querySelector('.sheet-head').insertBefore(downloads,$('o-close'));
    const controls=el('div','proof-shortcuts');controls.setAttribute('aria-label','Proof shortcuts');
    const defaults=api.DATA.nodes.filter(n=>n.paper && n.paper.env==='theorem').slice(0,5).map(n=>({id:n.id,label:n.title}));
    (api.PAYLOAD.shortcuts.length?api.PAYLOAD.shortcuts:defaults).forEach((s,i)=>{const b=button((i+1)+'  '+s.label,()=>{api.openTrace(s.id);});b.title=s.detail||s.label;controls.append(b);});
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
    const hash=new URLSearchParams(location.hash.slice(1));const selected=hash.get('statement');
    if(hash.get('view')==='graph'){if(selected)api.select(selected,true);}else api.openTrace(selected||api.DATA.paperIndex[0]?.id);
    const observer=new MutationObserver(()=>{const id=$('td-id').textContent;if(id)history.replaceState(null,'','#statement='+encodeURIComponent(id));});
    observer.observe($('td-id'),{childList:true,subtree:true});
  }
  return {init,ready,renderSources,openSource};
})();
