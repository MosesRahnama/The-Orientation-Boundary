/* The Boundary Atlas: source records retain their own evidence. */
(() => {
  'use strict';
  const $ = (s, root = document) => root.querySelector(s);
  const $$ = (s, root = document) => [...root.querySelectorAll(s)];
  const esc = value => String(value ?? '').replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const count = value => new Intl.NumberFormat('en-US').format(Number(value) || 0);
  const clamp = (n, min, max) => Math.max(min, Math.min(max, n));
  const human = value => String(value || 'source only').replace(/[_-]/g, ' ');
  const shortName = value => String(value || '').split('.').pop().replace(/^(example|instance)@L(\d+)$/, '$1, line $2');
  const displayText = value => String(value || '').replace(/\\(?:\\|\s)+/g, ' ').replace(/\s+/g, ' ').trim();
  function displayPaperTitle(paper) {
    const title = displayText(paper?.shortTitle || paper?.title || paper?.label || paper?.name || 'Paper');
    if (/lemma\s*64|lemma64/i.test(title) && title.length > 42) return 'Lemma 64 Counterexample';
    return title.split(':')[0].trim() || title;
  }
  const safeUrl = value => { try { const u = new URL(value); return ['http:','https:'].includes(u.protocol) ? u.href : ''; } catch { return ''; } };
  const icons = {
    menu:'<path d="M3 5h14M3 10h14M3 15h14"/>',search:'<circle cx="8.5" cy="8.5" r="5.5"/><path d="m13 13 4 4"/>',
    graph:'<circle cx="10" cy="4" r="2"/><circle cx="4" cy="15" r="2"/><circle cx="16" cy="15" r="2"/><path d="m9 6-4 7m6-7 4 7M6 15h8"/>',
    list:'<path d="M7 5h10M7 10h10M7 15h10M3 5h.1M3 10h.1M3 15h.1"/>',folder:'<path d="M2 5h6l2 2h8v10H2z"/><path d="M2 5V3h6l2 2h6v2"/>',
    shield:'<path d="m10 2 7 3v5c0 4-7 8-7 8s-7-4-7-8V5z"/><path d="m6.5 9.5 2.3 2.3 4.7-5"/>',
    link:'<path d="m8 12 4-4M7 14l-1 1a3.5 3.5 0 0 1-5-5l4-4a3.5 3.5 0 0 1 5 0M13 6l1-1a3.5 3.5 0 0 1 5 5l-4 4a3.5 3.5 0 0 1-5 0" transform="translate(0 0) scale(.95)"/>',
    help:'<circle cx="10" cy="10" r="8"/><path d="M10 9v5M10 6h.01"/>',download:'<path d="M10 2v11m-4-4 4 4 4-4M3 13v4h14v-4"/>',
    bookmark:'<path d="M5 3h10v14l-5-3-5 3z"/>',refresh:'<path d="M16.5 7a7 7 0 1 0 .3 5M17 3v5h-5"/>',layout:'<rect x="2" y="2" width="16" height="16" rx="2"/><path d="M2 7h16M7 7v11"/>',
    filter:'<path d="M2 4h16l-6 6v6l-4 2v-8z"/>',plus:'<path d="M10 3v14M3 10h14"/>',minus:'<path d="M3 10h14"/>',
    fit:'<path d="M7 2H2v5m11-5h5v5M2 13v5h5m6 0h5v-5"/><rect x="6" y="6" width="8" height="8" rx="1"/>',
    expand:'<path d="M7 2H2v5m11-5h5v5M2 13v5h5m6 0h5v-5M2 2l5 5m6 6 5 5M18 2l-5 5m-6 6-5 5"/>',
    close:'<path d="m4 4 12 12M16 4 4 16"/>',arrow:'<path d="M4 10h12m-5-5 5 5-5 5"/>',external:'<path d="M11 2h7v7M18 2l-9 9M8 3H3v14h14v-5"/>',
    copy:'<rect x="7" y="7" width="10" height="11" rx="1"/><path d="M13 7V2H2v11h5"/>',check:'<path d="m3 10 5 5 9-10"/>',clock:'<circle cx="10" cy="10" r="8"/><path d="M10 5v5l3 2"/>'
  };
  const icon = name => `<span class="icon" aria-hidden="true"><svg viewBox="0 0 20 20">${icons[name] || icons.graph}</svg></span>`;
  function fillIcons(root = document) { $$('[data-icon]', root).forEach(el => { el.innerHTML = `<svg viewBox="0 0 20 20" aria-hidden="true">${icons[el.dataset.icon] || icons.graph}</svg>`; }); }
  const statusLabels = {
    'lean-baseline':'Lean: baseline axioms only','lean-flagged':'Lean: axioms beyond the baseline','recorded-baseline':'Recorded baseline axioms','recorded-flagged':'Recorded flagged axioms','compiled-baseline':'Recorded baseline axioms','compiled-flagged':'Recorded flagged axioms',
    'source-only':'Source only','source-indexed':'Source indexed','paper-statement':'Paper statement','stale-compiled':'Stale compiled evidence','has-hole':'Proof hole',
    'source-index-paper':'Claim index paper','index-record-only':'Claim index only','external-evidence':'External evidence','manuscript-source':'Manuscript source'
  };
  const relationLabels = {paper_shared:'Shared declaration scope',proof_dependency:'Compiled proof dependency',recorded_dependency:'Recorded dependency',elaborated_reference:'Elaborated reference',recorded_reference:'Recorded reference',source_reference:'Source reference',source_anchor:'Paper source anchor',claim_index_anchor:'Claim index anchor',claim_index_module:'Claim index module',import:'Module import',module_contains:'Module contains',paper_contains:'Paper contains',paper_reference:'Paper reference',exact_compiled:'Compiled dependency',compiled_dependency:'Compiled dependency'};
  const badge = status => `<span class="badge ${esc(status || 'source-only')}">${esc(statusLabels[status] || human(status))}</span>`;
  const palette = ['#287e77','#756d9d','#ac8148','#63886a','#98717b','#527e96','#a56851','#83924c','#697a9b','#9a7e4d'];
  let summary = null;
  let papers = [];
  let graphData = null;
  let selectedDetail = null;
  let returnFocus = null;
  let requestSerial = 0;
  let detailSerial = 0;
  let toastTimer;
  let searchTimer;
  let checkingFreshness = false;
  let bookmarks = [];
  try { bookmarks = JSON.parse(localStorage.getItem('boundary-atlas-bookmarks') || '[]'); if (!Array.isArray(bookmarks)) bookmarks = []; } catch { bookmarks = []; }
  const params = new URLSearchParams(location.search);
  const state = {
    view:['theories','graph','outline','results','files','coverage'].includes(params.get('view')) ? params.get('view') : 'theories',
    level:['paper','module','declaration'].includes(params.get('level')) ? params.get('level') : 'paper',
    paperIds: params.has('papers') ? (params.get('papers') === '__none__' ? [] : params.get('papers').split(',').filter(Boolean)) : null,
    q:params.get('q') || '', match:params.get('match') === 'all' ? 'all' : 'any',focus:params.get('focus') || '',
    depth:clamp(Number(params.get('depth')) || 1,1,3),direction:['both','in','out'].includes(params.get('direction')) ? params.get('direction') : 'both',
    layout:['force','hierarchical','radial'].includes(params.get('layout')) ? params.get('layout') : 'force',limit:clamp(Number(params.get('limit')) || 240,1,3000),
    kind:params.get('kind') || '',status:params.get('status') || '',exact:params.get('exact') === '1',page:1,pageSize:50,sort:'name',order:'asc',fileSort:'path',fileOrder:'asc',
    relations:params.has('relations') ? (params.get('relations')==='__none__'?[]:params.get('relations').split(',').filter(Boolean)) : null,list:false,node:params.get('node') || ''
  };
  async function api(path, query = {}) {
    const p = new URLSearchParams();
    for (const [k,v] of Object.entries(query)) if (v !== '' && v !== null && v !== undefined) p.set(k, v);
    const response = await fetch(`/api/${path}${p.size ? `?${p}` : ''}`, {headers:{Accept:'application/json'}});
    if (!response.ok) { let reason = ''; try { const data = await response.json(); reason = data.error || data.message || ''; } catch {} throw new Error(reason || `The source service returned ${response.status}.`); }
    return response.json();
  }
  function scope() { return {papers:state.paperIds === null ? (state.match === 'all' && papers.length ? papers.map(p=>p.id).join(',') : '') : state.paperIds.length ? state.paperIds.join(',') : '__none__',match:state.match}; }
  function writeUrl(mode = 'replace') {
    const u = new URL(location.href); u.search = '';
    const values = {...scope(),view:state.view,level:state.level,q:state.q,focus:state.focus,depth:state.depth === 1 ? '' : state.depth,direction:state.direction === 'both' ? '' : state.direction,layout:state.layout === 'force' ? '' : state.layout,limit:state.limit === 240 ? '' : state.limit,kind:state.kind,status:state.status,exact:state.exact ? '1' : '',node:state.node,relations:state.relations === null ? '' : state.relations.length ? state.relations.join(',') : '__none__'};
    if (values.match === 'any') delete values.match;
    for (const [k,v] of Object.entries(values)) if (v !== '' && v !== null) u.searchParams.set(k,v);
    const marker = {atlas:true,atlasModalEntry:!!state.node && (mode === 'push' || !!history.state?.atlasModalEntry)};
    if (mode === 'push') history.pushState(marker,'',u); else history.replaceState(marker,'',u);
  }
  function showToast(message) { clearTimeout(toastTimer); $('#toast').textContent = message; $('#toast').hidden = false; toastTimer = setTimeout(() => { $('#toast').hidden = true; },4000); }
  function showError(message) { const e=$('#error-banner');e.innerHTML = `<span>${esc(message)}</span><button class="text-button" id="retry-request">Retry</button>`;e.hidden=false;$('#retry-request').onclick=()=>loadView(); }
  function clearError() { $('#error-banner').hidden=true; }
  function dateText(value) { if(!value) return 'Build time not recorded';const d=new Date(value);return Number.isNaN(d.getTime()) ? String(value) : d.toLocaleString(undefined,{year:'numeric',month:'short',day:'numeric',hour:'2-digit',minute:'2-digit'}); }
  function ageText(value) { const d=new Date(value);if(!value||Number.isNaN(d.getTime()))return '';const m=Math.max(0,Math.round((Date.now()-d.getTime())/60000));return m<2?'just now':m<60?`${m} minutes ago`:m<2880?`${Math.round(m/60)} hours ago`:`${Math.round(m/1440)} days ago`; }
  function buildLine(data) { const age=ageText(data?.generatedAt);return `Index built ${dateText(data?.generatedAt)}${age?` (${age})`:''} · ${count(data?.counts?.files)} source files · this page checks for a newer completed index every 45 seconds`; }
  function renderProfile(data) {
    document.title = data?.title || 'The Boundary Atlas';
    const note=$('#profile-note');if(!note)return;
    note.textContent=data?.publicExportAllowed
      ? 'Public repository sources. Paper links, saved readings and Lean proof evidence are separate records.'
      : `Local only · ${data?.profile||'local'} profile. Includes unpublished manuscript text; do not publish this index or its exports. Lean sources and evidence are limited to the selected repository.`;
  }
  function paperColor(id) { const i=papers.findIndex(p=>p.id===id);const c=papers[i]?.color;return /^#[0-9a-f]{3,8}$/i.test(c || '') ? c : palette[Math.max(0,i)%palette.length]; }
  function nodeColor(n) { if(n.kind==='paper') return paperColor(n.id);if(String(n.kind || '').startsWith('paper_') || ['paper_result','claim','lemma_result','theorem_result','result','paper-result'].includes(n.kind)||n.status==='paper-statement'||n.status==='index-record-only')return '#aa8247';if(['module','file'].includes(n.kind))return '#4e8290';return '#7b739f'; }
  function selectedPaper(p) { return state.paperIds===null || state.paperIds.includes(p.id); }
  /* Graph groups: Lean files group by their folder, declarations by their module, papers by themselves. */
  function groupKey(n) {
    if(n.kind==='paper')return 'papers';
    if(state.level==='module'){const parts=String(n.module||'').split('.').filter(Boolean);if(!parts.length)return 'other';if(parts[0]==='OperatorKO7'){if(parts[1]==='Meta'&&parts.length>3)return parts.slice(0,3).join('.');return parts.slice(0,Math.max(1,Math.min(2,parts.length-1))).join('.');}return parts[0];}
    if(state.level==='declaration'){if(n.kind==='external_declaration'||n.kind==='external_module')return 'external';const parts=String(n.module||'').split('.').filter(Boolean);return parts.length?parts.slice(0,Math.min(3,parts.length)).join('.'):(n.paperIds?.[0]||'unmapped');}
    return n.paperIds?.[0]||'unmapped';
  }
  function groupTitle(key) {
    if(key==='papers')return 'Papers';if(key==='external')return 'Lean core and Mathlib';if(key==='unmapped')return 'No paper link';if(key==='other')return 'Other files';if(key==='other-small')return 'Other folders';
    const paper=papers.find(p=>p.id===key);if(paper)return displayPaperTitle(paper);
    const parts=String(key).split('.');if(parts[0]==='OperatorKO7'){const rest=parts.slice(1);if(rest[0]==='Test')return 'Check files (Test)';return rest.length?rest.join(' / '):'Root modules';}
    return key;
  }
  function renderPapers() {
    const query=$('#paper-search').value.trim().toLowerCase();
    const visible=papers.filter(p=>(p.title+' '+p.shortTitle).toLowerCase().includes(query));
    $('#paper-count').textContent=count(papers.length);
    $('#selection-count').textContent=`${state.paperIds===null ? papers.length : state.paperIds.length} selected`;
    $('#paper-list').innerHTML=visible.length ? visible.map(p=>`<label class="paper-option ${selectedPaper(p)?'selected':''}"><input type="checkbox" data-paper="${esc(p.id)}" ${selectedPaper(p)?'checked':''}><span class="paper-option-body"><span class="paper-option-name">${esc(displayPaperTitle(p))}</span><span class="paper-option-meta"><i class="paper-color" style="background:${paperColor(p.id)}"></i><span>${count(p.resultCount)} results</span><span>·</span><span>${count(p.declarationCount)} declarations</span></span></span></label>`).join('') : '<div class="table-empty">No paper matches the filter.</div>';
    $$('[data-paper]',$('#paper-list')).forEach(el=>el.onchange=()=>{
      const ids=new Set(state.paperIds===null ? papers.map(p=>p.id) : state.paperIds);if(el.checked)ids.add(el.dataset.paper);else ids.delete(el.dataset.paper);
      state.paperIds=ids.size===papers.length ? null : [...ids];state.page=1;state.focus='';renderPapers();loadView();
    });
  }
  function renderMetrics(data) {
    const c=data?.counts || data?.totals || summary?.counts || {};
    const records=c.paperResults ?? c.results ?? 0;
    const items=[
      [c.papers,'Papers','Papers and claim indexes'],
      [c.files,'Source files','Files in the selected scope'],
      [c.declarations,'Lean declarations','Parsed from the Lean files'],
      [records,'Paper results','Numbered results of the papers']
    ];
    $('#metrics').innerHTML=items.map(([n,label,note])=>`<div class="metric"><div class="metric-top"><strong class="metric-value">${count(n)}</strong><span class="metric-label">${label}</span></div><div class="metric-note">${note}</div></div>`).join('');
  }
  function renderBookmarks() {
    $('#bookmark-count').textContent=count(bookmarks.length);
    $('#bookmark-list').innerHTML=bookmarks.length ? bookmarks.map(b=>`<div class="bookmark-item"><button class="text-button" data-bookmark-open="${esc(b.id)}">${esc(b.label || b.id)}</button><button class="icon-button" data-bookmark-remove="${esc(b.id)}" aria-label="Remove saved node">${icon('close')}</button></div>`).join('') : '<p class="detail-empty">Saved records appear here.</p>';
    $$('[data-bookmark-open]').forEach(el=>el.onclick=()=>openNode(el.dataset.bookmarkOpen));
    $$('[data-bookmark-remove]').forEach(el=>el.onclick=()=>{bookmarks=bookmarks.filter(b=>b.id!==el.dataset.bookmarkRemove);saveBookmarks();});
  }
  function saveBookmarks() { try{localStorage.setItem('boundary-atlas-bookmarks',JSON.stringify(bookmarks));}catch{showToast('Browser storage is unavailable. Saved nodes remain in this session.');}renderBookmarks(); }
  function renderRelations() {
    const kinds=summary?.relationKinds?.map(x=>x.kind) || Object.keys(relationLabels);
    if(!kinds.includes('paper_shared'))kinds.unshift('paper_shared');
    $('#edge-filter-panel').innerHTML=kinds.map(k=>`<label class="edge-option"><input type="checkbox" data-relation="${esc(k)}" ${state.relations===null || state.relations.includes(k)?'checked':''}><span>${esc(relationLabels[k] || human(k))}</span></label>`).join('');
    $('#edge-filter-count').textContent=state.relations===null ? '' : `(${state.relations.length})`;
    $$('[data-relation]').forEach(el=>el.onchange=()=>{state.relations=$$('[data-relation]:checked').map(e=>e.dataset.relation);if(state.relations.length===kinds.length)state.relations=null;renderRelations();loadView();});
  }
  const viewCopy={theories:['Theory map','The theories of the public Lean files, their conclusions, the relationships between them, and the boundary path from the kernel to the main results.'],graph:['Proof graph','Papers, Lean files and declarations, with their dependencies and recorded links.'],outline:['Paper walkthrough','The results of one paper in the order of the text, with the Lean declarations recorded for each result.'],results:['Results and declarations','Search over the paper results and the Lean declarations of the index.'],files:['Source files','Every source file with its declarations and its text.'],coverage:['Coverage and evidence','Source coverage, recorded proof evidence and unresolved links.']};
  function syncControls() {
    $$('.tab').forEach(el=>{const active=el.dataset.view===state.view;el.classList.toggle('active',active);if(active)el.setAttribute('aria-current','page');else el.removeAttribute('aria-current');});
    for(const v of ['theories','graph','outline','results','files','coverage'])$(`#${v}-view`).hidden=state.view!==v;
    $('#view-title').textContent=viewCopy[state.view][0];$('#view-description').textContent=viewCopy[state.view][1];
    $$('[data-level]').forEach(el=>{const active=el.dataset.level===state.level;el.classList.toggle('active',active);el.setAttribute('aria-pressed',String(active));});
    $('#global-search').value=state.q;$('#match-mode').value=state.match;$('#graph-layout').value=state.layout;$('#graph-limit').value=String(state.limit);$('#graph-depth').value=String(state.depth);$('#graph-direction').value=state.direction;
    $('#result-kind').value=state.kind;$('#result-status').value=state.status;$('#exact-search').checked=state.exact;
    $('#focus-bar').hidden=!state.focus;$('#focus-name').textContent=graphData?.nodes.find(n=>n.id===state.focus)?.label || state.focus;
    const labels={paper:['PAPER CONNECTIONS','Shared source and dependency scopes'],module:['LEAN FILE CONNECTIONS','Imports and module relations · each outlined group is one folder of Lean files'],declaration:['DECLARATION CONNECTIONS','Dependencies, references, and recorded anchors · each outlined group is one module']};
    $('#graph-stage-title').textContent=labels[state.level][0];$('#graph-stage-subtitle').textContent=labels[state.level][1];
  }
  async function loadView() {
    const serial=++requestSerial;clearError();syncControls();writeUrl();
    if(!summary)return;
    const p={...scope(),q:state.q,page:state.page,pageSize:state.pageSize};
    if(state.view==='graph')$('#graph-loading').hidden=false;
    try {
      const metricPromise=state.paperIds===null && state.match==='any' ? Promise.resolve(summary) : api('summary',scope());
      metricPromise.catch(() => {});
      let data;
      if(state.view==='theories')data=await api('atlas');
      else if(state.view==='graph')data=await api('graph',{...scope(),level:state.level,focus:state.focus,depth:state.depth,direction:state.direction,limit:state.limit,relations:state.relations===null?'':state.relations.length?state.relations.join(','):'__none__'});
      else if(state.view==='results')data=await api('search',{...p,kind:state.kind,status:state.status,exact:state.exact?'1':'',sort:state.sort,order:state.order});
      else if(state.view==='files')data=await api('files',{...p,sort:state.fileSort,order:state.fileOrder});
      else if(state.view==='outline'){data=await api('outline',scope());await loadClaimGrades();}
      else data=await api('coverage',scope());
      const metrics=await metricPromise;
      if(serial!==requestSerial)return;
      renderMetrics(metrics);
      if(state.view==='theories')renderTheories(data);else if(state.view==='graph')renderGraph(data);else if(state.view==='results')renderResults(data);else if(state.view==='files')renderFiles(data);else if(state.view==='outline')renderOutline(data);else renderCoverage(data);
    }catch(error){if(serial===requestSerial){showError(error.message);if(state.view==='graph'){$('#graph-empty').innerHTML='<h3>The graph is unavailable.</h3><p>The source service did not complete the request. The retry control repeats the selected view.</p>';$('#graph-empty').hidden=false;}}}
    finally{if(serial===requestSerial)$('#graph-loading').hidden=true;}
  }
  function setView(view) { state.view=view;state.page=1;loadView(); }
  function renderResults(data) {
    const rows=data.items || [];
    $('#results-table tbody').innerHTML=rows.length ? rows.map(n=>`<tr><td><button class="row-title" data-node="${esc(n.id)}">${esc(n.label || shortName(n.name))}</button><span class="row-subtitle">${esc(n.name || n.statement || n.module)}</span></td><td><span class="kind-label">${esc(human(n.kind))}</span></td><td>${badge(n.status)}</td><td>${sourceLink(n.sourceUrl,n.file || n.module,n.line)}</td><td><button class="icon-button" data-node="${esc(n.id)}" aria-label="Inspect ${esc(n.label || n.name)}">${icon('arrow')}</button></td></tr>`).join('') : '<tr><td colspan="5" class="table-empty"><strong>No matching records.</strong>The paper selection, name, kind, or evidence filters can be changed.</td></tr>';
    bindNodes($('#results-table'));renderPagination('results',data);
  }
  function sourceLink(url,file,line) {
    const path=String(file || '').replaceAll('\\','/').split('/').pop();
    return safeUrl(url) ? `<a class="source-link" href="${esc(safeUrl(url))}" target="_blank" rel="noopener noreferrer" title="${esc(file)}">${esc(path || 'Repository')}${line ? `:${count(line)}` : ''} ${icon('external')}</a>` : `<span class="row-subtitle" title="${esc(file)}">${esc(path || 'Indexed source')}${line?`:${count(line)}`:''}</span>`;
  }
  function renderFiles(data) {
    const rows=data.items || [];$('#file-list-count').textContent=`${count(data.total)} indexed files`;
    $('#files-table tbody').innerHTML=rows.length ? rows.map(f=>`<tr><td><button class="row-title" data-node="${esc(f.id)}">${esc(f.path)}</button><span class="row-subtitle">${esc(f.module || 'Source document')}</span></td><td><span class="kind-label">${esc(f.kind)}</span></td><td>${count(f.declarationCount)}</td><td>${count(f.lineCount)}</td><td>${sourceLink(f.sourceUrl,'Repository',null)}<button class="icon-button" data-node="${esc(f.id)}" aria-label="Inspect ${esc(f.path)}">${icon('arrow')}</button></td></tr>`).join('') : '<tr><td colspan="5" class="table-empty"><strong>No matching files.</strong>The full collection appears with all papers selected.</td></tr>';
    bindNodes($('#files-table'));renderPagination('files',data);
  }
  function renderPagination(view,data) {
    const page=Number(data.page)||1,size=Number(data.pageSize)||state.pageSize,total=Number(data.total)||0,pagesCount=Math.max(1,Math.ceil(total/size));
    $(`#${view}-pagination`).innerHTML=`<span>${total ? `${count((page-1)*size+1)}–${count(Math.min(page*size,total))}` : '0'} of ${count(total)} records</span><div class="pagination-actions"><label>Rows <select aria-label="Rows per page" data-page-size><option ${size===25?'selected':''}>25</option><option ${size===50?'selected':''}>50</option><option ${size===100?'selected':''}>100</option><option ${size===250?'selected':''}>250</option></select></label><button class="button" data-page="${page-1}" ${page<=1?'disabled':''}>Previous</button><span>${count(page)} / ${count(pagesCount)}</span><button class="button" data-page="${page+1}" ${page>=pagesCount?'disabled':''}>Next</button></div>`;
    $$('[data-page]',$(`#${view}-pagination`)).forEach(el=>el.onclick=()=>{state.page=Number(el.dataset.page);loadView();});
    $('[data-page-size]',$(`#${view}-pagination`)).onchange=e=>{state.pageSize=Number(e.target.value);state.page=1;loadView();};
  }
  function compilerEvidenceSection() {
    const evidence = summary?.compiledEvidence || summary?.evidence?.compiled || {};
    const refs = evidence.references;
    const recorded = evidence.recordedProofs;
    const hasReferences = !!refs && typeof refs === 'object';
    const hasProofs = recorded?.available === true;
    const unavailable = !hasReferences && !hasProofs;
    const degraded = evidence.degraded === true || refs?.degraded === true || recorded?.degraded === true;
    const stateLabel = unavailable ? 'Evidence unavailable' : degraded ? 'Degraded coverage' : 'Evidence recorded';
    const stateClass = unavailable || degraded ? 'recorded-flagged' : 'source-indexed';
    const metrics = [
      [hasReferences ? count(refs.current_reference_files) : 'Unavailable', 'Current reference files', 'Compiler reference artifacts at least as recent as their source.'],
      [hasReferences ? count(refs.stale_reference_files) : 'Unavailable', 'Stale reference files', 'Reference artifacts older than their source.'],
      [hasReferences ? count(refs.missing_reference_files) : 'Unavailable', 'Missing reference files', 'Lean files without a compiler reference artifact.'],
      [hasProofs ? count(recorded.recorded_declarations) : 'Unavailable', 'Recorded declarations', 'Declarations with retained compiled proof evidence.'],
      [hasProofs ? count(recorded.proof_edges) : 'Unavailable', 'Current proof links', 'Recorded dependencies with current source and artifact checks.'],
      [hasProofs ? count(recorded.stale_proof_edges) : 'Unavailable', 'Stale proof links', 'Recorded dependencies whose compiled evidence needs refresh.']
    ];
    return `<section class="issues-panel compiler-evidence"><div class="compiler-heading"><div><p class="eyebrow">ALL FILES</p><h3>Compiler evidence across the collection</h3></div><span class="badge ${stateClass}">${stateLabel}</span></div><p class="compiler-scope">These totals cover the entire generated index. Paper selection does not change them.</p><div class="compiler-metrics">${metrics.map(([value,label,note])=>`<div class="compiler-metric"><strong class="${value==='Unavailable'?'unavailable-value':''}">${esc(value)}</strong><span>${esc(label)}</span><small>${esc(note)}</small></div>`).join('')}</div>${recorded?.available===false?`<div class="detail-callout"><strong>Recorded proof export unavailable.</strong> ${esc(recorded.reason || 'No compiled proof export was supplied.')}</div>`:''}<p class="compiler-note">${esc(evidence.note || 'The index retains existing compiler evidence with its source checks. No new Lean build or manuscript-equivalence check runs in this view.')}</p></section>`;
  }
  const ISSUE_TEXT = {
    'unresolved-anchor': 'The paper names code the public repository lacks',
    'ambiguous-anchor': 'A paper name matches more than one public declaration',
    'claim-index-label-absent': 'The claim index cites a label the paper lacks',
    'claim-index-label-ambiguous': 'A claim index label matches two paper results',
    'claim-index-declaration-unresolved': 'The claim index names a declaration the public code lacks',
    'claim-index-declaration-ambiguous': 'A claim index name matches more than one public declaration',
    'claim-index-module-unresolved': 'The claim index names a file the public code lacks',
    'compiler-reference-error': 'The local Lean build differs from the published file',
    'compiler-target-module-mismatch': 'The local Lean build places a name in another file',
    'duplicate-paper-label': 'The paper uses one label twice',
  };
  function issueDetail(i) {
    const subject = i.token || i.name || i.label || i.module || i.include;
    if (subject) return subject;
    return i.message || Object.entries(i).filter(([key])=>key!=='kind').map(([key,value])=>`${human(key)}: ${typeof value==='object'?JSON.stringify(value):value}`).join(' · ') || human(i.kind);
  }
  function renderCoverageIssues(issues, limit = 100) {
    const container = $('#coverage-issues');
    if (!container) return;
    if (!issues.length) { container.innerHTML='<p class="detail-empty">No additional issues are recorded in this build.</p>';return; }
    const shown = issues.slice(0,limit);
    container.innerHTML = shown.map(i=>`<div class="issue-row"><strong>${esc(ISSUE_TEXT[i.kind] || human(i.kind || 'source note'))}</strong><div><p>${esc(issueDetail(i))}</p>${i.source || i.file || i.path ? `<small>${esc(i.source || i.file || i.path)}${i.line?`:${count(i.line)}`:''}</small>` : ''}</div></div>`).join('') + `<div class="issue-pagination"><span>${count(shown.length)} of ${count(issues.length)} issues shown</span>${shown.length<issues.length?`<button class="button" id="more-coverage-issues">Show next ${count(Math.min(100,issues.length-shown.length))}</button>`:''}</div>`;
    if ($('#more-coverage-issues')) $('#more-coverage-issues').onclick=()=>renderCoverageIssues(issues,limit+100);
  }
  function renderCoverage(data) {
    const c=data.totals || {},total=Number(c.paperResults)||0,anchored=Number(c.anchoredResults)||0,ratio=total?Math.min(100,100*anchored/total):0;
    const manuscript=data.manuscriptCoverage || summary?.manuscriptCoverage || [];
    const paperCards=(data.papers || []).map(p=>{
      const pc=Number(p.resultCount)||0,pa=Number(p.anchoredResults)||0,percent=pc?Math.min(100,100*pa/pc):0;
      const complete=p.manuscriptAvailable===true;
      const note=complete ? 'Manuscript source is present. Counts refer to the extracted records.' : p.manuscriptAvailable===false || p.sourceIndexPaper ? 'Claim-index records are present. Full manuscript coverage is not established.' : 'Coverage follows the source records held by this index.';
      return `<article class="coverage-paper"><h3>${esc(displayText(p.title))}</h3><div class="coverage-bar" aria-label="${count(pa)} of ${count(pc)} results have explicit anchors"><span style="width:${percent}%"></span></div><div class="coverage-paper-metrics"><div><strong>${count(pc)}</strong><span>Paper results</span></div><div><strong>${count(pa)}</strong><span>Explicit anchors</span></div><div><strong>${count(p.declarationCount)}</strong><span>Lean declarations</span></div></div><div class="coverage-paper-note">${esc(note)}</div><button class="text-button" data-coverage-paper="${esc(p.id)}" style="margin-top:10px">Open paper scope ${icon('arrow')}</button></article>`;
    }).join('');
    const issues=data.issues || [];
    $('#coverage-view').innerHTML=`<section class="coverage-intro"><div><h2>Source coverage</h2><p>${esc(data.method || 'The index counts source records and explicit code anchors.')}</p><p>${esc(data.meaning || 'An anchor identifies a source. Matching the manuscript to the complete Lean type remains a separate claim.')}</p></div><div class="coverage-chart"><div class="big-number">${count(anchored)}<small>of ${count(total)} results anchored</small></div><div class="coverage-bar" aria-label="${ratio.toFixed(1)} percent explicitly anchored"><span style="width:${ratio}%"></span></div><div class="coverage-legend"><span><i class="legend-dot"></i> Explicit source anchor</span><span><i class="legend-dot" style="background:#d8dfd3"></i> No anchor recorded</span></div><p>The ratio measures source-link coverage. It does not measure theorem correctness.</p></div></section>${compilerEvidenceSection()}<div class="coverage-grid">${paperCards || '<div class="table-empty">No papers are selected.</div>'}</div><section class="issues-panel"><h3>Source gaps <span class="count-label">${count(issues.length)}</span></h3><p class="compiler-scope">Each record names a reference in a paper or a claim index that the public Lean code does not carry, or a local build that differs from the published files.</p><div id="coverage-issues"></div></section>${manuscript.length ? `<section class="issues-panel"><h3>Manuscript source records</h3>${manuscript.map(m=>`<div class="issue-row"><strong>${esc(displayText(m.title || papers.find(p=>p.id===(m.paper_id || m.paperId || m.id))?.title || m.paper || m.paper_id || m.paperId || m.id || 'Manuscript'))}</strong><div><p>${esc(m.message || m.note || m.status || (m.manuscript_available===true || m.available===true?'Full manuscript source present':m.manuscript_available===false || m.available===false?'Claim-index records only; manuscript source absent':'Source record'))}</p>${m.path || m.source ? `<small>${esc(m.path || m.source)}</small>` : ''}</div></div>`).join('')}</section>` : ''}`;
    renderCoverageIssues(issues);
    $$('[data-coverage-paper]').forEach(el=>el.onclick=()=>{state.paperIds=[el.dataset.coveragePaper];state.focus='';state.view='graph';state.level='declaration';renderPapers();loadView();});
  }
  function bindNodes(root) { $$('[data-node]',root).forEach(el=>el.onclick=()=>openNode(el.dataset.node)); }
  /* The paper walkthrough: one paper's results in text order under their sections, each with its recorded status and Lean declarations. */
  function renderOutline(data) {
    const view=$('#outline-view');
    if(!data.paper){
      const choices=(data.papers||[]).filter(p=>state.paperIds===null||state.paperIds.includes(p.id));
      view.innerHTML=`<div class="outline-intro"><div><p class="eyebrow">PAPER WALKTHROUGH</p><h2>Paper choice</h2><p>The walkthrough follows one paper in the order of its text and lists the Lean declarations recorded behind each result. A choice below sets the paper.</p></div></div><div class="outline-section"><div class="detail-links">${choices.map(p=>`<button class="detail-link" data-outline-paper="${esc(p.id)}"><div><strong>${esc(displayPaperTitle(p))}</strong><small>${count(p.resultCount)} results · ${count(p.declarationCount)} declarations</small></div>${icon('arrow')}</button>`).join('')||'<p class="detail-empty">No paper is selected in the left column.</p>'}</div></div>`;
      $$('[data-outline-paper]',view).forEach(el=>el.onclick=()=>{state.paperIds=[el.dataset.outlinePaper];renderPapers();loadView();});return;
    }
    const t=data.totals||{};
    const kindName=k=>({paper_theorem:'Theorem',paper_proposition:'Proposition',paper_lemma:'Lemma',paper_corollary:'Corollary',paper_definition:'Definition',paper_remark:'Remark',paper_example:'Example',paper_observation:'Observation',paper_recorded_claim:'Index record'})[k]||human(String(k).replace(/^paper_/,''));
    const stripKind=label=>String(label||'').replace(/^(Theorem|Proposition|Lemma|Corollary|Definition|Remark|Example|Observation):\s*/i,'');
    const clip=(text,max)=>{const s=String(text||'');return s.length>max?s.slice(0,max-1)+'…':s;};
    view.innerHTML=`<div class="outline-intro"><div><p class="eyebrow">PAPER WALKTHROUGH</p><h2>${esc(displayPaperTitle(data.paper))}</h2><p>Every numbered result in the order of the text. The right column gives the recorded claim-index status and the number of Lean declarations recorded behind the result; a chip opens the declaration, the title opens the result.</p></div><div class="outline-counts"><div><strong>${count(t.results)}</strong>results</div><div><strong>${count(t.anchored)}</strong>with Lean records</div><div><strong>${count(t.sections)}</strong>sections</div></div></div>${(data.sections||[]).map((s,si)=>`<section class="outline-section"><h3>${s.recorded?'':`<span class="guide-number" style="font-size:14px">${String(si+1).padStart(2,'0')}</span>`}${esc(s.title)}<small>${count(s.results.length)} results</small></h3>${s.results.map((r,ri)=>`${r.subsection&&r.subsection!==(s.results[ri-1]||{}).subsection?`<p class="source-note" style="margin:10px 0 2px;font-weight:600">${esc(r.subsection)}</p>`:''}<div class="outline-row"><div class="outline-kind"><button class="row-title" data-node="${esc(r.id)}">${esc(kindName(r.kind))}</button><small>${/\.tex:L\d+$/.test(r.name)?`line ${count(r.line)}`:esc(r.name)}</small></div><div class="outline-text"><button class="row-title" data-node="${esc(r.id)}">${/\.tex:L\d+$/.test(r.name)?`Unnumbered ${esc(kindName(r.kind).toLowerCase())} at line ${count(r.line)}`:esc(stripKind(r.label))}</button>${r.leanResult?`<div>${esc(clip(r.leanResult,260))}</div>`:''}${r.anchors?.length?`<div class="lean-names">${r.anchors.map(a=>`<button data-node="${esc(a.id)}" title="${esc(a.name)}">${esc(shortName(a.name))}</button>`).join('')}${r.anchorCount>r.anchors.length?`<span class="count-label">+${count(r.anchorCount-r.anchors.length)} more</span>`:''}</div>`:''}</div><div class="outline-evidence">${r.recordedStatus?`<span class="badge ${String(r.recordedStatus).toUpperCase()==='PROVEN'?'recorded-baseline':'index-record-only'}">Index: ${esc(r.recordedStatus)}</span>`:badge(r.status)}<small>${r.anchorCount?`${count(r.anchorCount)} Lean ${r.anchorCount===1?'declaration':'declarations'}`:'No Lean record'}${r.entryCount>1?` · ${count(r.entryCount)} index entries`:''}</small>${(r.claimRefs||[]).slice(0,1).map(ref=>{const g=claimGradeFor(ref);return g?`<span class="grade grade-${esc(g.grade)}" title="${esc(g.reason)}">${esc(gradeLabels[g.grade]||human(g.grade))}</span>`:''}).join('')}</div><button class="icon-button" data-node="${esc(r.id)}" aria-label="Inspect ${esc(r.label)}">${icon('arrow')}</button></div>`).join('')}</section>`).join('')||'<div class="outline-empty">No results are recorded for this paper.</div>'}`;
    bindNodes(view);
  }
  function renderGraph(data) {
    data = {...data,nodes:(data.nodes || []).map(node=>node.kind==='paper'?{...node,label:displayPaperTitle(papers.find(p=>p.id===node.id) || node)}:node)};
    graphData=data;$('#graph-empty').hidden=!!data.nodes?.length;
    if(!data.nodes?.length)$('#graph-empty').innerHTML='<h3>No nodes in this view.</h3><p>The paper selection, graph level, or link filters can be changed. All source records remain in the searchable index.</p>';
    $('#graph-summary').innerHTML=`<span><strong>${count(data.nodes?.length)} nodes · ${count(data.edges?.length)} links shown</strong> of ${count(data.totalNodes)} nodes · ${count(data.totalEdges)} links${data.truncated?' <span class="limit-note">· Visible limit reached</span>':''}</span><span>${esc(data.note || '')}</span>`;
    $('#graph-node-list').innerHTML=(data.nodes || []).map(n=>`<button class="graph-list-node" data-node="${esc(n.id)}"><strong><i class="paper-color" style="background:${nodeColor(n)};margin-right:7px"></i>${esc(n.label || n.name)}</strong><small>${esc(human(n.kind))} · ${esc(statusLabels[n.status] || human(n.status))} · ${count(n.degree)} links</small></button>`).join('') || '<p class="detail-empty">No nodes in the current graph.</p>';
    bindNodes($('#graph-node-list'));syncControls();graph.setData(data);setGraphList(state.list);
  }
  function setGraphList(value) { state.list=value;$('#graph-node-list').hidden=!value;$('#graph-stage').hidden=value;$('#graph-list-toggle').setAttribute('aria-pressed',String(value));$('#graph-list-toggle').setAttribute('aria-label',value?'Show graph canvas':'Show graph as a list');if(!value)graph.resize(); }
  function closeDetail(options = {}) {
    if (!options.fromHistory && !options.replace && history.state?.atlasModalEntry && state.node) { history.back(); return; }
    $('#detail-panel').hidden=true;$('#detail-backdrop').hidden=true;state.node='';selectedDetail=null;detailSerial++;
    if (!options.fromHistory) writeUrl();
    document.body.style.overflow='';
    if (returnFocus?.isConnected) returnFocus.focus(); else $('#main').focus();
  }
  function detailShell() {
    if ($('#detail-panel').hidden) returnFocus=document.activeElement;$('#detail-panel').hidden=false;$('#detail-backdrop').hidden=false;document.body.style.overflow='hidden';
    $('#detail-panel').innerHTML=`<button class="icon-button detail-close-loading" id="close-detail" aria-label="Close record">${icon('close')}</button><div class="detail-loading"><span class="loader"></span><span>Reading the source record</span></div>`;$('#close-detail').onclick=closeDetail;$('#close-detail').focus();
  }
  async function openNode(id, options = {}) {
    const push = options.push !== false && $('#detail-panel').hidden && new URLSearchParams(location.search).get('node') !== id;
    state.node=id;writeUrl(push ? 'push' : 'replace');detailShell();const serial=++detailSerial;
    try { if(id.startsWith('claims:')){const g=await loadClaimGrades();if(serial!==detailSerial)return;selectedDetail=null;renderPaperClaims(id.slice(7),g);return;} if(id.startsWith('theory:')){const t=await api('theory',{id:id.slice(7)});if(serial!==detailSerial)return;selectedDetail=null;renderTheory(t);return;} const data=await api('node',{id});if(serial!==detailSerial)return;selectedDetail=data;renderDetail(data); }
    catch(e){if(serial!==detailSerial)return;$('#detail-panel').innerHTML=`<div class="detail-top"><div class="detail-topline"><span class="eyebrow">SOURCE RECORD</span><button id="close-detail" class="icon-button" aria-label="Close record">${icon('close')}</button></div><h2>Record unavailable.</h2></div><div class="detail-body"><p>${esc(e.message)}</p><button id="retry-detail" class="button">Retry</button></div>`;$('#close-detail').onclick=closeDetail;$('#retry-detail').onclick=()=>openNode(id);$('#close-detail').focus();}
  }
  function renderDetail(data) {
    const n=data.node || {},source=data.source || {},sourceUrl=safeUrl(source.url || n.sourceUrl),saved=bookmarks.some(b=>b.id===n.id);
    const warnings=Array.isArray(data.warnings)?data.warnings:[];
    $('#detail-panel').innerHTML=`<div class="detail-top"><div class="detail-topline"><span class="eyebrow">${esc(human(n.kind))} / SOURCE RECORD</span><div class="detail-actions"><button class="icon-button" id="widen-panel" aria-label="Widen the record panel" aria-pressed="false">${icon('expand')}</button><button class="icon-button" id="save-node" aria-label="${saved?'Remove saved record':'Save record'}" aria-pressed="${saved}">${icon(saved?'check':'bookmark')}</button><button class="icon-button" id="copy-node-link" aria-label="Copy record link">${icon('link')}</button><button id="close-detail" class="icon-button" aria-label="Close record">${icon('close')}</button></div></div><h2>${esc(displayText(n.label || shortName(n.name) || n.id))}</h2>${n.name && n.name!==n.label ? `<div class="detail-fullname">${esc(n.name)}</div>`:''}<div class="detail-badges">${badge(n.status)}${n.module?`<span class="count-label">${esc(n.module)}</span>`:''}</div><div class="source-actions"><button id="focus-node" class="button primary" ${n.graphAvailable===false?'disabled title="This file has no graph node"':''}>${icon('graph')} Focus in graph</button>${sourceUrl?`<a class="button" href="${esc(sourceUrl)}" target="_blank" rel="noopener noreferrer">${icon('external')} Repository source</a>`:''}</div></div><div class="detail-body">${warnings.map(w=>`<div class="detail-callout">${esc(typeof w==='string'?w:JSON.stringify(w))}</div>`).join('')}${n.publicLinks?.length?`<section class="detail-section"><h3>Related sources</h3><div class="detail-links">${n.publicLinks.filter(link=>safeUrl(link.url)).map(link=>`<a class="detail-link" href="${esc(safeUrl(link.url))}" target="_blank" rel="noopener noreferrer"><strong>${esc(link.label || 'Source')}</strong>${icon('external')}</a>`).join('')}</div></section>`:''}<div id="claim-fields"></div>${n.statement?'<section class="detail-section"><h3>Statement in the index</h3><pre class="statement-block" id="statement-text"></pre></section>':''}${n.elaboratedType?'<section class="detail-section"><h3>Recorded Lean type <span>Complete elaborated statement</span></h3><pre class="statement-block" id="elaborated-type"></pre></section>':''}<section class="detail-section"><h3>Exact source <span>${source.line?`${count(source.line)}–${count(source.endLine || source.line)}`:''}</span></h3><div class="source-path"><span>${esc(source.path || n.file || 'No source text recorded')}</span><button id="copy-source" class="text-button" ${!source.code?'disabled':''}>${icon('copy')} Copy</button></div><pre class="source-block" id="source-code"></pre><div class="source-tools"><button id="expand-source" class="text-button" hidden>${icon('folder')} Open the whole file</button><p class="source-note" id="source-note"></p></div></section>${n.elaboratedType || data.axioms?.length ? '<section class="detail-section"><h3>Recorded axioms</h3><div id="axiom-list" class="axiom-list"></div><p>These assumptions belong to the recorded compiled result.</p></section>':''}${data.assumptions?.length?'<section class="detail-section"><h3>Additional assumptions</h3><div id="assumptions-list"></div></section>':''}<section class="detail-section"><h3>Outgoing links <span>${count(data.dependencies?.length)}</span></h3><div id="dependency-list" class="detail-links"></div></section><section class="detail-section"><h3>Incoming links <span>${count(data.dependents?.length)}</span></h3><div id="dependent-list" class="detail-links"></div></section><section class="detail-section"><h3>Paper scopes <span>${count(data.papers?.length)}</span></h3><div id="detail-paper-list" class="detail-links"></div></section><section class="detail-section"><h3>Link evidence</h3><div id="detail-evidence"></div></section>${data.recordedEvidence && Object.keys(data.recordedEvidence).length ? '<details class="detail-section"><summary>Recorded evidence fields</summary><pre class="detail-json" id="recorded-evidence"></pre></details>':''}</div>`;
    if($('#statement-text'))$('#statement-text').textContent=n.statement;
    if($('#elaborated-type'))$('#elaborated-type').textContent=n.elaboratedType;
    const wholeFile=['module','file','paper'].includes(n.kind);renderSource(source,null);
    const expand=$('#expand-source');if(expand){const canExpand=!wholeFile&&!!(n.fileId||source.id)&&!!source.code;expand.hidden=!canExpand;expand.onclick=()=>openWholeFile(n,source);}
    renderClaimFields(data);
    if($('#axiom-list'))$('#axiom-list').innerHTML=data.axioms?.length?data.axioms.map(a=>`<span>${esc(typeof a==='string'?a:JSON.stringify(a))}</span>`).join(''):'<span>No axioms listed in this record</span>';
    if($('#assumptions-list'))$('#assumptions-list').innerHTML=data.assumptions.map(a=>`<p>${esc(typeof a==='string'?a:JSON.stringify(a))}</p>`).join('');
    if($('#recorded-evidence')){const r={...data.recordedEvidence};delete r.type;$('#recorded-evidence').textContent=JSON.stringify(r,null,2);}
    renderRelated($('#dependency-list'),data.dependencies || []);renderRelated($('#dependent-list'),data.dependents || []);
    $('#detail-paper-list').innerHTML=data.papers?.length?data.papers.map(p=>`<button class="detail-link" data-detail-paper="${esc(p.id)}"><div><strong>${esc(p.title)}</strong><small>${count(p.resultCount)} results · ${count(p.declarationCount)} declarations</small></div>${icon('arrow')}</button>`).join(''):'<div class="detail-empty">No paper scope is recorded for this item.</div>';
    $$('[data-detail-paper]').forEach(el=>el.onclick=()=>{state.paperIds=[el.dataset.detailPaper];state.view='graph';state.level='declaration';state.focus='';closeDetail({replace:true});renderPapers();loadView();});
    $('#detail-evidence').innerHTML=data.evidence?.length?data.evidence.map(e=>`<p>${esc(typeof e==='string'?e:JSON.stringify(e))}</p>`).join(''):'<p class="detail-empty">No link evidence is attached to this record.</p>';
    $('#close-detail').onclick=closeDetail;$('#close-detail').focus();
    $('#focus-node').onclick=()=>{state.focus=n.kind==='paper'?'':n.id;state.view='graph';state.level=['module','file'].includes(n.kind)?'module':'declaration';if(n.kind==='paper'){state.paperIds=[n.id];renderPapers();}closeDetail({replace:true});loadView();};
    $('#copy-source').onclick=()=>copyText(source.code || '','Source text copied.');$('#copy-node-link').onclick=()=>copyText(location.href,'Record link copied.');
    $('#save-node').onclick=()=>{if(bookmarks.some(b=>b.id===n.id))bookmarks=bookmarks.filter(b=>b.id!==n.id);else bookmarks.push({id:n.id,label:n.label||n.name});saveBookmarks();const active=bookmarks.some(b=>b.id===n.id);$('#save-node').innerHTML=icon(active?'check':'bookmark');$('#save-node').setAttribute('aria-pressed',String(active));showToast(active?'Record saved.':'Saved record removed.');};
    $('#widen-panel').onclick=()=>setPanelWidth(!$('#detail-panel').classList.contains('wide'));let wide=false;try{wide=localStorage.getItem('boundary-atlas-wide')==='1';}catch{}setPanelWidth(wide);
    renderAtlasNote(data);
    $('#detail-panel').scrollTop=0;
  }
  /* The claim-index entry behind a paper result: the heading, the recorded status, the Lean result, the conditions and the modules. */
  function renderClaimFields(data) {
    const box=$('#claim-fields');if(!box)return;const rows=Array.isArray(data.claimIndexes)?data.claimIndexes:[];const section=data.section||'';
    if(!rows.length&&!section){box.innerHTML='';return;}
    box.innerHTML=`<section class="detail-section"><h3>Claim index record <span>${rows.length?`${count(rows.length)} ${rows.length===1?'entry':'entries'}`:''}</span></h3>${section?`<p class="source-note">Section of the paper: ${esc(section)}</p>`:''}${rows.map(r=>`<dl class="claim-fields">${r.heading?`<dt>Entry</dt><dd><strong>${esc(r.heading)}</strong>${r.recordedStatus?` · recorded ${esc(r.recordedStatus)}`:''}</dd>`:''}${r.leanResult?`<dt>Lean establishes</dt><dd>${esc(r.leanResult)}</dd>`:''}${r.conditions?`<dt>Conditions</dt><dd>${esc(r.conditions)}</dd>`:''}${r.modules?.length?`<dt>Modules</dt><dd>${r.modules.map(m=>`<code>${esc(m)}</code>`).join(', ')}</dd>`:''}</dl>`).join('')}</section>`;
  }
  /* The whole text of the record, one row per line, with Lean colors for .lean files and the record's own lines marked. */
  function renderSource(source,mark) {
    const code=$('#source-code');if(!code)return;code.replaceChildren();
    if(!source.code){code.textContent='No source text is recorded for this item.';code.classList.remove('lean');return;}
    const lines=String(source.code).split('\n'),first=Number(source.line)||1;
    const lean=!!(window.LeanHighlight&&window.LeanHighlight.isLean(source.path));
    const colored=lean?window.LeanHighlight.highlight(source.code):null;
    const markStart=Number(mark?.start)||0,markEnd=Number(mark?.end)||markStart;
    const fragment=document.createDocumentFragment();
    lines.forEach((text,i)=>{const n=first+i;const row=document.createElement('span');row.className='source-line'+(markStart&&n>=markStart&&n<=markEnd?' marked':'');row.dataset.line=String(n);const number=document.createElement('span');number.className='line-number';number.textContent=String(n);number.setAttribute('aria-hidden','true');const body=document.createElement('span');body.className='line-text';if(colored)body.innerHTML=colored[i]||'';else body.textContent=text;row.append(number,body);fragment.append(row);});
    code.append(fragment);code.classList.toggle('lean',lean);
    const note=$('#source-note');if(note)note.textContent=`${count(lines.length)} lines${lean?' · Lean colors by token':''}${markStart?` · lines ${count(markStart)} to ${count(markEnd)} are the record`:''}`;
    if(mark?.scroll&&markStart){const row=code.querySelector(`[data-line="${markStart}"]`);if(row)requestAnimationFrame(()=>row.scrollIntoView({block:'center'}));}
  }
  /* A declaration record shows its own lines first; this fetches the complete file around it. */
  async function openWholeFile(n,source) {
    const button=$('#expand-source');if(button){button.disabled=true;button.textContent='Reading the whole file';}
    try{const whole=await api('source',{id:n.fileId||source.id||''});renderSource({...whole,url:source.url},{start:Number(n.line)||0,end:Number(n.endLine)||0,scroll:true});if(button)button.hidden=true;$('#copy-source').onclick=()=>copyText(whole.code||'','Source text copied.');}
    catch(e){showToast(e.message);if(button){button.disabled=false;button.textContent='Open the whole file';}}
  }
  function setPanelWidth(wide) {
    $('#detail-panel').classList.toggle('wide',wide);try{localStorage.setItem('boundary-atlas-wide',wide?'1':'');}catch{}
    const b=$('#widen-panel');if(b){b.setAttribute('aria-pressed',String(wide));b.setAttribute('aria-label',wide?'Narrow the record panel':'Widen the record panel');b.innerHTML=icon(wide?'fit':'expand');}
  }
  function renderRelated(container,records,limit=40) {
    if(!records.length){container.innerHTML='<div class="detail-empty">No links recorded in this direction.</div>';return;}
    container.innerHTML=records.slice(0,limit).map(n=>`<button class="detail-link" data-node="${esc(n.id)}"><div><strong>${esc(n.label || n.name)}</strong><small>${esc(relationLabels[n.edgeKind] || human(n.edgeKind))} · ${esc(statusLabels[n.status] || human(n.status))}</small></div>${icon('arrow')}</button>`).join('');
    bindNodes(container);if(records.length>limit){const b=document.createElement('button');b.className='text-button';b.textContent=`Show all ${count(records.length)} links`;b.onclick=()=>renderRelated(container,records,records.length);container.append(b);}
  }
  async function copyText(text,message) {
    try { await navigator.clipboard.writeText(text);showToast(message); }
    catch { const area=document.createElement('textarea');area.value=text;area.style.position='fixed';area.style.left='-9999px';document.body.append(area);area.select();const ok=document.execCommand('copy');area.remove();showToast(ok?message:'Clipboard access is unavailable. The text remains visible in the source panel.'); }
  }
  async function exportSelection() {
    const button=$('#export-button');button.disabled=true;
    try{const p=new URLSearchParams({...scope(),format:'json'});const r=await fetch(`/api/export?${p}`);if(!r.ok)throw new Error('The export did not complete.');const blob=await r.blob();const url=URL.createObjectURL(blob);const a=document.createElement('a');a.href=url;a.download='boundary-atlas-selection.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1500);showToast('The selected source records were exported.');}catch(e){showToast(e.message);}finally{button.disabled=false;}
  }
  class ProofGraph {
    constructor(canvas) {
      this.canvas=canvas;this.ctx=canvas.getContext('2d');this.nodes=[];this.edges=[];this.positions=new Map();this.camera={x:0,y:0,k:1};this.width=1;this.height=1;this.hover=null;this.drag=null;this.frame=0;this.drawFrame=0;this.iteration=0;this.cameraTouched=false;this.layout='force';this.reduced=matchMedia('(prefers-reduced-motion: reduce)').matches;
      new ResizeObserver(()=>this.resize()).observe(canvas.parentElement);
      canvas.addEventListener('wheel',e=>{e.preventDefault();const p=this.pointer(e);this.zoom(Math.exp(-e.deltaY*.001),p.x,p.y);},{passive:false});
      canvas.addEventListener('pointerdown',e=>{const p=this.pointer(e);this.drag={x:p.x,y:p.y,ox:this.camera.x,oy:this.camera.y,moved:false,node:this.hit(p)};canvas.setPointerCapture(e.pointerId);canvas.classList.add('dragging');$('#graph-tooltip').hidden=true;});
      canvas.addEventListener('pointermove',e=>this.move(e));
      canvas.addEventListener('pointerup',e=>{if(this.drag && !this.drag.moved){const n=this.drag.node;if(n)openNode(n.id);}this.drag=null;canvas.classList.remove('dragging');if(canvas.hasPointerCapture(e.pointerId))canvas.releasePointerCapture(e.pointerId);});
      canvas.addEventListener('pointercancel',()=>{this.drag=null;canvas.classList.remove('dragging');});
      canvas.addEventListener('pointerleave',()=>{if(!this.drag){this.hover=null;$('#graph-tooltip').hidden=true;this.draw();}});
      canvas.addEventListener('keydown',e=>{const step=45;let used=true;switch(e.key){case'+':case'=':this.zoom(1.2);break;case'-':this.zoom(.8);break;case'ArrowLeft':this.camera.x+=step;break;case'ArrowRight':this.camera.x-=step;break;case'ArrowUp':this.camera.y+=step;break;case'ArrowDown':this.camera.y-=step;break;case'f':case'F':this.fit();break;default:used=false;}if(used){e.preventDefault();this.cameraTouched=true;this.draw();}});
    }
    resize() { const r=this.canvas.parentElement.getBoundingClientRect();if(!r.width||!r.height)return;const previousWidth=this.width,previousHeight=this.height,first=this.width<=1;this.width=r.width;this.height=r.height;const dpr=Math.min(devicePixelRatio || 1,2);this.canvas.width=Math.round(this.width*dpr);this.canvas.height=Math.round(this.height*dpr);this.ctx.setTransform(dpr,0,0,dpr,0,0);if(first)this.fit();else{this.camera.x+=(this.width-previousWidth)/2;this.camera.y+=(this.height-previousHeight)/2;this.draw();} }
    pointer(e){const r=this.canvas.getBoundingClientRect();return{x:e.clientX-r.left,y:e.clientY-r.top};}
    setData(data) {
      cancelAnimationFrame(this.frame);this.layout=state.layout;this.iteration=0;this.cameraTouched=false;const old=this.positions;this.nodes=(data.nodes || []).map((n,i)=>({...n,index:i,x:old.get(n.id)?.x || 0,y:old.get(n.id)?.y || 0,vx:0,vy:0,r:n.kind==='paper'?clamp(10+Math.log1p(n.degree || 0)*2,11,25):clamp(3.8+Math.log1p(n.degree || 0)*.7,4,10),color:nodeColor(n)}));
      this.byId=new Map(this.nodes.map(n=>[n.id,n]));this.edges=(data.edges || []).filter(e=>this.byId.has(e.source)&&this.byId.has(e.target)).map(e=>({...e,a:this.byId.get(e.source),b:this.byId.get(e.target)}));this.neighbors=new Map(this.nodes.map(n=>[n.id,new Set()]));this.edges.forEach(e=>{this.neighbors.get(e.source).add(e.target);this.neighbors.get(e.target).add(e.source);});
      this.place();this.positions=new Map(this.nodes.map(n=>[n.id,n]));this.fit();this.hover=null;
      if(this.layout==='force'&&this.nodes.length>1&&this.nodes.length<=800&&this.edges.length<=12000&&!this.reduced)this.animate();else this.draw();
    }
    place() {
      this.groups=null;const n=this.nodes.length;if(!n)return;
      const radius=Math.max(130,Math.sqrt(n)*35);
      if(this.layout==='hierarchical'){
        const levels=new Map(this.nodes.map(x=>[x.id,0]));for(let step=0;step<8;step++){let changed=false;for(const e of this.edges){const a=levels.get(e.source),b=levels.get(e.target);if(a<=b&&b<7){levels.set(e.source,b+1);changed=true;}}if(!changed)break;}
        const groups=new Map();for(const node of this.nodes){const l=levels.get(node.id);if(!groups.has(l))groups.set(l,[]);groups.get(l).push(node);}
        for(const [level,nodes] of [...groups.entries()].sort((a,b)=>a[0]-b[0]))nodes.forEach((node,i)=>{node.x=(i-(nodes.length-1)/2)*(n<80?150:55);node.y=(level-3)*120;});return;
      }
      if(this.layout==='radial'){
        const ordered=[...this.nodes].sort((a,b)=>(b.degree||0)-(a.degree||0));let offset=0,ring=0;while(offset<n){const size=ring===0?1:Math.min(n-offset,Math.max(8,ring*12));for(let j=0;j<size;j++){const node=ordered[offset+j],angle=j/size*Math.PI*2-Math.PI/2;node.x=Math.cos(angle)*ring*100;node.y=Math.sin(angle)*ring*100;}offset+=size;ring++;}return;
      }
      const clusters=new Map();this.nodes.forEach(node=>{const key=groupKey(node);node.group=key;if(!clusters.has(key))clusters.set(key,[]);clusters.get(key).push(node);});
      let ordered=[...clusters.entries()].sort((a,b)=>b[1].length-a[1].length);
      if(ordered.length>12){const small=ordered.filter(([,nodes])=>nodes.length<3);if(small.length>1){const rest=[].concat(...small.map(([,nodes])=>nodes));rest.forEach(node=>{node.group='other-small';});ordered=[...ordered.filter(([,nodes])=>nodes.length>=3),['other-small',rest]];}}
      this.groups=ordered.map(([key,nodes],i)=>({key,title:key==='other-small'?'Other folders':groupTitle(key),nodes,color:palette[i%palette.length]}));
      let ci=0;for(const [,nodes]of ordered){const ca=ci/ordered.length*Math.PI*2;const cr=ordered.length>1?radius*(ordered.length>6?.95:.65):0;nodes.forEach((node,i)=>{const a=i*2.3999632297;const r=Math.sqrt(i+1)*24;node.x=Math.cos(ca)*cr+Math.cos(a)*r;node.y=Math.sin(ca)*cr+Math.sin(a)*r;node.cx=Math.cos(ca)*cr;node.cy=Math.sin(ca)*cr;});ci++;}
    }
    animate() { const batch=this.nodes.length>800?2:5;for(let i=0;i<batch;i++)this.tick();this.draw();if(this.iteration<180)this.frame=requestAnimationFrame(()=>this.animate());else if (!this.cameraTouched) this.fit(); }
    tick() {
      this.iteration++;const alpha=Math.max(.02,1-this.iteration/195),nodes=this.nodes,n=nodes.length,cellSize=110,grid=new Map();
      for(const node of nodes){const k=`${Math.floor(node.x/cellSize)},${Math.floor(node.y/cellSize)}`;if(!grid.has(k))grid.set(k,[]);grid.get(k).push(node);node.vx+=(node.cx-node.x)*.0009*alpha;node.vy+=(node.cy-node.y)*.0009*alpha;}
      for(const a of nodes){const gx=Math.floor(a.x/cellSize),gy=Math.floor(a.y/cellSize);for(let dx=-1;dx<=1;dx++)for(let dy=-1;dy<=1;dy++){const peers=grid.get(`${gx+dx},${gy+dy}`)||[];for(const b of peers){if(a.index>=b.index)continue;let x=a.x-b.x,y=a.y-b.y,d2=x*x+y*y;if(d2<.1){x=.1*(a.index+1);y=.1;d2=x*x+y*y;}const force=Math.min(3,950/d2)*alpha,d=Math.sqrt(d2);a.vx+=x/d*force;a.vy+=y/d*force;b.vx-=x/d*force;b.vy-=y/d*force;}}}
      for(const e of this.edges){const dx=e.b.x-e.a.x,dy=e.b.y-e.a.y,d=Math.sqrt(dx*dx+dy*dy)||1,target=e.a.kind==='paper'?145:65;const strength=.012/(1+Math.log1p(Math.max(e.a.degree||0,e.b.degree||0))*.4);const f=(d-target)*strength*alpha;e.a.vx+=dx/d*f;e.a.vy+=dy/d*f;e.b.vx-=dx/d*f;e.b.vy-=dy/d*f;}
      for(const node of nodes){node.vx*=.75;node.vy*=.75;node.x+=clamp(node.vx,-8,8);node.y+=clamp(node.vy,-8,8);}
    }
    hull(points) { const pts=points.slice().sort((a,b)=>a.x-b.x||a.y-b.y);if(pts.length<3)return pts;const cross=(o,a,b)=>(a.x-o.x)*(b.y-o.y)-(a.y-o.y)*(b.x-o.x);const lower=[];for(const p of pts){while(lower.length>=2&&cross(lower[lower.length-2],lower[lower.length-1],p)<=0)lower.pop();lower.push(p);}const upper=[];for(let i=pts.length-1;i>=0;i--){const p=pts[i];while(upper.length>=2&&cross(upper[upper.length-2],upper[upper.length-1],p)<=0)upper.pop();upper.push(p);}upper.pop();lower.pop();return lower.concat(upper); }
    /* One outlined region and one title per group, drawn under the links. */
    drawGroups(ctx,k) {
      if(this.layout!=='force'||!this.groups||this.groups.length<2||this.groups.length>16)return;
      const pad=30;
      for(const g of this.groups){
        if(!g.nodes.length)continue;const cx=g.nodes.reduce((s,n)=>s+n.x,0)/g.nodes.length,cy=g.nodes.reduce((s,n)=>s+n.y,0)/g.nodes.length;let top=Infinity;ctx.beginPath();
        if(g.nodes.length<3){const r=Math.max(...g.nodes.map(n=>Math.hypot(n.x-cx,n.y-cy)))+pad;ctx.arc(cx,cy,r,0,Math.PI*2);top=cy-r;}
        else{const pts=this.hull(g.nodes.map(n=>({x:n.x,y:n.y})));pts.forEach((p,i)=>{const dx=p.x-cx,dy=p.y-cy,d=Math.hypot(dx,dy)||1;const x=p.x+dx/d*pad,y=p.y+dy/d*pad;top=Math.min(top,y);if(i)ctx.lineTo(x,y);else ctx.moveTo(x,y);});ctx.closePath();}
        ctx.globalAlpha=1;ctx.fillStyle=g.color+'12';ctx.strokeStyle=g.color+'70';ctx.lineWidth=1/k;ctx.setLineDash([5/k,4/k]);ctx.fill();ctx.stroke();ctx.setLineDash([]);
        const label=`${g.title} · ${count(g.nodes.length)}`;ctx.font=`650 ${11/k}px system-ui,sans-serif`;ctx.textAlign='center';ctx.textBaseline='bottom';const w=ctx.measureText(label).width,y=top-6/k;ctx.fillStyle='#fafbf5e8';ctx.fillRect(cx-w/2-6/k,y-14/k,w+12/k,16/k);ctx.fillStyle=g.color;ctx.fillText(label,cx,y);
      }
    }
    fit() {
      if(!this.nodes.length){this.camera={x:this.width/2,y:this.height/2,k:1};this.draw();return;}
      let minX=Infinity,maxX=-Infinity,minY=Infinity,maxY=-Infinity;for(const n of this.nodes){minX=Math.min(minX,n.x-n.r-45);maxX=Math.max(maxX,n.x+n.r+45);minY=Math.min(minY,n.y-n.r-30);maxY=Math.max(maxY,n.y+n.r+35);}
      const k=clamp(Math.min((this.width-70)/Math.max(1,maxX-minX),(this.height-100)/Math.max(1,maxY-minY)),.05,1.55);this.camera={x:this.width/2-(minX+maxX)/2*k,y:this.height/2-(minY+maxY)/2*k,k};this.draw();
    }
    zoom(factor,x=this.width/2,y=this.height/2) { this.cameraTouched=true;const old=this.camera.k,k=clamp(old*factor,.025,8);this.camera.x=x-(x-this.camera.x)*k/old;this.camera.y=y-(y-this.camera.y)*k/old;this.camera.k=k;this.draw(); }
    hit(p) {const wx=(p.x-this.camera.x)/this.camera.k,wy=(p.y-this.camera.y)/this.camera.k;for(let i=this.nodes.length-1;i>=0;i--){const n=this.nodes[i];if(Math.hypot(n.x-wx,n.y-wy)<Math.max(n.r+4,8/this.camera.k))return n;}return null;}
    move(e) {
      const p=this.pointer(e);if(this.drag){const dx=p.x-this.drag.x,dy=p.y-this.drag.y;if(Math.hypot(dx,dy)>4){this.drag.moved=true;this.cameraTouched=true;}this.camera.x=this.drag.ox+dx;this.camera.y=this.drag.oy+dy;this.draw();return;}
      const n=this.hit(p);this.canvas.style.cursor=n?'pointer':'grab';if(n?.id!==this.hover?.id){this.hover=n;this.draw();}
      const tip=$('#graph-tooltip');tip.hidden=!n;if(n){tip.replaceChildren();const strong=document.createElement('strong');strong.textContent=n.label||n.name;const span=document.createElement('span');span.textContent=`${human(n.kind)} · ${statusLabels[n.status] || human(n.status)} · ${count(n.degree)} links${n.group&&this.groups&&this.groups.length>1?` · group: ${groupTitle(n.group)}`:''}`;tip.append(strong,span);tip.style.left=`${clamp(p.x+15,8,this.width-345)}px`;tip.style.top=`${clamp(p.y+15,8,this.height-85)}px`;}
    }
    draw() {
      if(this.drawFrame)return;
      this.drawFrame=requestAnimationFrame(()=>{this.drawFrame=0;this.drawNow();});
    }
    drawNow() {
      const ctx=this.ctx;if(!ctx)return;ctx.clearRect(0,0,this.width,this.height);if(!this.nodes.length)return;ctx.save();ctx.translate(this.camera.x,this.camera.y);ctx.scale(this.camera.k,this.camera.k);const k=this.camera.k,hover=this.hover,adjacent=hover?this.neighbors.get(hover.id):null;this.drawGroups(ctx,k);
      for(const e of this.edges){const active=hover&&(e.source===hover.id||e.target===hover.id);ctx.globalAlpha=hover?(active?.9:.06):e.kind==='paper_shared'?.24:.18;ctx.strokeStyle=active?'#277b72':e.kind.includes('proof')||e.kind==='recorded_dependency'?'#537a91':'#7d947f';ctx.lineWidth=(active?1.7:clamp(Math.log1p(e.weight||1)*.4,.6,2.3))/k;ctx.setLineDash(e.kind.includes('reference')||e.kind.includes('anchor')||e.kind==='paper_shared'?[4/k,4/k]:[]);ctx.beginPath();ctx.moveTo(e.a.x,e.a.y);ctx.lineTo(e.b.x,e.b.y);ctx.stroke();
        if(active&&e.kind!=='paper_shared'){const a=Math.atan2(e.b.y-e.a.y,e.b.x-e.a.x),x=e.b.x-Math.cos(a)*(e.b.r+4/k),y=e.b.y-Math.sin(a)*(e.b.r+4/k),r=5/k;ctx.setLineDash([]);ctx.fillStyle='#277b72';ctx.beginPath();ctx.moveTo(x,y);ctx.lineTo(x-Math.cos(a-.5)*r,y-Math.sin(a-.5)*r);ctx.lineTo(x-Math.cos(a+.5)*r,y-Math.sin(a+.5)*r);ctx.closePath();ctx.fill();}
      }
      ctx.setLineDash([]);for(const node of this.nodes){const active=!hover||node.id===hover.id||adjacent?.has(node.id);ctx.globalAlpha=active?1:.2;const selected=state.focus===node.id; if(node.kind==='paper'||selected||node.id===hover?.id){ctx.beginPath();ctx.arc(node.x,node.y,node.r+6/k,0,Math.PI*2);ctx.fillStyle=node.color;ctx.globalAlpha=active?.09:.02;ctx.fill();ctx.globalAlpha=active?1:.2;}
        ctx.beginPath();ctx.arc(node.x,node.y,node.r,0,Math.PI*2);ctx.fillStyle=node.color;ctx.fill();ctx.strokeStyle='#fffefa';ctx.lineWidth=1.5/k;ctx.stroke();if(selected){ctx.beginPath();ctx.arc(node.x,node.y,node.r+5/k,0,Math.PI*2);ctx.strokeStyle='#183f43';ctx.lineWidth=1.2/k;ctx.stroke();}
        const labelVisible=node.kind==='paper'||node.id===hover?.id||selected||(this.nodes.length<65&&k>.4)||(k>1.6&&node.degree>4);if(labelVisible&&active){const fontSize=node.kind==='paper'?11:9;ctx.font=`${node.kind==='paper'?'600':'500'} ${fontSize/k}px system-ui,sans-serif`;ctx.textAlign='center';ctx.textBaseline='top';const raw=node.kind==='paper'?node.label:shortName(node.label || node.name);const max=node.kind==='paper'?26:35;const label=raw.length>max?raw.slice(0,max-1)+'…':raw;const y=node.y+node.r+7/k,w=ctx.measureText(label).width;ctx.fillStyle='#fafbf5ed';ctx.fillRect(node.x-w/2-3/k,y-1/k,w+6/k,(fontSize+4)/k);ctx.fillStyle='#23453e';ctx.fillText(label,node.x,y);if(node.kind==='paper'){ctx.font=`400 ${8/k}px system-ui,sans-serif`;ctx.fillStyle='#7d9184';ctx.fillText(`${count(node.resultCount)} results`,node.x,y+15/k);}}
      }ctx.restore();ctx.globalAlpha=1;
    }
  }
  const graph=new ProofGraph($('#proof-canvas'));window.atlasGraph=graph;
  function attachEvents() {
    $$('.tab').forEach(el=>el.onclick=()=>setView(el.dataset.view));
    $$('[data-level]').forEach(el=>el.onclick=()=>{state.level=el.dataset.level;state.focus='';loadView();});
    $('#paper-search').oninput=renderPapers;
    $('#select-all').onclick=()=>{state.paperIds=null;state.focus='';state.page=1;renderPapers();loadView();};
    $('#clear-papers').onclick=()=>{state.paperIds=[];state.focus='';state.page=1;renderPapers();loadView();};
    $('#match-mode').onchange=e=>{state.match=e.target.value;state.page=1;loadView();};
    $('#global-search').oninput=e=>{clearTimeout(searchTimer);state.q=e.target.value;searchTimer=setTimeout(()=>{if(state.view!=='files')state.view='results';state.page=1;loadView();},240);};
    $('#graph-layout').onchange=e=>{state.layout=e.target.value;writeUrl();if(graphData)graph.setData(graphData);};
    $('#graph-limit').onchange=e=>{state.limit=Number(e.target.value);loadView();};
    $('#graph-depth').onchange=e=>{state.depth=Number(e.target.value);loadView();};
    $('#graph-direction').onchange=e=>{state.direction=e.target.value;loadView();};
    $('#clear-focus').onclick=()=>{state.focus='';loadView();};
    $('#edge-filter-toggle').onclick=()=>{const panel=$('#edge-filter-panel');panel.hidden=!panel.hidden;$('#edge-filter-toggle').setAttribute('aria-expanded',String(!panel.hidden));};
    $('#graph-list-toggle').onclick=()=>setGraphList(!state.list);
    $('#result-kind').onchange=e=>{state.kind=e.target.value;state.page=1;loadView();};
    $('#result-status').onchange=e=>{state.status=e.target.value;state.page=1;loadView();};
    $('#exact-search').onchange=e=>{state.exact=e.target.checked;state.page=1;loadView();};
    $$('[data-sort]').forEach(el=>el.onclick=()=>{const s=el.dataset.sort;state.order=state.sort===s&&state.order==='asc'?'desc':'asc';state.sort=s;state.page=1;loadView();});
    $$('[data-file-sort]').forEach(el=>el.onclick=()=>{const s=el.dataset.fileSort;state.fileOrder=state.fileSort===s&&state.fileOrder==='asc'?'desc':'asc';state.fileSort=s;state.page=1;loadView();});
    $('#zoom-in').onclick=()=>graph.zoom(1.25);$('#zoom-out').onclick=()=>graph.zoom(.8);$('#fit-graph').onclick=()=>graph.fit();
    $('#fullscreen-graph').onclick=async()=>{try{if(document.fullscreenElement)await document.exitFullscreen();else await $('#graph-stage').requestFullscreen();}catch{showToast('Fullscreen view is unavailable in this browser.');}};
    $('#detail-backdrop').onclick=closeDetail;
    $('#evidence-view-button').onclick=()=>setView('coverage');
    $('#help-button').onclick=()=>$('#guide-dialog').showModal();$('#close-guide').onclick=()=>$('#guide-dialog').close();
    $('#guide-dialog').onclick=e=>{if(e.target===$('#guide-dialog')){const r=e.target.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)e.target.close();}};
    $('#share-button').onclick=()=>{writeUrl();copyText(location.href,'Current view link copied.');};
    $('#export-button').onclick=exportSelection;$('#reload-button').onclick=boot;
    $('#bookmark-toggle').onclick=()=>{const list=$('#bookmark-list');list.hidden=!list.hidden;$('#bookmark-toggle').setAttribute('aria-expanded',String(!list.hidden));};
    $('#sidebar-toggle').onclick=()=>{const open=$('#sidebar').classList.toggle('open');$('#sidebar-toggle').setAttribute('aria-expanded',String(open));};
    document.addEventListener('click',e=>{if(innerWidth<=680 && !$('#sidebar').contains(e.target) && !$('#sidebar-toggle').contains(e.target)){$('#sidebar').classList.remove('open');$('#sidebar-toggle').setAttribute('aria-expanded','false');}});
    window.addEventListener('popstate', async () => {
      const p = new URLSearchParams(location.search);
      state.view = ['theories','graph','outline','results','files','coverage'].includes(p.get('view')) ? p.get('view') : 'theories';
      state.level = ['paper','module','declaration'].includes(p.get('level')) ? p.get('level') : 'paper';
      state.paperIds = p.has('papers') ? (p.get('papers')==='__none__'?[]:p.get('papers').split(',').filter(Boolean)) : null;
      state.q=p.get('q') || '';state.match=p.get('match')==='all'?'all':'any';state.focus=p.get('focus') || '';
      state.depth=clamp(Number(p.get('depth')) || 1,1,3);state.direction=['both','in','out'].includes(p.get('direction'))?p.get('direction'):'both';
      state.layout=['force','hierarchical','radial'].includes(p.get('layout'))?p.get('layout'):'force';state.limit=clamp(Number(p.get('limit')) || 240,1,3000);
      state.kind=p.get('kind') || '';state.status=p.get('status') || '';state.exact=p.get('exact')==='1';state.page=1;
      state.relations=p.has('relations')?(p.get('relations')==='__none__'?[]:p.get('relations').split(',').filter(Boolean)):null;
      const node=p.get('node') || '';state.node=node;
      if (!node) closeDetail({fromHistory:true});
      renderPapers();renderRelations();await loadView();
      if (node) openNode(node,{push:false});
    });
    document.addEventListener('keydown',e=>{
      const typing=['INPUT','TEXTAREA','SELECT'].includes(document.activeElement?.tagName);
      if(e.key==='/'&&!typing){e.preventDefault();$('#global-search').focus();}
      if(e.key==='Escape'){if(!$('#detail-panel').hidden)closeDetail();$('#sidebar').classList.remove('open');$('#sidebar-toggle').setAttribute('aria-expanded','false');}
      if(e.key==='Tab'&&!$('#detail-panel').hidden){const focusable=$$('button:not(:disabled),a[href],input,select,[tabindex="0"]',$('#detail-panel')).filter(el=>el.offsetParent!==null);if(!focusable.length)return;const first=focusable[0],last=focusable.at(-1);if(e.shiftKey&&document.activeElement===first){e.preventDefault();last.focus();}else if(!e.shiftKey&&document.activeElement===last){e.preventDefault();first.focus();}}
    });
  }
  /* The theory layer: theories read from the public Lean source, their relationships, the boundary path and the claim grades. */
  const relationStyle={'builds-on':['#5b6e9e','builds on'],'instance-of':['#287e77','instance of'],'generalizes':['#756d9d','generalizes'],'obstructs':['#b4544c','obstructs'],'transfers-to':['#ac8148','transfers to'],'equivalent-to':['#4f8a5b','equivalent to'],'applies-to':['#527e96','applies to']};
  const gradeLabels={'states-the-claim':'Lean states the claim','stronger-than-claim':'Lean proves a stronger form','assembled-from-pieces':'Assembled from several declarations','definition-matches':'Definition matches','weaker-than-claim':'Lean proves a weaker form','partial':'Partly covered','mismatch':'Mismatch','no-lean':'No Lean declaration','external-evidence':'External evidence','unread':'Not graded yet'};
  const gradeColors={'states-the-claim':'#2f7d5b','stronger-than-claim':'#3f8f6b','assembled-from-pieces':'#6da383','definition-matches':'#8fbb9f','weaker-than-claim':'#c79a4b','partial':'#dcb877','mismatch':'#b4544c','no-lean':'#a9b1ad','external-evidence':'#527e96','unread':'#d9ddd8'};
  const clipText=(text,max)=>{const s=String(text||'');return s.length>max?s.slice(0,max-1)+'…':s;};
  const PROGRAM_COLORS=[['#207f79','#e6f2ee'],['#7870a6','#efedf7'],['#af813b','#f8f0e1'],['#4e7290','#e7eef4'],['#b36454','#f7e9e5'],['#5c8a3a','#edf4e6'],['#8a6224','#f5ecdf'],['#3f6f8f','#e5edf3']];
  const programStyle=(data,id)=>{const n=Math.max(0,(data.programs||[]).findIndex(g=>g.id===id));const [c,p]=PROGRAM_COLORS[n%PROGRAM_COLORS.length];return `--pc:${c};--pp:${p}`;};
  const tagSections=root=>root.querySelectorAll('section').forEach(s=>{const h=s.querySelector(':scope > h3');if(h)s.dataset.kind=h.textContent.trim().toLowerCase().replace(/[^a-z]+/g,'-').replace(/^-|-$/g,'');});
  const leanTitle={baseline:'Lean run: baseline axioms only',beyond:'Lean run: axioms beyond the baseline',hole:'Lean run: a sorry remains',stale:'Recorded Lean result is not current: its source, compiled artifact or run receipt is missing or out of date'};
  const chip=r=>r&&r.id?`<button class="decl-chip${r.lean?' lean-'+esc(r.lean):''}" data-node="${esc(r.id)}" title="${esc(r.name)}${r.lean?' · '+esc(leanTitle[r.lean]||r.lean):''}">${esc(shortName(r.name))}</button>`:`<span class="decl-chip muted" title="${esc(r?.name)}">${esc(shortName(r?.name))}</span>`;
  let claimGrades=null;
  async function loadClaimGrades(){ if(!claimGrades){ try{claimGrades=await api('claimgrades');}catch{claimGrades={grades:{}};} } return claimGrades; }
  function claimGradeFor(ref){ return claimGrades?.grades?.[ref.index]?.[String(ref.line)] || null; }
  function bindTheories(root){ $$('[data-theory]',root).forEach(el=>{ if(el.tagName!=='g') el.onclick=()=>openNode('theory:'+el.dataset.theory); }); }
  let atlasFocus='';
  function edgePath(a,b,W,H){
    if(a.x+W<=b.x){const x1=a.x+W,y1=a.y+H/2,x2=b.x-3,y2=b.y+H/2,m=(x1+x2)/2;return `M${x1},${y1} C${m},${y1} ${m},${y2} ${x2},${y2}`;}
    if(b.x+W<=a.x){const x1=a.x,y1=a.y+H/2,x2=b.x+W+3,y2=b.y+H/2,m=(x1+x2)/2;return `M${x1},${y1} C${m},${y1} ${m},${y2} ${x2},${y2}`;}
    const x1=a.x+W,y1=a.y+H/2,x2=b.x+W+3,y2=b.y+H/2,bend=Math.min(90,34+Math.abs(y2-y1)/4);return `M${x1},${y1} C${x1+bend},${y1} ${x2+bend},${y2} ${x2},${y2}`;
  }
  const arrowDefs=()=>Object.entries(relationStyle).map(([k,[c]])=>`<marker id="atlas-arrow-${k}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="${c}"/></marker>`).join('')+'<marker id="atlas-arrow-mixed" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto-start-reverse"><path d="M0,0 L10,5 L0,10 z" fill="#7d8b87"/></marker>';
  function columnLayout(items,levelOf,W,H,GX,GY,PAD,TOP){
    const levels=[...new Set(items.map(levelOf))].sort((a,b)=>a-b);
    const columns=levels.map(l=>items.filter(t=>levelOf(t)===l));
    const rows=Math.max(1,...columns.map(c=>c.length));
    const pos=new Map();
    columns.forEach((c,ci)=>{const offset=(rows-c.length)*(H+GY)/2;c.forEach((t,ri)=>pos.set(t.id,{x:PAD+ci*(W+GX),y:TOP+offset+ri*(H+GY)}));});
    return {pos,levels,width:PAD*2+levels.length*W+Math.max(0,levels.length-1)*GX,height:TOP+PAD+rows*H+(rows-1)*GY};
  }
  function programMapSvg(data){
    const W=270,H=104,GX=90,GY=18,PAD=22,TOP=40;
    const byId=new Map(data.theories.map(t=>[t.id,t]));
    const programOf=new Map();data.programs.forEach(g=>g.theories.forEach(t=>programOf.set(t,g.id)));
    const items=data.programs.map(g=>{const ts=g.theories.map(id=>byId.get(id)).filter(Boolean);const levels=ts.map(t=>t.level).sort((a,b)=>a-b);
      return {id:g.id,g,ts,level:levels.length?levels[Math.floor((levels.length-1)/2)]:0,files:ts.reduce((n,t)=>n+t.fileCount,0),conclusions:ts.reduce((n,t)=>n+t.conclusionCount,0)};});
    const ranks=[...new Set(items.map(i=>i.level))].sort((a,b)=>a-b);const cols=Math.min(4,ranks.length);items.forEach(i=>i.rank=Math.floor(ranks.indexOf(i.level)*cols/ranks.length));
    const {pos,width,height}=columnLayout(items,i=>i.rank,W,H,GX,GY,PAD,TOP);
    const pairs=new Map();
    data.relations.forEach(r=>{const a=programOf.get(r.from),b=programOf.get(r.to);if(!a||!b||a===b)return;const k=a+'|'+b;const e=pairs.get(k)||{a,b,n:0,kinds:{}};e.n++;e.kinds[r.kind]=(e.kinds[r.kind]||0)+1;pairs.set(k,e);});
    const edges=[...pairs.values()].map(e=>{const kinds=Object.entries(e.kinds).sort((x,y)=>y[1]-x[1]);const main=kinds[0][0];const color=kinds.length===1?(relationStyle[main]||['#7d8b87'])[0]:'#7d8b87';
      return `<path class="atlas-edge linked" data-from="${esc(e.a)}" data-to="${esc(e.b)}" d="${edgePath(pos.get(e.a),pos.get(e.b),W,H)}" stroke="${color}" stroke-width="${Math.min(7,1.4+e.n*0.8)}" marker-end="url(#atlas-arrow-${kinds.length===1?esc(main):'mixed'})"><title>${count(e.n)} relationships: ${esc(kinds.map(([k,n])=>`${n} ${(relationStyle[k]||[0,k])[1]}`).join(', '))}</title></path>`;}).join('');
    const nodes=items.map(i=>{const p=pos.get(i.id);const lines=clipText(i.g.summary,150);return `<g class="atlas-node atlas-program" data-program="${esc(i.id)}" transform="translate(${p.x},${p.y})" style="${programStyle(data,i.id)}" tabindex="0" role="button" aria-label="${esc(i.g.name)}"><rect class="box" width="${W}" height="${H}" rx="11"/><rect class="stripe" width="${W}" height="6" rx="3"/><text class="atlas-node-name" x="14" y="26">${esc(clipText(i.g.name,34))}</text><text class="atlas-node-meta" x="14" y="46">${count(i.ts.length)} theories · ${count(i.files)} files · ${count(i.conclusions)} conclusions</text><foreignObject x="14" y="54" width="${W-28}" height="${H-58}"><div xmlns="http://www.w3.org/1999/xhtml" class="atlas-program-summary">${esc(lines)}</div></foreignObject><title>${esc(i.g.summary)}</title></g>`;}).join('');
    return `<svg id="atlas-map" class="program-level" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-label="Map of the research programs and the relationships between them"><defs>${arrowDefs()}</defs><text class="atlas-col" x="${PAD}" y="24">FOUNDATIONS</text><text class="atlas-col" x="${Math.max(PAD,width-PAD-W)}" y="24">STRONGEST CONCLUSIONS</text><g class="atlas-edges">${edges}</g><g class="atlas-nodes">${nodes}</g></svg>`;
  }
  function programFocusSvg(data,pid){
    const W=214,H=64,GX=84,GY=12,PAD=22,TOP=40;
    const g=data.programs.find(x=>x.id===pid);const inside=new Set(g?g.theories:[]);
    const rel=data.relations.filter(r=>inside.has(r.from)||inside.has(r.to));
    const outside=new Set();rel.forEach(r=>{if(!inside.has(r.from))outside.add(r.from);if(!inside.has(r.to))outside.add(r.to);});
    const byId=new Map(data.theories.map(t=>[t.id,t]));
    const own=[...inside].map(id=>byId.get(id)).filter(Boolean);
    const ranks=[...new Set(own.map(t=>t.level))].sort((a,b)=>a-b);
    const cols=Math.min(4,ranks.length);const items=own.map(t=>({...t,rank:Math.floor(ranks.indexOf(t.level)*cols/ranks.length)+1}));
    [...outside].map(id=>byId.get(id)).filter(Boolean).forEach(t=>{const usesIt=rel.some(r=>r.from!==t.id&&r.to===t.id);items.push({...t,rank:usesIt?0:cols+1,external:true});});
    const {pos,width,height}=columnLayout(items,i=>i.rank,W,H,GX,GY,PAD,TOP);
    const edges=rel.map(r=>{const a=pos.get(r.from),b=pos.get(r.to);if(!a||!b)return '';const [color,label]=relationStyle[r.kind]||['#8a9490',r.kind];
      return `<path class="atlas-edge${r.compilerLinked?' linked':''}" data-from="${esc(r.from)}" data-to="${esc(r.to)}" d="${edgePath(a,b,W,H)}" stroke="${color}" marker-end="url(#atlas-arrow-${esc(r.kind)})"${r.kind==='obstructs'?' stroke-dasharray="6 4"':''}><title>${esc(label)}: ${esc(r.statement)}</title></path>`;}).join('');
    const nodes=items.map(t=>{const p=pos.get(t.id);return `<g class="atlas-node${t.external?' external':''}" data-theory="${esc(t.id)}" transform="translate(${p.x},${p.y})" tabindex="0" role="button" aria-label="${esc(t.name)}"><rect width="${W}" height="${H}" rx="9"/><text class="atlas-node-name" x="12" y="25">${esc(clipText(t.name,31))}</text><text class="atlas-node-meta" x="12" y="45">${t.external?'another program':`${count(t.fileCount)} files · ${count(t.conclusionCount)} conclusions`}</text><title>${esc(t.oneLine)}</title></g>`;}).join('');
    return `<svg id="atlas-map" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-label="Theories of one program and their relationships"><defs>${arrowDefs()}</defs><g class="atlas-edges">${edges}</g><g class="atlas-nodes">${nodes}</g></svg>`;
  }
  function mapSvg(data){
    if(data.programs&&data.programs.length){
      if(atlasFocus&&data.programs.some(g=>g.id===atlasFocus))return programFocusSvg(data,atlasFocus);
      return programMapSvg(data);
    }
    const W=214,H=64,GX=84,GY=12,PAD=22,TOP=40;
    const {pos,width,height}=columnLayout(data.theories.map(t=>({...t})),t=>t.level,W,H,GX,GY,PAD,TOP);
    const edges=data.relations.map(r=>{const a=pos.get(r.from),b=pos.get(r.to);if(!a||!b)return '';const [color,label]=relationStyle[r.kind]||['#8a9490',r.kind];return `<path class="atlas-edge" data-from="${esc(r.from)}" data-to="${esc(r.to)}" d="${edgePath(a,b,W,H)}" stroke="${color}" marker-end="url(#atlas-arrow-${esc(r.kind)})"><title>${esc(label)}: ${esc(r.statement)}</title></path>`;}).join('');
    const nodes=data.theories.map(t=>{const p=pos.get(t.id);return `<g class="atlas-node" data-theory="${esc(t.id)}" transform="translate(${p.x},${p.y})" tabindex="0" role="button" aria-label="${esc(t.name)}"><rect width="${W}" height="${H}" rx="9"/><text class="atlas-node-name" x="12" y="25">${esc(clipText(t.name,31))}</text><text class="atlas-node-meta" x="12" y="45">${count(t.fileCount)} files · ${count(t.conclusionCount)} conclusions</text><title>${esc(t.oneLine)}</title></g>`;}).join('');
    return `<svg id="atlas-map" viewBox="0 0 ${width} ${height}" width="${width}" height="${height}" role="img" aria-label="Map of the theories and the relationships between them"><defs>${arrowDefs()}</defs><g class="atlas-edges">${edges}</g><g class="atlas-nodes">${nodes}</g></svg>`;
  }
  function highlightTheory(svg,id){
    if(!svg)return;
    let key=id,attr='theory';
    if(id&&svg.classList.contains('program-level')){attr='program';const g=(currentAtlas?.programs||[]).find(x=>x.id===id||x.theories.includes(id));key=g?g.id:'';}
    svg.classList.toggle('focus',!!key);
    const near=new Set(key?[key]:[]);
    $$('.atlas-edge',svg).forEach(e=>{const hot=!!key&&(e.dataset.from===key||e.dataset.to===key);e.classList.toggle('hot',hot);if(hot){near.add(e.dataset.from);near.add(e.dataset.to);}});
    $$('.atlas-node',svg).forEach(n=>n.classList.toggle('hot',near.has(n.dataset[attr])));
  }
  function theoryCard(t){
    const papers=Object.entries(t.papers||{}),f=t.freshness||{};
    const changed=(f.changed||0)+(f.removed||0);
    const freshness=changed?`<span class="badge stale-compiled">Historical reading · ${count(f.changed)} changed/new files · ${count(f.removed)} removed</span>`:t.reviewed?'<span class="badge source-indexed">Reading matches indexed sources</span>':'<span class="badge source-only">Source catalogue · review not confirmed</span>';
    return `<button class="theory-card" data-theory="${esc(t.id)}"><span class="theory-level">${t.level===0?'Foundation':'Level '+(t.level+1)}</span><strong>${esc(t.name)}</strong>${freshness}<p>${esc(clipText(t.oneLine,220))}</p><small>${count(t.fileCount)} files · ${count(t.conclusionCount)} recorded conclusions${papers.length?' · '+papers.map(([name,n])=>`${count(n)} claims of ${esc(name)}`).join(' · '):''}</small></button>`;
  }
  function theoryGroups(data){
    const sorted=list=>[...list].sort((a,b)=>a.level-b.level||a.name.localeCompare(b.name));
    if(!data.programs||!data.programs.length)return `<div class="theory-cards">${sorted(data.theories).map(theoryCard).join('')}</div>`;
    const byId=new Map(data.theories.map(t=>[t.id,t]));
    return data.programs.map(g=>`<div class="program-group"><h4>${esc(g.name)}</h4><p class="source-note">${esc(g.summary)}</p><div class="theory-cards">${sorted(g.theories.map(id=>byId.get(id)).filter(Boolean)).map(theoryCard).join('')}</div></div>`).join('');
  }
  let currentAtlas=null;
  function drawAtlasMap(view,data){
    const holder=$('#atlas-map-holder',view);if(!holder)return;
    const focus=atlasFocus&&data.programs?.find(g=>g.id===atlasFocus);
    $('#atlas-map-title',view).innerHTML=focus?`<button class="link-button" id="atlas-back">All programs</button> › ${esc(focus.name)}`:(data.programs?.length?'Research programs and their relationships':'Theories and their relationships');
    $('#atlas-map-note',view).textContent=focus?`${focus.summary} Theories of other programs that relate to this one stand at the edges in grey. A theory opens its page.`:(data.programs?.length?'Each card is one research program: a group of theories on one question. A card opens its theories; an arrow carries the number of relationships between two programs in its title.':'A theory opens its page. An arrow points from a theory to the theory it relates to.');
    holder.innerHTML=mapSvg(data);
    const svg=$('#atlas-map',view);
    $$('.atlas-program',svg).forEach(n=>{n.onclick=()=>{atlasFocus=n.dataset.program;drawAtlasMap(view,data);};n.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();atlasFocus=n.dataset.program;drawAtlasMap(view,data);}};n.onmouseenter=()=>highlightTheory(svg,n.dataset.program);n.onmouseleave=()=>highlightTheory(svg,'');});
    $$('.atlas-node[data-theory]',svg).forEach(n=>{n.onmouseenter=()=>highlightTheory(svg,n.dataset.theory);n.onmouseleave=()=>highlightTheory(svg,'');n.onclick=()=>openNode('theory:'+n.dataset.theory);n.onkeydown=e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();openNode('theory:'+n.dataset.theory);}};});
    const back=$('#atlas-back',view);if(back)back.onclick=()=>{atlasFocus='';drawAtlasMap(view,data);};
  }
  const atlasSourceNote=r=>{if(r.currentSnapshot){const date=r.snapshotAt?new Date(r.snapshotAt).toLocaleString():'';return `Current source catalogue${date?` indexed ${date}`:''}. ${count(r.filesRead)} saved file readings match the indexed text; ${count(r.newFiles)} new files and ${count(r.staleFiles)} changed files show current source documentation instead. ${count(r.retiredFiles)} retired paths are excluded. Semantic reading notes are not Lean proof certificates.`;}const p=r.published||{};const when=p.date?new Date(p.date).toLocaleDateString(undefined,{year:'numeric',month:'short',day:'numeric'}):'';
    const model={'muse-spark-1.3-contributor':'Muse Spark 1.3 Contributor'}[r.model]||r.model||'Muse Spark';const effort={xhigh:'extra high reasoning'}[r.effort]||r.effort||'';
    return `Notes by ${model}${effort?` at ${effort}`:''} from the published Lean text${when?` of ${when}`:''}${p.title?` (${p.title})`:''}`
      +`${r.reviewed?.map?`; the thesis, the programs, the path and ${r.reviewed.theories===r.reviewed.of?'every theory page':`${r.reviewed.theories} of ${r.reviewed.of} theory pages`} passed a second reading against the Lean statements`:''}`
      +'. Lean marks and compiler uses come from the local build of the public package.';};
  function renderTheories(data){
    const view=$('#theories-view'),r=data.reading||{};
    const pct=r.filesTotal?Math.round(100*r.filesRead/r.filesTotal):0;
    const reading=`${count(r.filesRead)} of ${count(r.filesTotal)} saved file readings match the current indexed source`;
    if(!data.available){
      view.innerHTML=`<div class="atlas-intro"><div><p class="eyebrow">THEORY MAP</p><h2>The reading of the public formalization is in progress.</h2><p>${esc(reading)}. The theory map appears once the readers finish every file and the theories are drawn from the checked cards. Every other view of the atlas works now.</p><div class="atlas-progress" role="progressbar" aria-valuemin="0" aria-valuemax="100" aria-valuenow="${pct}"><span style="width:${pct}%"></span></div></div></div>`;
      return;
    }
    const papersHtml=Object.entries(data.claims?.grades||{}).map(([stem,counts])=>{const total=Object.values(counts).reduce((a,b)=>a+b,0);const order=data.claims.order||Object.keys(counts);
      return `<div class="claim-paper"><div class="claim-paper-head"><button class="link-button" data-claims="${esc(stem)}">${esc(data.claims.papers[stem]||stem)}</button><small>${count(total)} claims · the list opens with every grade and reason</small></div><div class="claim-bar">${order.filter(g=>counts[g]).map(g=>`<span style="flex:${counts[g]};background:${gradeColors[g]||'#ccc'}" title="${esc(gradeLabels[g]||g)}: ${count(counts[g])}"></span>`).join('')}</div><div class="claim-legend">${order.filter(g=>counts[g]).map(g=>`<span><i style="background:${gradeColors[g]||'#ccc'}"></i>${esc(gradeLabels[g]||g)} ${count(counts[g])}</span>`).join('')}</div></div>`;}).join('');
    view.innerHTML=`<div class="atlas-intro"><div><p class="eyebrow">THEORY MAP · ${count(data.theories.length)} THEORIES · ${count(data.relations.length)} RELATIONSHIPS</p><h2>Thesis</h2><p class="atlas-thesis">${esc(data.thesis)}</p><p class="source-note">${esc(atlasSourceNote(r))}</p></div><div class="outline-counts"><div><strong>${count(r.filesTotal)}</strong>source files indexed</div><div><strong>${count(data.theories.length)}</strong>theories</div><div><strong>${count(Object.values(data.claims?.grades||{}).reduce((a,c)=>a+Object.values(c).reduce((x,y)=>x+y,0),0))}</strong>claim-index entries</div></div></div>
      ${(data.featured||[]).length?`<section class="atlas-section"><h3>Current theorem packages and results</h3><p class="source-note">Exact declarations in this source snapshot. Open a result for its full type, assumptions, source, and recorded proof evidence.</p><div class="theory-grid">${data.featured.map(f=>`<article class="theory-card">${chip({...f,lean:({'lean-baseline':'baseline','stale-compiled':'stale','lean-flagged':'beyond','has-hole':'hole'})[f.status]||''})}<details><summary>Exact Lean statement</summary><pre style="white-space:pre-wrap;overflow-wrap:anywhere">${esc(f.statement)}</pre></details></article>`).join('')}</div></section>`:''}
      <div class="atlas-body"><section class="atlas-map-card"><div class="atlas-map-head"><h3 id="atlas-map-title">Theories and their relationships</h3><div class="atlas-legend">${Object.entries(relationStyle).filter(([k])=>data.relations.some(x=>x.kind===k)).map(([k,[c,l]])=>`<span><i style="background:${c}"></i>${esc(l)}</span>`).join('')}</div></div><div class="atlas-map-scroll" id="atlas-map-holder"></div><p class="source-note" id="atlas-map-note"></p></section>
      <aside class="atlas-path"><h3>The boundary path</h3><p class="source-note">From the foundations to the strongest conclusions, one Lean result per step.</p><ol>${data.path.map(s=>`<li data-path-theory="${esc(s.theory)}"><button class="path-theory" data-theory="${esc(s.theory)}">${esc((data.theories.find(t=>t.id===s.theory)||{}).name||s.theory)}</button><p>${esc(s.statement)}</p><p class="path-significance">${esc(s.significance)}</p>${s.linked===false?'<p class="path-gap">Lean records no use between this theory and the earlier steps.</p>':''}${s.declarationId?chip({name:s.declaration,id:s.declarationId,lean:s.lean}):''}</li>`).join('')}</ol></aside></div>
      <section class="atlas-section"><h3>Theories</h3>${theoryGroups(data)}</section>
      <section class="atlas-section"><h3>Current paper claims and Lean links</h3><p class="source-note">Every entry comes from the current claim index. A saved semantic grade is retained only when its claim text and supplied Lean statements match; changed inputs are marked Not graded yet. Grades and compiler proof evidence are separate.</p><div class="claim-papers">${papersHtml||'<p class="detail-empty">The claim grades are still being read.</p>'}</div></section>
      <p class="atlas-provenance">The catalogue and links follow the current source snapshot. ${esc(reading)}. Historical interpretations are retained only with their provenance; source extraction does not certify a proof.</p>`;
    currentAtlas=data;drawAtlasMap(view,data);
    $$('[data-path-theory]',view).forEach(li=>{li.onmouseenter=()=>highlightTheory($('#atlas-map',view),li.dataset.pathTheory);li.onmouseleave=()=>highlightTheory($('#atlas-map',view),'');});
    $$('[data-claims]',view).forEach(el=>el.onclick=()=>openNode('claims:'+el.dataset.claims));
    bindTheories(view);bindNodes(view);tagSections(view);
  }
  function renderPaperClaims(stem,g){
    const panel=$('#detail-panel');const rows=Object.values(g.grades?.[stem]||{});
    const counts={};rows.forEach(r=>{counts[r.grade]=(counts[r.grade]||0)+1;});
    const order=g.order||Object.keys(counts);
    panel.innerHTML=`<div class="detail-top"><div class="detail-topline"><span class="eyebrow">PAPER CLAIMS IN LEAN · ${count(rows.length)} ENTRIES</span><div class="detail-actions"><button class="icon-button" id="widen-panel" aria-label="Widen the record panel" aria-pressed="false">${icon('expand')}</button><button id="close-detail" class="icon-button" aria-label="Close claim list">${icon('close')}</button></div></div><h2>${esc(g.papers?.[stem]||stem)}</h2><p class="detail-lead">Current public claim-index entries and exact declaration links. A semantic grade is shown only when the saved reading input still matches.</p></div>
      <div class="detail-body theory-page"><div class="claim-legend">${order.filter(k=>counts[k]).map(k=>`<span><i style="background:${gradeColors[k]||'#ccc'}"></i>${esc(gradeLabels[k]||k)} ${count(counts[k])}</span>`).join('')}</div>
      <ul class="theory-claims" style="margin-top:12px">${rows.map(c=>`<li><div><strong>${esc(c.heading)}</strong> <span class="grade grade-${esc(c.grade)}">${esc(gradeLabels[c.grade]||human(c.grade))}</span></div><p>${esc(c.reason)}</p>${c.statement?`<details><summary>Current claim statement</summary><p>${esc(c.statement)}</p>${c.conditions?`<p><strong>Conditions.</strong> ${esc(c.conditions)}</p>`:''}</details>`:''}${c.gap?`<p class="claim-gap">${esc(c.gap)}</p>`:''}<div class="chip-row">${(c.best||[]).map(chip).join('')}</div></li>`).join('')}</ul>
      <p class="atlas-provenance">Saved semantic grades are separate from compiler evidence. Changed claim text or supplied Lean statements invalidate a grade, even when its old line number still exists. The paper remains the statement of record.</p></div>`;
    bindNodes(panel);$('#close-detail').onclick=closeDetail;$('#close-detail').focus();
    $('#widen-panel').onclick=()=>setPanelWidth(!panel.classList.contains('wide'));let wide=false;try{wide=localStorage.getItem('boundary-atlas-wide')==='1';}catch{}setPanelWidth(wide);
    panel.scrollTop=0;
  }
  function renderTheory(t){
    const panel=$('#detail-panel');
    const rel=(r,dir)=>{const [color,label]=relationStyle[r.kind]||['#8a9490',r.kind];const other=dir==='out'?r.to:r.from,otherName=dir==='out'?r.toName:r.fromName;
      return `<div class="theory-rel"><div class="theory-rel-head"><span class="rel-kind" style="--rel:${color}">${dir==='out'?esc(label):esc(otherName)+' '+esc(label)}</span>${dir==='out'?`<button class="link-button" data-theory="${esc(other)}">${esc(otherName)}</button>`:`<span>this theory</span>`}</div><p>${esc(r.statement)}</p><div class="chip-row">${r.evidence.map(chip).join('')}</div></div>`;};
    const byPaper={};(t.claims||[]).forEach(c=>{(byPaper[c.paper]=byPaper[c.paper]||[]).push(c);});
    panel.innerHTML=`<div class="detail-top"><div class="detail-topline"><span class="eyebrow">THEORY · ${count(t.files.length)} FILES · ${count(t.conclusions.length)} CONCLUSIONS</span><div class="detail-actions"><button class="icon-button" id="widen-panel" aria-label="Widen the record panel" aria-pressed="false">${icon('expand')}</button><button class="icon-button" id="copy-node-link" aria-label="Copy theory link">${icon('link')}</button><button id="close-detail" class="icon-button" aria-label="Close theory">${icon('close')}</button></div></div><h2>${esc(t.name)}</h2><p class="detail-lead">${esc(t.oneLine)}</p></div>
      <div class="detail-body theory-page">
        ${t.freshness&&(t.freshness.changed||t.freshness.added||t.freshness.removed)?`<p class="source-note"><strong>Source update:</strong> ${count(t.freshness.changed)} changed or new files and ${count(t.freshness.removed)} removed paths. The claim links and source catalogue below are current; this retained narrative has not been re-reviewed for those changes.</p>`:''}${t.cardReady?`<p class="source-note">${t.reviewed?'Written by Muse Spark from the file notes and the Lean statements, then checked against the Lean statements in a second reading.':'Written by Muse Spark from the file notes and the Lean statements; this page awaits a second reading.'}</p>`:'<p class="detail-empty">The theory card is still being written; the files below carry their checked cards.</p>'}
        ${t.program||Object.keys(t.papers||{}).length?`<p class="theory-meta">${t.program?`Program: <strong>${esc(t.program.name)}</strong>`:''}${Object.keys(t.papers||{}).length?`${t.program?' · ':''}Papers: ${Object.entries(t.papers).map(([name,n])=>`${esc(name)} (${count(n)} claims)`).join(', ')}`:''}</p>`:''}
        ${t.boundary?`<section class="boundary-box"><h3>The boundary in this theory</h3><p>${esc(t.boundary)}</p></section>`:''}
        ${t.summary?`<section><h3>Summary</h3><p>${esc(t.summary)}</p></section>`:''}
        ${t.foundations.length?`<section><h3>Foundations</h3><dl class="foundation-list">${t.foundations.map(f=>`<dt>${chip(f)}</dt><dd>${esc(f.meaning)}</dd>`).join('')}</dl></section>`:''}
        ${t.conclusions.length?`<section><h3>Conclusions</h3><ol class="conclusion-list">${t.conclusions.map(c=>`<li><span class="kind-tag">${esc(human(c.kind))}</span><p>${esc(c.statement)}</p><div class="chip-row">${c.declarations.map(chip).join('')}</div></li>`).join('')}</ol></section>`:''}
        ${t.relationsOut.length||t.relationsIn.length?`<section><h3>Connections</h3>${t.relationsOut.map(r=>rel(r,'out')).join('')}${t.relationsIn.map(r=>rel(r,'in')).join('')}</section>`:''}
        ${Object.keys(byPaper).length?`<section><h3>Current paper claims linked to this theory</h3>${Object.entries(byPaper).map(([paper,rows])=>`<h4>${esc(paper)}</h4><ul class="theory-claims">${rows.map(c=>`<li><div><strong>${esc(c.heading)}</strong> <span class="grade grade-${esc(c.grade)}">${esc(gradeLabels[c.grade]||human(c.grade))}</span></div><p>${esc(c.reason)}</p>${c.statement?`<details><summary>Current claim statement</summary><p>${esc(c.statement)}</p>${c.conditions?`<p><strong>Conditions.</strong> ${esc(c.conditions)}</p>`:''}</details>`:''}${c.gap?`<p class="claim-gap">${esc(c.gap)}</p>`:''}<div class="chip-row">${c.declarations.map(chip).join('')}</div></li>`).join('')}</ul>`).join('')}</section>`:''}
        ${t.openPoints.length?`<section><h3>Conditions and limits</h3><ul class="open-points">${t.openPoints.map(o=>`<li>${esc(o)}</li>`).join('')}</ul></section>`:''}
        ${t.evidencePairs.length?`<section><h3>Compiler-recorded uses across theories</h3><ul class="evidence-pairs">${t.evidencePairs.map(p=>`<li><span>${esc(p.fromName)} → ${esc(p.toName)}</span><small>${count(p.references)} references</small><div class="chip-row">${p.examples.map(([a,b])=>`${chip(a)}<span class="uses">uses</span>${chip(b)}`).join('')}</div></li>`).join('')}</ul></section>`:''}
        <section><h3>Files</h3><div class="theory-files">${t.files.map(f=>`<button class="theory-file" data-node="${esc(f.id)}"><strong>${esc(f.path.split('/').pop())}</strong><small>${esc(f.topic)} · ${esc(human(f.role))}</small><span>${esc(clipText(f.summary,240))}</span></button>`).join('')}</div></section>
        <p class="atlas-provenance">Written by ${esc(t.model||'Muse Spark 1.3 Contributor')} at ${esc(t.effort||'extra-high')} reasoning from the checked cards of the public Lean files. Every Lean name on this page was found by the Lean parser in a public file.</p>
      </div>`;
    bindNodes(panel);bindTheories(panel);tagSections(panel);
    $('#close-detail').onclick=closeDetail;$('#close-detail').focus();
    $('#copy-node-link').onclick=()=>copyText(location.href,'Theory link copied.');
    $('#widen-panel').onclick=()=>setPanelWidth(!panel.classList.contains('wide'));let wide=false;try{wide=localStorage.getItem('boundary-atlas-wide')==='1';}catch{}setPanelWidth(wide);
    panel.scrollTop=0;
  }
  function renderAtlasNote(data){
    const a=data&&data.atlas;if(!a)return;
    const body=$('#detail-panel .detail-body');if(!body)return;
    const box=document.createElement('section');box.className='plain-words';
    const theoryLink=th=>th&&th.id?`<p class="plain-theory">Theory: <button class="link-button" data-theory="${esc(th.id)}">${esc(th.name)}</button></p>`:'';
    if(a.declaration){const d=a.declaration;
      box.innerHTML=`<h3>${d.model==='source-documentation'?'Current source statement':'In plain words'}</h3>${d.plain?`<p>${esc(d.plain)}</p>`:'<p class="detail-empty">The reading of this file lists this declaration among its routine steps; the file summary gives its context.</p>'}${d.role?`<span class="kind-tag">${esc(human(d.role))}</span>`:''}${d.paperReference?`<span class="kind-tag">${esc(d.paperReference)}</span>`:''}${theoryLink(d.theory)}${d.dependsOn?.length?`<div class="chip-row">${d.dependsOn.map(chip).join('')}</div>`:''}<p class="plain-file"><strong>File.</strong> ${esc(d.fileSummary)}</p>`;}
    else if(a.file){const f=a.file;
      box.innerHTML=`<h3>${f.model==='source-documentation'?'Current source documentation':'This file in plain words'}</h3><p>${esc(f.summary)}</p>${f.boundary&&f.boundary!=='none'?`<p class="plain-boundary"><strong>Boundary.</strong> ${esc(f.boundary)}</p>`:''}<p><strong>Conclusion.</strong> ${esc(f.conclusion)}</p>${theoryLink(f.theory)}${f.keyDeclarations?.length?`<h4>Key declarations</h4><ul class="key-decls">${f.keyDeclarations.map(k=>`<li>${chip(k)} <span class="kind-tag">${esc(human(k.role))}</span><p>${esc(k.plain_statement)}</p></li>`).join('')}</ul>`:''}<p class="source-note">${f.model==='source-documentation'?'Extracted from current source comments and declarations, not a new independent proof review.':'Saved reading input matches the current source. Interpretation and compiler evidence remain separate.'}</p>`;}
    else return;
    body.prepend(box);bindNodes(box);bindTheories(box);
  }
  async function boot() {
    claimGrades=null;
    clearError();$('#snapshot-status').textContent='Reading source data';$('#reload-button').disabled=true;
    try{summary=await api('summary');renderProfile(summary);papers=summary.papers || [];if(state.paperIds!==null){const absent=state.paperIds.filter(id=>!papers.some(p=>p.id===id));if(absent.length){state.paperIds=state.paperIds.filter(id=>papers.some(p=>p.id===id));showToast(`${count(absent.length)} saved paper selections are absent from this source index.`);}}renderPapers();renderRelations();renderBookmarks();renderMetrics(summary);$('#evidence-label').textContent=summary.evidence?.label || 'Proof status';$('#evidence-description').textContent=summary.evidence?.details || 'Each link carries its evidence type.';$('#build-date').textContent=buildLine(summary);$('#snapshot-status').textContent=`${count(summary.counts?.files)} source files indexed`;try{await api('atlas');}catch{const tab=$('.tab[data-view="theories"]');if(tab)tab.hidden=true;if(state.view==='theories')state.view='graph';}await loadView();if(state.node)openNode(state.node);}catch(e){showError(e.message);$('#snapshot-status').textContent='Source data unavailable';$('#paper-list').innerHTML='<div class="table-empty">The source collection could not be loaded.</div>';$('#graph-loading').hidden=true;$('#graph-empty').innerHTML='<h3>The source index is unavailable.</h3><p>The retry control reloads the collection. The dashboard requires its generated data or local source service.</p>';$('#graph-empty').hidden=false;$('#retry-request').onclick=boot;}finally{$('#reload-button').disabled=false;}
  }
  async function checkFreshness() {
    if (document.hidden || !summary || checkingFreshness) return;
    checkingFreshness = true;
    try {
      const health = await api('health');
      if (health.generatedAt && health.generatedAt !== summary.generatedAt) {
        const latest = await api('summary');
        summary = latest; papers = latest.papers || []; renderProfile(latest);
        if (state.paperIds !== null) state.paperIds = state.paperIds.filter(id => papers.some(paper => paper.id === id));
        renderPapers(); renderRelations(); renderMetrics(latest);
        $('#evidence-label').textContent = latest.evidence?.label || 'Proof status';
        $('#evidence-description').textContent = latest.evidence?.details || 'Each link carries its evidence type.';
        $('#build-date').textContent = buildLine(latest);
        $('#snapshot-status').textContent = `${count(latest.counts?.files)} source files indexed`;
        const openRecord = state.node;
        await loadView();
        if (openRecord) await openNode(openRecord);
        showToast('The source index changed. The current view has been refreshed.');
      }
    } catch {
      $('#snapshot-status').textContent = 'Last loaded source index retained';
    } finally { checkingFreshness = false; }
  }
  fillIcons();attachEvents();syncControls();renderBookmarks();boot();
  setInterval(checkFreshness, 45000);
  document.addEventListener('visibilitychange', () => { if (!document.hidden) checkFreshness(); });
})();
