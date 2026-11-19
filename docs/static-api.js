(() => {
  'use strict';
  const originalFetch = window.fetch.bind(window);
  const base = new URL('.', document.currentScript.src);
  let loadPromise;
  const sourceCache = new Map();
  const text = value => String(value ?? '');
  const unique = list => [...new Set(list)];
  const list = (params, key) => unique(params.getAll(key).flatMap(value => value.split(',')).map(value => value.trim()).filter(Boolean));
  const number = (params, key, fallback, low, high) => {
    const raw = params.get(key);
    const n = raw === null || raw === '' ? fallback : Number(raw);
    if (!Number.isInteger(n)) throw {status: 400, message: `The ${key} value must be an integer.`};
    return Math.max(low, Math.min(high, n));
  };
  const isDeclaration = node => node.repositoryDeclaration === true;
  const isResult = node => node.kind.startsWith('paper_');
  const anchorKinds = new Set(['source_anchor', 'claim_index_anchor']);
  const compare = (left, right) => text(left).toLowerCase().localeCompare(text(right).toLowerCase(), 'en');
  let corePromise, prefetchStarted = false;
  const getJson = name => originalFetch(new URL(name, base)).then(response => {
    if (!response.ok) throw new Error(`The static index part ${name} could not be loaded.`);
    return response.json();
  });
  // The core file holds the summary, coverage and file list; the nodes, edges and evidence arrive in parts,
  // so the first view needs only the core and the parts load once a view asks for declarations or links.
  async function loadCore() {
    if (!corePromise) corePromise = getJson('static-data.json').catch(error => {corePromise = null; throw error;});
    return corePromise;
  }
  function prefetch() {
    if (prefetchStarted) return;
    prefetchStarted = true;
    const memory = navigator.deviceMemory, saveData = navigator.connection && navigator.connection.saveData;
    if (saveData || (memory && memory < 4)) return;
    setTimeout(() => load().catch(() => {}), 1200);
  }
  async function load() {
    if (!loadPromise) loadPromise = loadCore().then(async core => {
      if (!core.parts) return core;
      const [nodeParts, edgeParts, evidenceParts] = await Promise.all(['nodes', 'edges', 'evidence'].map(key => Promise.all((core.parts[key] || []).map(getJson))));
      const data = {...core, nodes: nodeParts.flat(), edgeRows: edgeParts.flat(), evidenceText: evidenceParts.flat()};
      delete data.parts;
      return data;
    }).then(data => {
      data.byId = new Map(data.nodes.map(node => [node.id, node]));
      data.byFile = new Map(data.files.map(file => [file.id, file]));
      data.modules = new Map(data.nodes.filter(node => ['module', 'file'].includes(node.kind)).map(node => [node.fileId, node]));
      for (let index = 0; index < data.edgeRows.length; index++) {
        const row = data.edgeRows[index];
        data.edgeRows[index] = {source: data.nodes[row[0]].id, target: data.nodes[row[1]].id, kind: data.relationKinds[row[2]], evidence: data.evidenceText[row[3]], file_id: row[4] < 0 ? '' : data.files[row[4]].id, line: row[5]};
      }
      data.edges = data.edgeRows;
      delete data.edgeRows;
      data.out = new Map(); data.incoming = new Map(); data.filePapers = new Map(); data.anchored = new Set();
      for (const node of data.nodes) {
        if (!data.filePapers.has(node.fileId)) data.filePapers.set(node.fileId, new Set());
        for (const paper of node.paperIds) data.filePapers.get(node.fileId).add(paper);
      }
      for (const edge of data.edges) {
        if (!data.out.has(edge.source)) data.out.set(edge.source, []);
        if (!data.incoming.has(edge.target)) data.incoming.set(edge.target, []);
        data.out.get(edge.source).push(edge); data.incoming.get(edge.target).push(edge);
        if (anchorKinds.has(edge.kind) && isDeclaration(data.byId.get(edge.target))) data.anchored.add(edge.source);
      }
      return data;
    }).catch(error => {loadPromise = null; throw error;});
    return loadPromise;
  }
  function inSelection(data, node, params, fileScope = false) {
    const selected = list(params, 'papers');
    if (!selected.length) return true;
    const belongs = paper => node.id === paper || node.paperIds.includes(paper) || (fileScope && data.filePapers.get(node.fileId)?.has(paper));
    return params.get('match') === 'all' ? selected.every(belongs) : selected.some(belongs);
  }
  function nodeFilter(data, node, params) {
    if (!inSelection(data, node, params)) return false;
    const kinds = list(params, 'kind');
    if (kinds.length && !kinds.some(kind => ['declaration', 'declarations', 'lean'].includes(kind) ? isDeclaration(node) : ['result', 'results', 'paper-results', 'paper_result'].includes(kind) ? isResult(node) : node.kind === kind)) return false;
    const statuses = list(params, 'status');
    if (statuses.length && !statuses.includes(node.status)) return false;
    const rawQuery = text(params.get('q')).trim();
    if (rawQuery && params.get('exact') === '1') return node.name === rawQuery || node.label === rawQuery;
    const query = rawQuery.toLowerCase();
    return !query || [node.name, node.label, node.statement, node.module].some(value => text(value).toLowerCase().includes(query));
  }
  function fileList(files, data, params) {
    const field = ['path', 'declarationCount', 'lineCount', 'module', 'kind'].includes(params.get('sort')) ? params.get('sort') : 'path';
    const direction = params.get('order') === 'desc' ? -1 : 1;
    return pager(files.filter(file => fileFilter(data, file, params)).sort((a, b) => direction * (['declarationCount', 'lineCount'].includes(field) ? a[field] - b[field] : compare(a[field], b[field])) || compare(a.path, b.path)).map(file => {const result = {...file}; delete result.sourceFile; return result;}), params);
  }
  function fileFilter(data, file, params) {
    const selected = list(params, 'papers');
    const members = (data && data.filePapers.get(file.id)) || new Set();
    if (selected.length && !(params.get('match') === 'all' ? selected.every(paper => members.has(paper)) : selected.some(paper => members.has(paper)))) return false;
    const query = text(params.get('q')).trim().toLowerCase();
    if (query && ![file.path, file.module].some(value => text(value).toLowerCase().includes(query))) return false;
    return !params.get('kind') || file.kind === params.get('kind');
  }
  function selectedPapers(data, params) {
    const selected = list(params, 'papers');
    return data.summary.papers.filter(paper => !selected.length || selected.includes(paper.id));
  }
  function counts(data, params) {
    const nodes = data.nodes.filter(node => inSelection(data, node, params));
    const ids = new Set(nodes.map(node => node.id));
    const results = nodes.filter(isResult);
    const fileParams = new URLSearchParams();
    for (const key of ['papers', 'match']) for (const value of params.getAll(key)) fileParams.append(key, value);
    const anchored = results.filter(node => data.anchored.has(node.id)).length;
    return {papers: selectedPapers(data, params).length, files: data.files.filter(file => fileFilter(data, file, fileParams)).length,
      declarations: nodes.filter(isDeclaration).length, paperResults: results.length,
      edges: data.edges.reduce((count, edge) => count + (ids.has(edge.source) && ids.has(edge.target) ? 1 : 0), 0),
      anchoredResults: anchored, unmappedResults: results.length - anchored,
      recordedClaims: results.filter(node => node.kind === 'paper_recorded_claim').length,
      manuscriptResults: results.filter(node => node.kind !== 'paper_recorded_claim').length};
  }
  function publicNode(node, statements = true) {
    const result = {...node}; delete result.extra;
    if (!statements) delete result.statement;
    return result;
  }
  function pager(items, params) {
    const page = number(params, 'page', 1, 1, 10000000), size = number(params, 'pageSize', 50, 1, 500);
    return {items: items.slice((page - 1) * size, page * size), total: items.length, page, pageSize: size};
  }
  function search(data, params) {
    const query = text(params.get('q')).trim();
    const field = ['name', 'label', 'kind', 'status', 'module', 'line'].includes(params.get('sort')) ? params.get('sort') : 'name';
    const direction = params.get('order') === 'desc' ? -1 : 1;
    const rank = node => node.name === query || node.label === query ? 0 : node.name.toLowerCase().startsWith(query.toLowerCase()) ? 1 : 2;
    const nodes = data.nodes.filter(node => nodeFilter(data, node, params)).sort((a, b) => (query ? rank(a) - rank(b) : 0) || direction * (field === 'line' ? a.line - b.line : compare(a[field], b[field])) || compare(a.id, b.id));
    const result = pager(nodes, params); result.items = result.items.map(node => publicNode(node)); return result;
  }
  function aggregateEdges(edges) {
    const result = new Map();
    for (const edge of edges) {
      const key = JSON.stringify([edge.source, edge.target, edge.kind]);
      const prior = result.get(key);
      if (prior) { prior.weight += edge.weight || 1; if (text(edge.evidence) < text(prior.evidence)) prior.evidence = edge.evidence; }
      else result.set(key, {source: edge.source, target: edge.target, kind: edge.kind, evidence: edge.evidence || '', weight: edge.weight || 1});
    }
    return [...result.values()];
  }
  function graph(data, params) {
    const level = params.get('level') || 'paper', limit = number(params, 'limit', 240, 1, 3000);
    if (!['paper', 'module', 'declaration'].includes(level)) throw {status: 400, message: 'The graph level must be paper, module, or declaration.'};
    const relationFilter = new Set(list(params, 'relations'));
    if (level === 'paper') {
      const papers = selectedPapers(data, params), selected = new Set(papers.map(paper => paper.id)), pairs = new Map();
      const requested = list(params, 'papers'), sharedByAll = params.get('match') === 'all' && requested.length > 0;
      const evidence = sharedByAll ? 'All selected paper scopes include these source declarations. This edge does not state implication.' : 'Both paper scopes include these source declarations. This edge does not state implication.';
      if (!relationFilter.size || relationFilter.has('paper_shared')) {
        for (const node of data.nodes.filter(isDeclaration)) {
          if (sharedByAll && !requested.every(paper => node.paperIds.includes(paper))) continue;
          const pids = node.paperIds.filter(id => selected.has(id)).sort();
          for (let i = 0; i < pids.length; i++) for (let j = i + 1; j < pids.length; j++) {
            const key = JSON.stringify([pids[i], pids[j]]);
            const edge = pairs.get(key) || {source: pids[i], target: pids[j], kind: 'paper_shared', evidence, weight: 0};
            edge.weight++; pairs.set(key, edge);
          }
        }
      }
      const edges = [...pairs.values()], degree = new Map();
      for (const edge of edges) for (const key of [edge.source, edge.target]) degree.set(key, (degree.get(key) || 0) + edge.weight);
      papers.sort((a, b) => (degree.get(b.id) || 0) - (degree.get(a.id) || 0) || compare(a.title, b.title));
      const nodes = papers.slice(0, limit).map(paper => ({id: paper.id, label: paper.shortTitle, name: paper.title, kind: 'paper', status: paper.status, paperIds: [paper.id], module: '', file: '', line: 1, degree: degree.get(paper.id) || 0, color: paper.color, resultCount: paper.resultCount}));
      const ids = new Set(nodes.map(node => node.id));
      let note = 'Paper links count shared declarations in the source and dependency scopes. The edge weight is the shared declaration count; it is not an implication between theories.';
      if (sharedByAll) note += ' Each link counts only declarations included in every selected paper scope.';
      return {nodes, edges: edges.filter(edge => ids.has(edge.source) && ids.has(edge.target)), totalNodes: papers.length, totalEdges: edges.length, truncated: nodes.length < papers.length, limit, note};
    }
    let candidates = data.nodes.filter(node => inSelection(data, node, params, level === 'module') && (level === 'module' ? ['module', 'file'].includes(node.kind) : !['paper', 'module', 'file', 'section', 'external_module'].includes(node.kind)));
    let ids = new Set(candidates.map(node => node.id));
    function* eligibleEdges() {
      for (const edge of data.edges) {
        if (relationFilter.size && !relationFilter.has(edge.kind)) continue;
        if (level === 'module') {
          const source = data.modules.get(data.byId.get(edge.source).fileId), target = data.modules.get(data.byId.get(edge.target).fileId);
          if (source && target && source.id !== target.id && ids.has(source.id) && ids.has(target.id)) yield {...edge, source: source.id, target: target.id};
        } else if (ids.has(edge.source) && ids.has(edge.target)) yield edge;
      }
    }
    let edges = aggregateEdges(eligibleEdges());
    let focus = params.get('focus') || '';
    if (focus && level === 'module' && !ids.has(focus)) focus = data.modules.get(data.byId.get(focus)?.fileId)?.id || focus;
    if (focus) {
      if (!ids.has(focus)) return {nodes: [], edges: [], totalNodes: 0, totalEdges: 0, truncated: false, limit, note: 'The selected result is outside this graph level or paper selection.'};
      const depth = number(params, 'depth', 1, 0, 8), direction = params.get('direction') || 'both', adjacency = new Map();
      const connect = (a, b) => {if (!adjacency.has(a)) adjacency.set(a, new Set()); adjacency.get(a).add(b);};
      for (const edge of edges) {
        if (['both', 'out', 'dependencies'].includes(direction)) connect(edge.source, edge.target);
        if (['both', 'in', 'dependents'].includes(direction)) connect(edge.target, edge.source);
      }
      ids = new Set([focus]); let frontier = new Set([focus]);
      for (let step = 0; step < depth && frontier.size; step++) {
        const next = new Set();
        for (const id of frontier) for (const child of adjacency.get(id) || []) if (!ids.has(child)) next.add(child);
        for (const id of next) ids.add(id); frontier = next;
      }
      candidates = candidates.filter(node => ids.has(node.id)); edges = edges.filter(edge => ids.has(edge.source) && ids.has(edge.target));
    }
    const degree = new Map();
    for (const edge of edges) for (const id of [edge.source, edge.target]) degree.set(id, (degree.get(id) || 0) + edge.weight);
    candidates.sort((a, b) => (a.id === focus ? 0 : 1) - (b.id === focus ? 0 : 1) || (degree.get(b.id) || 0) - (degree.get(a.id) || 0) || compare(a.id, b.id));
    const nodes = candidates.slice(0, limit).map(node => ({...publicNode(node, false), degree: degree.get(node.id) || 0}));
    const shown = new Set(nodes.map(node => node.id)), truncated = nodes.length < candidates.length;
    let note = level === 'module' ? 'File links group source relationships by file. The link type distinguishes imports, source references, and compiled dependencies.' : 'Arrows point from a result to its dependency or cited source. Each edge retains its own evidence type.';
    if (truncated) note += ` The view displays ${nodes.length.toLocaleString('en-US')} of ${candidates.length.toLocaleString('en-US')} nodes. Search and the file list retain every indexed entry.`;
    return {nodes, edges: edges.filter(edge => shown.has(edge.source) && shown.has(edge.target)), totalNodes: candidates.length, totalEdges: edges.length, truncated, limit, note};
  }
  async function readSource(data, fileId) {
    const file = data.byFile.get(fileId);
    if (!file) throw {status: 404, message: 'The source file is not present in this index.'};
    if (!sourceCache.has(fileId)) sourceCache.set(fileId, originalFetch(new URL(file.sourceFile, base)).then(response => {
      if (!response.ok) throw new Error('The source text could not be loaded.');
      return response.json();
    }).catch(error => {sourceCache.delete(fileId); throw error;}));
    return sourceCache.get(fileId);
  }
  function sourceSlice(source, start, end, url) {
    const lines = source.code.split(/\r\n|\n|\r/); if (lines.at(-1) === '') lines.pop();
    return {path: source.path, line: start, endLine: end, code: lines.slice(start - 1, end).join('\n'), url: url ?? source.url};
  }
  async function nodeDetail(data, id) {
    const sourceFile = data.byFile.get(id);
    let node = data.byId.get(id) || (sourceFile?.kind !== 'claim_index' && data.nodes.find(item => item.fileId === id && ['module', 'paper', 'file'].includes(item.kind)));
    let synthetic = false;
    if (!node && sourceFile) {
      synthetic = true;
      const paperIds = unique([...data.nodes.filter(item => item.fileId === id).flatMap(item => item.paperIds), ...data.edges.filter(edge => edge.file_id === id).flatMap(edge => data.byId.get(edge.source)?.paperIds || [])]);
      node = {id, label: sourceFile.path, name: sourceFile.path, kind: 'file', status: 'source-indexed', paperIds, module: sourceFile.module, file: sourceFile.path, fileId: id, line: 1, endLine: Math.max(1, sourceFile.lineCount), sourceUrl: sourceFile.sourceUrl, degree: 0, statement: '', repositoryDeclaration: false};
      if (node.sourceUrl.includes('github.com/') && !node.sourceUrl.includes('#')) node.sourceUrl += '#L1' + (node.endLine > 1 ? `-L${node.endLine}` : '');
    }
    if (!node) throw {status: 404, message: 'The result is not present in this index.'};
    const out = synthetic ? data.nodes.filter(item => item.fileId === id && item.id !== id).sort((a, b) => a.line - b.line || compare(a.id, b.id)).map(item => ({source: id, target: item.id, kind: 'file_contains', evidence: 'Record appears in this source file', file_id: id, line: item.line})) : data.out.get(node.id) || [], incoming = data.incoming.get(node.id) || [];
    let extra = node.extra || {};
    let source = {path: '', line: 1, endLine: 1, code: '', url: ''};
    if (data.byFile.has(node.fileId)) {
      const raw = await readSource(data, node.fileId), whole = ['module', 'file', 'paper'].includes(node.kind);
      extra = {...extra, ...(raw.nodeDetails?.[node.id] || {})};
      source = sourceSlice(raw, whole ? 1 : node.line, whole ? raw.endLine : node.endLine, node.sourceUrl);
    }
    const evidence = unique([...out, ...incoming].map(edge => edge.evidence).filter(Boolean));
    const warnings = Array.isArray(extra.warnings) ? [...extra.warnings] : extra.warnings ? [extra.warnings] : [];
    if (['source-only', 'source-indexed', 'paper-statement'].includes(node.status)) warnings.push('This status records source content. It does not report a new Lean build or axiom check.');
    if (node.status === 'stale-compiled' || ['source_fresh', 'cache_fresh', 'sourceFresh'].some(key => extra[key] === false)) warnings.push('The compiled record does not match current source or artifact checks. The source link shows the indexed file; the recorded proof evidence needs a fresh check.');
    if (['compiled-flagged', 'recorded-flagged'].includes(node.status)) warnings.push('The recorded compiled declaration carries flagged assumptions. Its complete assumptions remain part of the result.');
    if (node.status === 'recorded-baseline') warnings.push('The recorded compiled declaration retains its complete type and axiom list. Its match to the manuscript remains a separate claim.');
    if (extra.manuscript_available === false) warnings.push('The manuscript source is not in this index. Recorded claim entries remain visible; they do not establish complete manuscript coverage.');
    if (node.status === 'index-record-only') warnings.push('This record comes from the repository claim index. The statement and its recorded status retain that source.');
    if (node.sourceUrl.includes('/blob/main/')) warnings.push('The repository link follows the main branch. The source shown here is the indexed copy from the recorded build time.');
    const compiled = extra.compiled_evidence || extra.compiled;
    if (compiled) evidence.push(typeof compiled === 'string' ? compiled : JSON.stringify(Object.fromEntries(Object.entries(compiled).filter(([key]) => key !== 'type'))));
    let assumptions = extra.assumptions || []; if (typeof assumptions === 'string') assumptions = [assumptions];
    const item = publicNode(node); item.elaboratedType = extra.elaboratedType || compiled?.type || ''; item.sourceCurrent = extra.source_current ?? compiled?.current ?? null; item.graphAvailable = !synthetic;
    return {node: item, source,
      dependencies: out.map(edge => ({...publicNode(data.byId.get(edge.target), false), edgeKind: edge.kind, edgeEvidence: edge.evidence})),
      dependents: incoming.map(edge => ({...publicNode(data.byId.get(edge.source), false), edgeKind: edge.kind, edgeEvidence: edge.evidence})),
      papers: data.summary.papers.filter(paper => node.paperIds.includes(paper.id)), evidence, assumptions, axioms: extra.axioms || compiled?.axioms || [], recordedEvidence: compiled || {}, warnings,
      section: extra.section || '', proof: extra.proof || '', atlas: await atlasNote(node, source.path),
      claimIndexes: (Array.isArray(extra.claim_indexes) ? extra.claim_indexes : []).map(entry => ({heading: entry.heading || '', recordedStatus: entry.recorded_status || '', leanResult: entry.lean_result || '', conditions: entry.conditions || '', modules: Array.isArray(entry.modules) ? entry.modules.map(String) : [], fileId: entry.file_id || '', line: entry.line || 0}))};
  }
  async function outline(data, params) {
    const selected = (params.get('papers') || '').split(',').map(v => v.trim()).filter(v => v && v !== '__none__');
    const papers = data.summary.papers;
    if (!selected.length) return {paper: null, papers, sections: [], totals: {results: 0, anchored: 0, sections: 0}};
    const paper = papers.find(p => p.id === selected[0]);
    if (!paper) throw {status: 404, message: 'The paper is not present in this index.'};
    const results = data.nodes.filter(n => n.kind.startsWith('paper_') && (n.paperIds || []).includes(paper.id)).sort((a, b) => compare(a.fileId, b.fileId) || a.line - b.line || compare(a.id, b.id));
    const details = {}, headings = new Map();
    const headingText = value => value.replace(/\\label\{[^}]*\}?/g, '').replace(/\\\\/g, ' ').replace(/~/g, ' ').replace(/\\[a-zA-Z]+\*?\s*/g, '').replace(/[{}$]/g, '').replace(/\s+/g, ' ').trim();
    for (const fileId of unique(results.map(n => n.fileId).filter(Boolean))) {
      if (!data.byFile.has(fileId)) continue;
      const raw = await readSource(data, fileId);
      Object.assign(details, raw.nodeDetails || {});
      if (data.byFile.get(fileId)?.kind === 'tex') headings.set(fileId, String(raw.code || '').split('\n').map((line, index) => { const match = /^\s*\\section\*?\s*(?:\[[^\]]*\])?\{(.+)\}\s*(?:%.*)?$/.exec(line); return match ? [index + 1, headingText(match[1])] : null; }).filter(Boolean));
    }
    const sections = [], byTitle = new Map();
    let anchored = 0;
    for (const n of results) {
      const extra = {...(n.extra || {}), ...(details[n.id] || {})};
      const entries = (Array.isArray(extra.claim_indexes) ? extra.claim_indexes : []).map(entry => ({heading: entry.heading || '', recordedStatus: entry.recorded_status || '', leanResult: entry.lean_result || '', conditions: entry.conditions || '', modules: Array.isArray(entry.modules) ? entry.modules.map(String) : []}));
      const recorded = n.kind === 'paper_recorded_claim';
      const subsection = extra.section || '';
      let top = '';
      for (const [number, text] of headings.get(n.fileId) || []) { if (number <= (n.line || 0)) top = text; else break; }
      const title = recorded ? 'Claim index records without a manuscript label' : (top || subsection || 'Front matter');
      const names = unique((data.out.get(n.id) || []).filter(e => ['claim_index_anchor', 'source_anchor'].includes(e.kind)).map(e => e.target));
      const modules = unique(entries.flatMap(e => e.modules));
      const item = {id: n.id, kind: n.kind, name: n.name, label: n.label || n.name, line: n.line, endLine: n.endLine, status: n.status, section: title, subsection: subsection && subsection !== title ? subsection : '', hasProof: !!extra.proof,
        recordedStatus: entries[0]?.recordedStatus || '', leanResult: entries[0]?.leanResult || '', conditions: entries[0]?.conditions || '', modules, entryCount: entries.length,
        anchorCount: names.length, anchors: names.slice(0, 24).map(id => data.byId.get(id)).filter(Boolean).map(d => ({id: d.id, label: d.label || d.name, name: d.name, status: d.status, module: d.module}))};
      if (names.length || entries.length) anchored += 1;
      const key = recorded ? '\u0000recorded' : title;
      if (!byTitle.has(key)) { const section = {title, results: [], recorded}; byTitle.set(key, section); sections.push(section); }
      byTitle.get(key).results.push(item);
    }
    sections.sort((a, b) => Number(a.recorded) - Number(b.recorded));
    return {paper, papers, sections, totals: {results: results.length, anchored, sections: sections.filter(s => !s.recorded).length}};
  }
  const atlasCache = new Map();
  async function atlasFile(name, fallback) {
    if (!atlasCache.has(name)) atlasCache.set(name, originalFetch(new URL(name, base)).then(r => r.ok ? r.json() : fallback).catch(() => fallback));
    return atlasCache.get(name);
  }
  async function atlasNote(node, path) {
    if (!path || !path.endsWith('.lean')) return null;
    const cards = await atlasFile('atlas/cards.json', {});
    const card = cards[path];
    if (!card) return null;
    if (['module', 'file'].includes(node.kind)) return {file: card, declaration: null};
    const d = (card.keyDeclarations || []).find(k => k.name === node.name);
    return {file: null, declaration: {theory: card.theory, fileSummary: card.summary, fileTopic: card.topic, role: d ? d.role : '',
      plain: d ? d.plain_statement : '', paperReference: d ? d.paper_reference : '', dependsOn: d ? d.dependsOn : []}};
  }
  async function route(path, params) {
    if (path === '/api/atlas') return atlasFile('atlas/overview.json', {available: false, theories: [], relations: [], path: [], reading: {}, claims: {grades: {}}});
    if (path === '/api/claimgrades') return atlasFile('atlas/claimgrades.json', {grades: {}});
    if (path === '/api/theory') {
      const theory = await atlasFile(`atlas/theory/${encodeURIComponent(params.get('id') || '')}.json`, null);
      if (!theory) throw {status: 404, message: 'The theory is not present in the atlas.'};
      return theory;
    }
    if (path === '/api/filecard') {
      const card = (await atlasFile('atlas/cards.json', {}))[params.get('path') || ''];
      if (!card) throw {status: 404, message: 'The file has no checked card in the atlas.'};
      return card;
    }
    const core = await loadCore();
    prefetch();
    if (!list(params, 'papers').length) {
      // With no paper selection the totals are the export's own totals, so the core answers without the parts.
      if (path === '/api/summary' && core.summary.counts) return {...core.summary, papers: core.summary.papers, counts: core.summary.counts};
      if (path === '/api/coverage' && core.coverage.totals) return {...core.coverage, papers: core.summary.papers, totals: core.coverage.totals};
      if (path === '/api/files') return fileList(core.files, null, params);
      if (path === '/api/health') return {status: 'ok', readOnly: true, static: true, generatedAt: core.summary.generatedAt, nodeCount: core.nodeCount ?? (core.nodes || []).length};
    }
    const data = await load();
    if (path === '/api/outline') return outline(data, params);
    if (path === '/api/summary') return {...data.summary, papers: selectedPapers(data, params), counts: counts(data, params)};
    if (path === '/api/search') return search(data, params);
    if (path === '/api/files') return fileList(data.files, data, params);
    if (path === '/api/graph') return graph(data, params);
    if (path === '/api/node') return nodeDetail(data, params.get('id'));
    if (path === '/api/source') {
      const source = await readSource(data, params.get('id') || params.get('file'));
      const start = number(params, 'line', 1, 1, Math.max(1, source.endLine));
      const end = number(params, 'endLine', source.endLine, start, Math.max(start, source.endLine));
      return {id: source.id, ...sourceSlice(source, start, end)};
    }
    if (path === '/api/coverage') return {...data.coverage, papers: selectedPapers(data, params), totals: counts(data, params)};
    if (path === '/api/health') return {status: 'ok', readOnly: true, static: true, generatedAt: data.summary.generatedAt, nodeCount: data.nodes.length};
    if (path === '/api/export') {
      const nodes = data.nodes.filter(node => nodeFilter(data, node, params)).sort((a, b) => compare(a.kind, b.kind) || compare(a.name, b.name)).map(node => publicNode(node));
      const format = params.get('format') || 'json';
      if (format === 'csv') {
        const columns = ['id', 'kind', 'name', 'label', 'status', 'module', 'file', 'line', 'endLine', 'paperIds', 'sourceUrl', 'statement'];
        const cell = value => {let result = Array.isArray(value) ? value.join(';') : text(value); if (/^[=+\-@\t\r]/.test(result)) result = "'" + result; return '"' + result.replaceAll('"', '""') + '"';};
        return [columns.join(','), ...nodes.map(node => columns.map(key => cell(node[key])).join(','))].join('\r\n') + '\r\n';
      }
      if (format !== 'json') throw {status: 400, message: 'The export format must be json or csv.'};
      const ids = new Set(nodes.map(node => node.id));
      return {generatedAt: data.summary.generatedAt, selection: list(params, 'papers'), counts: counts(data, params), nodes, edges: data.edges.filter(edge => ids.has(edge.source) && ids.has(edge.target))};
    }
    throw {status: 404, message: 'The API route is not present.'};
  }
  window.fetch = async function(input, options = {}) {
    const url = new URL(typeof input === 'string' || input instanceof URL ? input : input.url, window.location.href);
    const apiPosition = url.pathname.indexOf('/api/');
    if (url.origin !== window.location.origin || apiPosition < 0) return originalFetch(input, options);
    if (options.signal?.aborted) throw new DOMException('The request was aborted.', 'AbortError');
    const path = url.pathname.slice(apiPosition), method = text(options.method || (typeof input === 'object' && input.method) || 'GET').toUpperCase();
    if (!['GET', 'HEAD'].includes(method)) return new Response(JSON.stringify({error: 'The dashboard provides read-only requests.'}), {status: 405, headers: {'Content-Type': 'application/json'}});
    try {
      const result = await route(path, url.searchParams);
      if (options.signal?.aborted) throw new DOMException('The request was aborted.', 'AbortError');
      const csv = path === '/api/export' && url.searchParams.get('format') === 'csv';
      return new Response(method === 'HEAD' ? null : csv ? result : JSON.stringify(result), {status: 200, headers: {'Content-Type': csv ? 'text/csv; charset=utf-8' : 'application/json; charset=utf-8'}});
    } catch (error) {
      if (error.name === 'AbortError') throw error;
      return new Response(JSON.stringify({error: error.message || 'The static source index is unavailable.'}), {status: error.status || 503, headers: {'Content-Type': 'application/json'}});
    }
  };
  document.addEventListener('click', async event => {
    const anchor = event.target.closest?.('a[href]');
    if (!anchor) return;
    const url = new URL(anchor.href, window.location.href);
    if (!url.pathname.includes('/api/export') || url.origin !== window.location.origin) return;
    event.preventDefault();
    const response = await window.fetch(url); if (!response.ok) return;
    const blob = await response.blob(), link = document.createElement('a');
    link.href = URL.createObjectURL(blob); link.download = 'proof-index.' + (url.searchParams.get('format') === 'csv' ? 'csv' : 'json'); link.click();
    setTimeout(() => URL.revokeObjectURL(link.href), 1000);
  });
  window.__PROOF_STATIC_API__ = true;
})();
