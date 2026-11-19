/* Lean 4 syntax colors for the source panel. One pass over the text; one HTML string per line. */
(() => {
  'use strict';
  const esc = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  const KEYWORDS = new Set(('import open namespace section end universe variable variables theorem lemma def abbrev instance structure class ' +
    'inductive coinductive axiom axioms opaque constant example where extends deriving with match fun let have show from by do return ' +
    'if then else at calc in using only mutual private protected noncomputable partial unsafe nonrec macro macro_rules syntax elab ' +
    'notation infix infixl infixr prefix postfix attribute local scoped set_option termination_by decreasing_by this exists forall ' +
    'suffices obtain intro intros rintro assume fun λ Π Σ ∀ ∃ export hiding renaming as unif_hint initialize builtin_initialize ' +
    'declare_syntax_cat register_option omit include').split(/\s+/));
  const DECLARATORS = new Set('theorem lemma def abbrev instance structure class inductive coinductive axiom opaque constant macro syntax elab notation example'.split(' '));
  const SCOPES = new Set('namespace section end open import export'.split(' '));
  const TACTICS = new Set(('exact intro intros rintro obtain rcases cases induction simp simp_all simpa rw rwa erw unfold change refine apply ' +
    'constructor use exists exacts specialize subst omega decide linarith nlinarith positivity norm_num ring ring_nf field_simp aesop ' +
    'trivial contradiction exfalso left right split split_ifs funext ext congr gcongr by_contra by_cases push_neg push_cast norm_cast ' +
    'exact_mod_cast assumption tauto simp_rw dsimp delta generalize revert clear rename_i set lift choose nth_rewrite nth_rw conv next ' +
    'case all_goals any_goals first try repeat iterate focus done skip infer_instance filter_upwards measurability continuity fun_prop ' +
    'bound rfl sorry admit native_decide simp_arith interval_cases fin_cases mod_cases absurd injection injections contrapose symm trans ' +
    'calc show_term exists_intro rename apply_fun refine_lift').split(/\s+/));
  const SORTS = new Set(['Type', 'Prop', 'Sort', 'Type*', 'Sort*']);
  const IDENT = /^[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*(?:\.[\p{L}_][\p{L}\p{N}_'!?₀-₉ₐ-ₜ]*)*/u;
  const NUMBER = /^(?:0x[0-9a-fA-F]+|0b[01]+|\d+(?:\.\d+)?(?:e[+-]?\d+)?)/;
  const SYMBOL = /^(?::=|<;>|<\|>|\|>\.|->|<-|=>|==|≠|≤|≥|→|←|↔|⟶|∧|∨|¬|∀|∃|∃!|λ|↦|∘|∑|∏|∫|∈|∉|⊆|⊂|⊇|⊃|∪|∩|∖|∅|⁻¹|•|⊢|▸|∣|≃|≅|≡|≈|⊕|⊗|⊤|⊥|√|∞|×|⟨|⟩|⦃|⦄|‹|›|«|»|⟦|⟧|[+\-*\/=<>|&^%~!?@#$]+)/u;
  const PUNCT = /^[()\[\]{},;:.·]/;

  function span(cls, text) { return cls ? `<span class="lh-${cls}">${esc(text)}</span>` : esc(text); }

  /* Reads the text once. Block comments and strings carry across lines through `state`. */
  function highlight(code) {
    const lines = String(code || '').split('\n');
    const out = new Array(lines.length);
    let state = {block: 0, doc: false, string: false};
    let expectDecl = false;
    let expectScope = false;
    for (let li = 0; li < lines.length; li++) {
      const line = lines[li];
      let i = 0;
      let html = '';
      let attrDepth = 0;
      while (i < line.length) {
        const rest = line.slice(i);
        if (state.block > 0) {
          const open = rest.indexOf('/-'), close = rest.indexOf('-/');
          if (close === -1 && open === -1) { html += span(state.doc ? 'doc' : 'comment', rest); i = line.length; break; }
          if (open !== -1 && (close === -1 || open < close)) { html += span(state.doc ? 'doc' : 'comment', rest.slice(0, open + 2)); state.block++; i += open + 2; continue; }
          html += span(state.doc ? 'doc' : 'comment', rest.slice(0, close + 2)); i += close + 2; state.block--; if (!state.block) state.doc = false; continue;
        }
        if (state.string) {
          const m = /^(?:[^"\\]|\\.)*"/.exec(rest);
          if (m) { html += span('string', m[0]); i += m[0].length; state.string = false; } else { html += span('string', rest); i = line.length; }
          continue;
        }
        const ch = rest[0];
        if (rest.startsWith('/-')) { state.block = 1; state.doc = rest.startsWith('/--') || rest.startsWith('/-!'); const close = rest.indexOf('-/', 2); const inner = close === -1 ? rest : rest.slice(0, close + 2); const nested = (inner.slice(2).match(/\/-/g) || []).length; if (close === -1) { html += span(state.doc ? 'doc' : 'comment', rest); i = line.length; state.block += nested; } else if (nested) { html += span(state.doc ? 'doc' : 'comment', inner); i += inner.length; state.block += nested - 1; if (!state.block) state.doc = false; } else { html += span(state.doc ? 'doc' : 'comment', inner); i += inner.length; state.block = 0; state.doc = false; } continue; }
        if (rest.startsWith('--')) { html += span('comment', rest); i = line.length; break; }
        if (ch === '"') { const m = /^"(?:[^"\\]|\\.)*"/.exec(rest); if (m) { html += span('string', m[0]); i += m[0].length; } else { html += span('string', rest); i = line.length; state.string = true; } continue; }
        if (ch === "'" && /^'(?:[^'\\]|\\.)'/.test(rest)) { const m = /^'(?:[^'\\]|\\.)'/.exec(rest); html += span('string', m[0]); i += m[0].length; continue; }
        if (rest.startsWith('@[')) { attrDepth = 1; html += span('attr', '@['); i += 2; continue; }
        if (attrDepth) { if (ch === ']') { attrDepth = 0; html += span('attr', ch); i += 1; continue; } const m = /^[^\]]+/.exec(rest); html += span('attr', m[0]); i += m[0].length; continue; }
        if (/\s/.test(ch)) { const m = /^\s+/.exec(rest); html += m[0]; i += m[0].length; continue; }
        if (/^\d/.test(rest)) { const m = NUMBER.exec(rest); html += span('number', m[0]); i += m[0].length; continue; }
        const id = IDENT.exec(rest);
        if (id) {
          const word = id[0];
          const starred = rest.slice(word.length).startsWith('*') && SORTS.has(word + '*') ? word + '*' : word;
          let cls = '';
          if (expectDecl) { cls = 'decl'; expectDecl = false; }
          else if (expectScope) { cls = 'namespace'; expectScope = false; }
          else if (SORTS.has(starred)) cls = 'sort';
          else if (KEYWORDS.has(word)) { cls = 'keyword'; if (DECLARATORS.has(word)) expectDecl = true; if (SCOPES.has(word)) expectScope = true; }
          else if (TACTICS.has(word)) cls = 'tactic';
          else if (/^[A-Z]/.test(word.split('.').pop()) || /^[A-Z]/.test(word)) cls = 'type';
          else if (word.includes('.')) cls = 'qualified';
          else cls = 'ident';
          if (word === 'sorry' || word === 'admit') cls = 'hole';
          html += span(cls, starred); i += starred.length; continue;
        }
        if (ch === '#' && /^#[a-z_]+/.test(rest)) { const m = /^#[a-z_]+/.exec(rest); html += span('command', m[0]); i += m[0].length; continue; }
        const sym = SYMBOL.exec(rest);
        if (sym) { html += span('op', sym[0]); i += sym[0].length; continue; }
        const punct = PUNCT.exec(rest);
        if (punct) { html += span('punct', punct[0]); i += 1; continue; }
        html += esc(ch); i += 1;
      }
      if (!line.trim()) { expectDecl = expectDecl && false; }
      out[li] = html;
    }
    return out;
  }
  window.LeanHighlight = {highlight, isLean: path => /\.lean$/i.test(String(path || ''))};
})();
