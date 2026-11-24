import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1649.Count
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.and, []⟩, 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) : (replC gates i0).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (replC gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · simp [replC, hki]
  · have e : (replC gates i0.val).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (replC gates i0.val) x (n + i0.val) = true := by
  have h := gate_value (replC gates i0.val) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (replC gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (replC gates i0) x r else false) := by
  have h := gate_value (replC gates i0) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0).gates[w - n]'(by simp [replC]; omega) = gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = true) (w : ℕ) :
    value (replC gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val) x w (by rw [replC_size]; omega)]


def singletonInput {n : ℕ} (p : Fin n) : Fin n → Bool := fun v => decide (v = p)

def outsideSupport {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) :=
  support C w \ R

def liveInputs {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) (g : Gate) :=
  g.inputs.toFinset.filter fun r => r < w ∧ (outsideSupport C R r).Nonempty

def branches {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ h : w - n < C.gates.length,
    C.gates[w - n].op = GateOp.or ∧
      2 ≤ (liveInputs C R w C.gates[w - n]).card

noncomputable def charged {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (z : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Ico n (n + C.size)).erase z).filter fun w =>
    outsideSupport C R w ⊆ S ∧ 2 ≤ (outsideSupport C R w).card ∧ branches C R w

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.or) :
    value C x w = true ↔ ∃ r ∈ C.gates[w - n].inputs, r < w ∧ value C x r = true := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hv⟩
    by_cases h' : r < w
    · exact ⟨r, hr, h', by simpa [h'] using hv⟩
    · simp [h'] at hv
  · rintro ⟨r, hr, h', hv⟩
    exact ⟨r, hr, by simp [h', hv]⟩

lemma and_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.and) :
    value C x w = false ↔ ∃ r ∈ C.gates[w - n].inputs, w ≤ r ∨ value C x r = false := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hf⟩
    by_cases h' : r < w
    · exact ⟨r, hr, Or.inr (by simpa [h'] using hf)⟩
    · exact ⟨r, hr, Or.inl (by omega)⟩
  · rintro ⟨r, hr, hf | hf⟩
    · exact ⟨r, hr, by simp [show ¬ r < w by omega]⟩
    · exact ⟨r, hr, by simp [hf]⟩

lemma outside_mono {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j)
    (x y : Fin n → Bool) (hx : value ⟨gates, 0⟩ x (n+j.val) = true)
    (hy : value ⟨gates, 0⟩ y (n+j.val) = true)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  rw [← replC_eq gates j 0 x hx w, ← replC_eq gates j 0 y hy w]
  exact value_mono _ (replC_gates gates j hops hu) x y hxy w

lemma outside_input_data {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (y : Fin n → Bool)
    (w : ℕ) (hw : n ≤ w) (h : w - n < C.gates.length)
    (hops : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or)
    (hlen : C.gates[w - n].inputs.length ≤ 2)
    (hy : value C y w = false) (hne : (outsideSupport C R w).Nonempty) :
    ∃ P : Finset ℕ, (∀ r ∈ P, r < w ∧ value C y r = false) ∧
      outsideSupport C R w ⊆ P.biUnion (outsideSupport C R) ∧
      P.card ≤ 2 ∧ (2 ≤ P.card → branches C R w) := by
  classical
  rcases hops with hop | hop
  · obtain ⟨r, hr, hbad⟩ := (and_false C y w hw h hop).mp hy
    have hlt : r < w := by
      by_contra! hrw
      obtain ⟨p, hp⟩ := hne
      have hp' := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      have hbad' := (and_false C (singletonInput p) w hw h hop).mpr ⟨r, hr, Or.inl hrw⟩
      change value C (singletonInput p) w = true at hp'
      simp [hbad'] at hp'
    refine ⟨{r}, ?_, ?_, by simp, by simp⟩
    · intro a ha
      have : a = r := Finset.mem_singleton.mp ha
      subst a
      exact ⟨hlt, hbad.resolve_left (by omega)⟩
    · intro p hp
      have hp' := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      have hpr : value C (singletonInput p) r = true := by
        by_contra! hr'
        have hr'' : value C (singletonInput p) r = false := by simpa using hr'
        have hn := (and_false C (singletonInput p) w hw h hop).mpr ⟨r, hr, Or.inr hr''⟩
        change value C (singletonInput p) w = true at hp'
        simp [hn] at hp'
      simpa [outsideSupport] using
        Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr hpr, (Finset.mem_sdiff.mp hp).2⟩
  · let P := liveInputs C R w C.gates[w - n]
    refine ⟨P, ?_, ?_, ?_, fun hP => ⟨h,hop,hP⟩⟩
    · intro r hr
      have ⟨hri, hlt, _⟩ := Finset.mem_filter.mp hr
      refine ⟨hlt, Bool.eq_false_iff.mpr ?_⟩
      intro hrt
      have he := (or_value C y w hw h hop).mpr ⟨r,List.mem_toFinset.mp hri,hlt,hrt⟩
      simp [hy] at he
    · intro p hp
      have hpt := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C (singletonInput p) w hw h hop).mp hpt
      have hpr : p ∈ outsideSupport C R r :=
        Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr hv, (Finset.mem_sdiff.mp hp).2⟩
      exact Finset.mem_biUnion.mpr ⟨r,
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt, ⟨p,hpr⟩⟩, hpr⟩
    · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)

lemma outside_sub {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool)
    (hy : ∀ p, p ∉ R → p ∉ S → y p = true)
    (hm : ∀ p, p ∉ R → y p = true → ∀ w,
      value C (singletonInput p) w = true → value C y w = true)
    (w : ℕ) (hw : value C y w = false) :
    outsideSupport C R w ⊆ S := by
  intro p hp
  obtain ⟨hs, hr⟩ := Finset.mem_sdiff.mp hp
  by_contra hs'
  have := hm p hr (hy p hr hs') w ((mem_support C w p).mp hs)
  simp [hw] at this

lemma frontier {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (z : ℕ)
    (y : Fin n → Bool) (hz : value C y z = true)
    (hsub : ∀ w, value C y w = false → outsideSupport C R w ⊆ S)
    (hops : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2) :
    ∀ (t : ℕ) (B : Finset ℕ), (∀ w ∈ B, value C y w = false) →
      (∀ w ∈ B, 2 ≤ (outsideSupport C R w).card → w < t) →
      ∃ F : Finset ℕ, B.biUnion (outsideSupport C R) ⊆ F.biUnion (outsideSupport C R) ∧
        (∀ w ∈ F, (outsideSupport C R w).card ≤ 1) ∧
        F.card ≤ B.card + ((charged C R S z).filter (· < t)).card := by
  classical
  intro t
  induction t with
  | zero =>
    intro B _ hlt
    refine ⟨B, Finset.Subset.rfl, ?_, by omega⟩
    intro w hw
    have := hlt w hw
    omega
  | succ t ih =>
    intro B hfalse hlt
    by_cases hcase : t ∈ B ∧ 2 ≤ (outsideSupport C R t).card
    · obtain ⟨ht, hs⟩ := hcase
      have hs' := hs.trans (Finset.card_le_card (Finset.sdiff_subset (s := support C t) (t := R)))
      obtain ⟨hn, hC⟩ := support_gate C t hs'
      have hi : t - n < C.gates.length := by unfold Circuit.size at hC; omega
      have hne : t ≠ z := by intro e; have := hfalse t ht; simp [e, hz] at this
      obtain ⟨hop, hlen⟩ := hops t hn hi hne
      obtain ⟨P, hP, hcover, hcard, hb⟩ :=
        outside_input_data C R y t hn hi hop hlen (hfalse t ht)
          (Finset.card_pos.mp (by omega))
      let B' := B.erase t ∪ P
      have hf' (w) (hw : w ∈ B') : value C y w = false := by
        rcases Finset.mem_union.mp hw with h | h
        · exact hfalse w (Finset.mem_erase.mp h).2
        · exact (hP w h).2
      have ht' (w) (hw : w ∈ B') (hsw : 2 ≤ (outsideSupport C R w).card) : w < t := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨hne, hin⟩ := Finset.mem_erase.mp h
          have := hlt w hin hsw
          omega
        · exact (hP w h).1
      obtain ⟨F, hFsub, hFs, hFc⟩ := ih B' hf' ht'
      refine ⟨F, ?_, hFs, ?_⟩
      · intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        apply hFsub
        by_cases he : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩), hpw⟩
      · have hbc := Finset.card_union_le (B.erase t) P
        change B'.card ≤ _ at hbc
        have he := Finset.card_erase_add_one ht
        let G := charged C R S z
        have hinc : G.filter (· < t) ⊆ G.filter (· < t + 1) := by
          intro w hw
          obtain ⟨hm, hw'⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨hm, by omega⟩
        by_cases hp : 2 ≤ P.card
        · have hg : t ∈ G :=
            Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_Ico.mpr ⟨hn,hC⟩⟩,
              hsub t (hfalse t ht), hs, hb hp⟩
          have hinc' : insert t (G.filter (· < t)) ⊆ G.filter (· < t + 1) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Finset.mem_filter.mpr ⟨hg, by omega⟩
            · exact hinc hw
          have hfin := Finset.card_le_card hinc'
          rw [Finset.card_insert_of_notMem (by simp)] at hfin
          change F.card ≤ B.card + (G.filter (· < t + 1)).card
          change F.card ≤ B'.card + (G.filter (· < t)).card at hFc
          omega
        · have hfin := Finset.card_le_card hinc
          change F.card ≤ B.card + (G.filter (· < t + 1)).card
          change F.card ≤ B'.card + (G.filter (· < t)).card at hFc
          omega
    · have hlt' (w) (hw : w ∈ B) (hsw : 2 ≤ (outsideSupport C R w).card) : w < t := by
        have := hlt w hw hsw
        have hne : w ≠ t := by intro e; subst w; exact hcase ⟨hw,hsw⟩
        omega
      obtain ⟨F, hF, hFs, hFc⟩ := ih B hfalse hlt'
      refine ⟨F, hF, hFs, hFc.trans (Nat.add_le_add_left (Finset.card_le_card ?_) _)⟩
      intro w hw
      obtain ⟨hm, hw'⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hm, by omega⟩

lemma charged_count {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (o z : ℕ)
    (y : Fin n → Bool) (hz : value C y z = true)
    (hout : value C y o = false) (hsupport : support C o = S)
    (hsub : ∀ w, value C y w = false → outsideSupport C R w ⊆ S)
    (hops : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2) :
    (S \ R).card - 1 ≤ (charged C R S z).card := by
  have hlt (w) (hw : w ∈ ({o} : Finset ℕ)) (h : 2 ≤ (outsideSupport C R w).card) :
      w < n + C.size := by
    exact (support_gate C w (h.trans (Finset.card_le_card Finset.sdiff_subset))).2
  obtain ⟨F, hFsub, hFs, hFc⟩ := frontier C R S z y hz hsub hops
    (n + C.size) {o} (by intro w hw; simpa using (Finset.mem_singleton.mp hw) ▸ hout) hlt
  have h1 := Finset.card_le_card hFsub
  simp [outsideSupport, hsupport] at h1
  have h2 := Finset.card_biUnion_le_card_mul F (outsideSupport C R) 1 hFs
  have h3 := Finset.card_filter_le (charged C R S z) (fun w => w < n + C.size)
  simp only [Nat.mul_one] at h2
  simp only [Finset.card_singleton] at hFc
  omega

end PEqualNP.Outside.L_meta_1649.Count

namespace PEqualNP.Outside.L_meta_1649.Count

open PEqualNP.CircuitLowerBounds

def projected {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (w : ℕ) :=
  support C w ∩ U

def mixedOn {n : ℕ} (C : Circuit) (R T U : Finset (Fin n)) (w : ℕ) : Prop :=
  projected C U w ⊆ T ∧ (outsideSupport C R w).Nonempty ∧
    (projected C U w ∩ R).Nonempty ∧ value C (fun _ : Fin n => false) w = false

lemma or_reader_not_sub {n : ℕ} (C : Circuit) (R T : Finset (Fin n))
    (w z : ℕ) (hn : n ≤ w) (hi : w - n < C.gates.length)
    (hop : C.gates[w - n].op = GateOp.or) (hz : z ∈ C.gates[w - n].inputs) (hzw : z < w)
    (hlarge : ¬ (Finset.univ \ R ⊆ T))
    (hoff : ∀ p ∉ R, value C (singletonInput p) z = true) :
    ¬ outsideSupport C R w ⊆ T := by
  intro hsub
  apply hlarge
  intro p hp
  have hpR := (Finset.mem_sdiff.mp hp).2
  have hpw := (or_value C (singletonInput p) w hn hi hop).mpr ⟨z, hz, hzw, hoff p hpR⟩
  exact hsub (Finset.mem_sdiff.mpr ⟨(mem_support C w p).mpr hpw, hpR⟩)

lemma and_reader_alias {n : ℕ} (C : Circuit)
    (w z : ℕ) (hn : n ≤ w) (hi : w - n < C.gates.length)
    (hop : C.gates[w - n].op = GateOp.and) (hz : z ∈ C.gates[w - n].inputs)
    (hlen : C.gates[w - n].inputs.length ≤ 2)
    (hwf : ∀ a ∈ C.gates[w - n].inputs, a < w)
    (h0 : value C (fun _ : Fin n => false) z = true)
    (hw0 : value C (fun _ : Fin n => false) w = false) :
    ∃ r < w, (∀ x : Fin n → Bool, value C x z = true → value C x w = value C x r) := by
  obtain ⟨r, hr, hrf⟩ := (and_false C _ w hn hi hop).mp hw0
  have hrf' := hrf.resolve_left (not_le_of_gt (hwf r hr))
  have hzr : z ≠ r := by
    intro e
    subst r
    exact Bool.noConfusion (h0.symm.trans hrf')
  have hmem : ∀ s ∈ C.gates[w - n].inputs, s = z ∨ s = r := by
    intro s hs
    by_contra! h
    have hsub : ({s,z,r} : Finset ℕ) ⊆ (C.gates[w - n].inputs).toFinset := by
      intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton, List.mem_toFinset] at ha ⊢
      rcases ha with rfl | rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hsub
    have hfin := List.toFinset_card_le C.gates[w - n].inputs
    rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair hzr] at hcard
    omega
  refine ⟨r, hwf r hr, fun x hx => ?_⟩
  have hiff : value C x w = false ↔ value C x r = false := by
    rw [and_false C x w hn hi hop]
    constructor
    · rintro ⟨s, hs, hs'⟩
      have hf := hs'.resolve_left (not_le_of_gt (hwf s hs))
      rcases hmem s hs with rfl | rfl
      · exact False.elim (Bool.noConfusion (hx.symm.trans hf))
      · exact hf
    · exact fun h => ⟨r, hr, Or.inr h⟩
  cases a : value C x w <;> cases b : value C x r <;> simp [a, b] at hiff ⊢

lemma projected_card {n : ℕ} (C : Circuit) (R T U : Finset (Fin n)) (w : ℕ)
    (h : mixedOn C R T U w) : 2 ≤ (support (n := n) C w).card := by
  obtain ⟨p, hp⟩ := h.2.1
  obtain ⟨r, hr⟩ := h.2.2.1
  obtain ⟨hps, hpR⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hrU, hrR⟩ := Finset.mem_inter.mp hr
  exact Finset.one_lt_card.mpr ⟨p, hps, r, (Finset.mem_inter.mp hrU).1, fun h => hpR (h ▸ hrR)⟩

lemma filtered_entry {n : ℕ} (C : Circuit) (R T U : Finset (Fin n)) (o z : ℕ)
    (h0 : value C (fun _ : Fin n => false) z = true)
    (hU : ∀ p ∉ R, p ∈ U)
    (hoff : ∀ p ∉ R, value C (singletonInput p) z = true)
    (hlarge : ¬ (Finset.univ \ R ⊆ T))
    (hmode : (∀ p ∈ U, value C (singletonInput p) z = true) ∨
      (∀ p ∈ R ∩ T, value C (singletonInput p) z = false))
    (hlegal : ∀ w, n ≤ w → (hi : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2)
    (hwf : ∀ w, n ≤ w → (hi : w - n < C.gates.length) →
      ∀ a ∈ C.gates[w - n].inputs, a < w)
    (hm : mixedOn C R T U o) :
    ∃ w, w ∈ Finset.Ico n (n + C.size) ∧ w ≠ z ∧ mixedOn C R T U w ∧
      ¬ branches C R w ∧ ∀ i : Fin C.gates.length, w = n + i.val → z ∉ (C.gates.get i).inputs := by
  classical
  have hex : ∃ w, mixedOn C R T U w := ⟨o, hm⟩
  let w := Nat.find hex
  have hw := Nat.find_spec hex
  obtain ⟨hn, hbound⟩ := support_gate C w (projected_card C R T U w hw)
  have hi : w - n < C.gates.length := by unfold Circuit.size at hbound; omega
  have hne : w ≠ z := by
    intro he
    exact Bool.noConfusion (hw.2.2.2.symm.trans (he.symm ▸ h0))
  have hg := hlegal w hn hi hne
  have hmarker : ∃ p ∈ R ∩ T, p ∈ U ∧ p ∈ support C w := by
    obtain ⟨p, hp⟩ := hw.2.2.1
    obtain ⟨hproj, hpR⟩ := Finset.mem_inter.mp hp
    obtain ⟨hps, hpU⟩ := Finset.mem_inter.mp hproj
    exact ⟨p, Finset.mem_inter.mpr ⟨hpR, hw.1 hproj⟩, hpU, hps⟩
  have hbr : ¬ branches C R w := by
    rintro ⟨h, hop, hb⟩
    let g := C.gates[w - n]
    obtain ⟨p, hp, hpU, hps⟩ := hmarker
    have hpR := (Finset.mem_inter.mp hp).1
    obtain ⟨r, hr, hrw, hrt⟩ :=
      (or_value C (singletonInput p) w hn h hop).mp ((mem_support C w p).mp hps)
    have hfilter : liveInputs C R w g = g.inputs.toFinset := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      exact (List.toFinset_card_le _).trans (hg.2.trans hb)
    have hout : (outsideSupport C R r).Nonempty :=
      (Finset.mem_filter.mp (show r ∈ liveInputs C R w g by
        rw [hfilter]
        exact List.mem_toFinset.mpr hr)).2.2
    have hrsub : projected C U r ⊆ projected C U w := by
      intro p' hp'
      obtain ⟨hpr, hpU⟩ := Finset.mem_inter.mp hp'
      exact Finset.mem_inter.mpr ⟨(mem_support C w p').mpr
        ((or_value C (singletonInput p') w hn h hop).mpr ⟨r, hr, hrw, (mem_support C r p').mp hpr⟩), hpU⟩
    have hz : value C (fun _ : Fin n => false) r = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact Bool.noConfusion (hw.2.2.2.symm.trans ((or_value C _ w hn h hop).mpr ⟨r, hr, hrw, ht⟩))
    have hmr : mixedOn C R T U r := ⟨hrsub.trans hw.1, hout,
      ⟨p, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨(mem_support C r p).mpr hrt, hpU⟩, hpR⟩⟩, hz⟩
    exact Nat.find_min hex hrw hmr
  refine ⟨w, Finset.mem_Ico.mpr ⟨hn,hbound⟩, hne, hw, hbr, ?_⟩
  intro i hiw hzi
  have he : w - n = i.val := by omega
  have hz : z ∈ C.gates[w - n].inputs := by simpa only [he, List.get_eq_getElem] using hzi
  rcases hg.1 with hand | hor
  · rcases hmode with hgood | hbad
    · obtain ⟨r, hr, hrval⟩ :=
        and_reader_alias C w z hn hi hand hz hg.2 (hwf w hn hi) h0 hw.2.2.2
      have hProjEq : projected C U r = projected C U w := by
        ext p
        simp only [projected, Finset.mem_inter, mem_support]
        constructor <;> rintro ⟨hp, hu⟩
        · exact ⟨(hrval _ (hgood p hu)).trans hp, hu⟩
        · exact ⟨(hrval _ (hgood p hu)).symm.trans hp, hu⟩
      have hOut : (outsideSupport C R r).Nonempty := by
        obtain ⟨p, hp⟩ := hw.2.1
        obtain ⟨hpW, hpR⟩ := Finset.mem_sdiff.mp hp
        refine ⟨p, Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr ?_, hpR⟩⟩
        exact (hrval _ (hgood p (hU p hpR))).symm.trans ((mem_support C w p).mp hpW)
      refine Nat.find_min hex hr ⟨hProjEq ▸ hw.1, hOut, ?_, (hrval _ h0).symm.trans hw.2.2.2⟩
      rw [hProjEq]
      exact hw.2.2.1
    · obtain ⟨p, hp, _, hpw⟩ := hmarker
      have hfalse := (and_false C _ w hn hi hand).mpr ⟨z, hz, Or.inr (hbad p hp)⟩
      exact Bool.noConfusion (hfalse.symm.trans ((mem_support C w p).mp hpw))
  · apply or_reader_not_sub C R T w z hn hi hor hz (hwf w hn hi z hz) hlarge hoff
    intro p hp
    obtain ⟨hpS, hpR⟩ := Finset.mem_sdiff.mp hp
    exact hw.1 (Finset.mem_inter.mpr ⟨hpS, hU p hpR⟩)

end PEqualNP.Outside.L_meta_1649.Count

namespace PEqualNP.Outside.L_meta_1649.Count

open PEqualNP.CircuitLowerBounds

lemma other_rows (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hsize : ∀ t, (L t).card = q + 1)
    (hinter : ∀ t u, t ≠ u → (L t ∩ L u).card = 1)
    (gates : List Gate) (o : Fin N → ℕ) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hWF : ∀ i : Fin gates.length, ∀ r ∈ (gates.get i).inputs, r < N + i.val)
    (hu : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hcorrect : ∀ t (x : Fin N → Bool), value ⟨gates, 0⟩ x (o t) = decide (∃ v ∈ L t, x v = true))
    (hoff : ∀ x : Fin N → Bool, (∀ p ∈ L i0, x p = false) → value ⟨gates, 0⟩ x (N + j.val) = true) :
    ∃ U : Finset ℕ, (N - 1) * q ≤ U.card ∧
      ∀ w ∈ U, w ∈ Finset.Ico N (N + gates.length) ∧ w ≠ N + j.val ∧
        (∀ i : Fin gates.length, w = N + i.val → N + j.val ∉ (gates.get i).inputs) ∧
        (outsideSupport ⟨gates, 0⟩ (L i0) w).Nonempty := by
  classical
  let C : Circuit := ⟨gates, 0⟩
  let R := L i0
  let z := N + j.val
  have outside_single (p : Fin N) (hp : p ∉ R) : value C (singletonInput p) z = true := by
    apply hoff
    intro r hr
    have he : r ≠ p := fun e => hp (e ▸ hr)
    simp [singletonInput, he]
  have h0 : value C (fun _ : Fin N => false) z = true := hoff _ (by simp)
  have hop (w : ℕ) (hn : N ≤ w) (hw : w - N < C.gates.length) (hne : w ≠ z) :
      (C.gates[w - N].op = GateOp.and ∨ C.gates[w - N].op = GateOp.or) ∧
      C.gates[w - N].inputs.length ≤ 2 := by
    have h := hg C.gates[w - N] (List.getElem_mem _)
    refine ⟨?_, h.2⟩
    rcases h.1 with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · have he := congrArg Fin.val (hu ⟨w - N, hw⟩ e)
      change w - N = j.val at he
      exact False.elim (hne (by dsimp [z]; omega))
  have hwf (w : ℕ) (hn : N ≤ w) (hw : w - N < C.gates.length) :
      ∀ a ∈ C.gates[w - N].inputs, a < w := by
    intro a ha
    have h := hWF ⟨w - N, hw⟩ a ha
    exact lt_of_lt_of_le h (by dsimp; omega)
  have hsp (t : Fin N) : support C (o t) = L t := by
    ext p
    rw [mem_support, ← show singletonInput p = (fun v => decide (v = p)) from rfl,
      show value C (singletonInput p) (o t) =
      decide (∃ v ∈ L t, singletonInput p v = true) from hcorrect t _]
    simp [singletonInput]
  have hlarge (t : Fin N) : ¬ (Finset.univ \ R ⊆ L t) := by
    intro h
    have hle := Finset.card_le_card h
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_univ, Fintype.card_fin] at hle
    have hR : R.card = q + 1 := hsize i0
    rw [hR, hsize t, hN] at hle
    have hq2 : q + 1 < q ^ 2 := by nlinarith [Nat.mul_le_mul_left q hq]
    omega
  have outside_counts (t : Fin N) : (L t \ R).card - 1 ≤ (charged C R (L t) z).card := by
    let y : Fin N → Bool := fun p => decide (p ∉ R ∧ p ∉ L t)
    have hy : ∀ p ∈ R, y p = false := by intro p hp; simp [y, hp]
    apply charged_count C R (L t) (o t) z y (hoff y hy) _ (hsp t) _ hop
    · rw [show value C y (o t) = decide (∃ v ∈ L t, y v = true) from hcorrect t _]
      apply decide_eq_false
      rintro ⟨p, hp, he⟩
      exact (of_decide_eq_true he).2 hp
    · apply outside_sub C R (L t) y
      · intro p hp hr; simp [y,hp,hr]
      · intro p hp hyp w
        apply outside_mono gates j hg hu (singletonInput p) y (outside_single p hp) (hoff y hy) _ w
        intro v hv
        have e : v = p := of_decide_eq_true hv
        simpa [e] using hyp
  have hOut (t : Fin N) (ht : t ≠ i0) : (L t \ R).card = q := by
    have hs := Finset.card_sdiff_add_card_inter (L t) R
    have hi : (L t ∩ R).card = 1 := hinter t i0 ht
    rw [hi, hsize] at hs
    omega
  let G : Finset (Fin N) := Finset.univ.filter fun p => value C (singletonInput p) z = true
  let U (t : Fin N) : Finset (Fin N) :=
    if ∀ p ∈ R ∩ L t, value C (singletonInput p) z = false then Finset.univ else G
  have hUC (t : Fin N) (p : Fin N) (hp : p ∉ R) : p ∈ U t := by
    unfold U
    split_ifs
    · exact Finset.mem_univ p
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, outside_single p hp⟩
  have hUComp (t u : Fin N) : U t ⊆ U u ∨ U u ⊆ U t := by
    unfold U
    split_ifs <;> simp
  have hEntry (t : Fin N) (ht : t ≠ i0) :
      ∃ w, w ∈ Finset.Ico N (N + C.size) ∧ w ≠ z ∧ mixedOn C R (L t) (U t) w ∧
        ¬ branches C R w ∧ ∀ i : Fin C.gates.length, w = N + i.val → z ∉ (C.gates.get i).inputs := by
    refine filtered_entry C R (L t) (U t) (o t) z h0 (hUC t) outside_single (hlarge t) ?_ hop hwf ?_
    · by_cases hm : ∀ p ∈ R ∩ L t, value C (singletonInput p) z = false
      · exact Or.inr hm
      · left
        simp only [U, ite_eq_right hm]
        exact fun _ hp => (Finset.mem_filter.mp hp).2
    · have hOutNonempty : (L t \ R).Nonempty := Finset.card_pos.mp (by rw [hOut t ht]; omega)
      have hI : (R ∩ L t).card = 1 := hinter i0 t (Ne.symm ht)
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hI
      have hpr : p ∈ R ∩ L t := by simp [hp]
      have hpR := (Finset.mem_inter.mp hpr).1
      have hpT := (Finset.mem_inter.mp hpr).2
      have hpU : p ∈ U t := by
        unfold U
        split_ifs with hm
        · exact Finset.mem_univ p
        · have hpt : value C (singletonInput p) z = true := by
            cases hb : value C (singletonInput p) z with
            | true => rfl
            | false => exact False.elim (hm (by simpa [hp] using hb))
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpt⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · unfold projected
        rw [hsp]
        exact Finset.inter_subset_left
      · simpa [outsideSupport,hsp] using hOutNonempty
      · exact ⟨p, Finset.mem_inter.mpr
          ⟨Finset.mem_inter.mpr ⟨(hsp t).symm ▸ hpT, hpU⟩, hpR⟩⟩
      · rw [show value C (fun _ : Fin N => false) (o t) =
          decide (∃ v ∈ L t, (fun _ : Fin N => false) v = true) from hcorrect t _]
        simp
  let D := (Finset.univ : Finset (Fin N)).erase i0
  let et (t : D) := Classical.choose (hEntry t.val (Finset.ne_of_mem_erase t.property))
  have e_spec (t : D) := Classical.choose_spec (hEntry t.val (Finset.ne_of_mem_erase t.property))
  let B (t : D) := insert (et t) (charged C R (L t.val) z)
  have heNew (t : D) : et t ∉ charged C R (L t.val) z :=
    fun hm => (e_spec t).2.2.2.1 (Finset.mem_filter.mp hm).2.2.2
  have hB (t : D) : q ≤ (B t).card := by
    unfold B
    rw [Finset.card_insert_of_notMem (heNew t)]
    have h := outside_counts t.val
    rw [hOut t.val (Finset.ne_of_mem_erase t.property)] at h
    omega
  have hdis : Set.PairwiseDisjoint (Finset.univ : Finset D) B := by
    intro t _ u _ hne
    have htu : t.val ≠ u.val := fun h => hne (Subtype.ext h)
    change Disjoint (B t) (B u)
    rw [Finset.disjoint_left]
    intro w hwT hwU
    have impossible (X : Finset (Fin N)) (hX : 2 ≤ X.card)
        (hXT : X ⊆ L t.val) (hXU : X ⊆ L u.val) : False := by
      have hcard := Finset.card_le_card (Finset.subset_inter hXT hXU)
      rw [hinter _ _ htu] at hcard
      omega
    rcases Finset.mem_insert.mp hwT with hT | hT <;> rcases Finset.mem_insert.mp hwU with hU | hU
    · have hTm : mixedOn C R (L t.val) (U t.val) w := hT.symm ▸ (e_spec t).2.2.1
      have hUm : mixedOn C R (L u.val) (U u.val) w := hU.symm ▸ (e_spec u).2.2.1
      obtain ⟨p,hp⟩ := hTm.2.1
      obtain ⟨hpS,hpR⟩ := Finset.mem_sdiff.mp hp
      have hpT := hTm.1 (Finset.mem_inter.mpr ⟨hpS,hUC t.val p hpR⟩)
      have hpU := hUm.1 (Finset.mem_inter.mpr ⟨hpS,hUC u.val p hpR⟩)
      have hcommon : ∃ r ∈ R, r ∈ L t.val ∧ r ∈ L u.val := by
        rcases hUComp t.val u.val with hcomp | hcomp
        · obtain ⟨r, hr⟩ := hTm.2.2.1
          obtain ⟨hr1, hrR⟩ := Finset.mem_inter.mp hr
          obtain ⟨hrSp, hrUt⟩ := Finset.mem_inter.mp hr1
          exact ⟨r, hrR, hTm.1 hr1, hUm.1 (Finset.mem_inter.mpr ⟨hrSp,hcomp hrUt⟩)⟩
        · obtain ⟨r, hr⟩ := hUm.2.2.1
          obtain ⟨hr1, hrR⟩ := Finset.mem_inter.mp hr
          obtain ⟨hrSp, hrUu⟩ := Finset.mem_inter.mp hr1
          exact ⟨r, hrR, hTm.1 (Finset.mem_inter.mpr ⟨hrSp,hcomp hrUu⟩), hUm.1 hr1⟩
      obtain ⟨r, hrR, hrT, hrU⟩ := hcommon
      have hpNe : p ≠ r := fun h => hpR (h ▸ hrR)
      apply impossible {p,r} (by simp [hpNe])
      · intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption
      · intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with rfl | rfl <;> assumption
    · have hn : ¬ branches C R w := hT.symm ▸ (e_spec t).2.2.2.1
      exact hn (Finset.mem_filter.mp hU).2.2.2
    · have hn : ¬ branches C R w := hU.symm ▸ (e_spec u).2.2.2.1
      exact hn (Finset.mem_filter.mp hT).2.2.2
    · have a := (Finset.mem_filter.mp hT).2
      have b := (Finset.mem_filter.mp hU).2
      exact impossible _ a.2.1 a.1 b.1
  let W := Finset.univ.biUnion B
  refine ⟨W, ?_, ?_⟩
  · have hc : W.card = ∑ t : D, (B t).card := Finset.card_biUnion hdis
    rw [hc]
    have h1 : ∑ t : D, q ≤ ∑ t : D, (B t).card :=
      Finset.sum_le_sum (fun t _ => hB t)
    have hD : D.card = N - 1 := by
      simp [D]
    simpa [hD, Nat.mul_comm] using h1
  · intro w hw
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hw
    rcases Finset.mem_insert.mp ht with rfl | hCh
    · exact ⟨(e_spec t).1, (e_spec t).2.1, (e_spec t).2.2.2.2, (e_spec t).2.2.1.2.1⟩
    · obtain ⟨hm, hout, htwo, hbranch⟩ := Finset.mem_filter.mp hCh
      obtain ⟨hnz, hI⟩ := Finset.mem_erase.mp hm
      refine ⟨hI, hnz, ?_, Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) htwo)⟩
      intro i hi hz
      have hNw := (Finset.mem_Ico.mp hI).1
      obtain ⟨hidx, hor, _⟩ := hbranch
      have hwe : w - N = i.val := by omega
      have hz' : z ∈ C.gates[w - N].inputs := by
        simpa only [hwe,List.get_eq_getElem] using hz
      exact or_reader_not_sub C R (L t.val) w z hNw hidx hor hz'
        (hwf w hNw hidx z hz') (hlarge t.val) outside_single hout

end PEqualNP.Outside.L_meta_1649.Count

namespace PEqualNP.Outside.L_meta_1649.Freeze
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def cval {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    cval C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : cval C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    cval C x w = g.op.eval (g.inputs.map fun r => if r < w then cval C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then cval C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then cval C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, cval C x r = true → cval C y r = true) →
        cval C x w = true → cval C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then cval C x r else false) = true →
        (if r < w then cval C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        cval C z w = g.op.eval (g.inputs.map fun r => if r < w then cval C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    cval C x w = true → cval C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change cval C x p = true → cval C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.and, []⟩, 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) : (replC gates i0).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (replC gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · simp [replC, hki]
  · have e : (replC gates i0.val).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    cval (replC gates i0.val) x (n + i0.val) = true := by
  have h := gate_value (replC gates i0.val) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    cval (replC gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then cval (replC gates i0) x r else false) := by
  have h := gate_value (replC gates i0) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0).gates[w - n]'(by simp [replC]; omega) = gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    cval ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then cval ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : cval ⟨gates, o⟩ x (n + i0.val) = true) (w : ℕ) :
    cval (replC gates i0.val) x w = cval ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val) x w (by rw [replC_size]; omega)]


def upper (gates : List Gate) (j : Fin gates.length) : List Gate :=
  gates.set j.val ⟨GateOp.and, []⟩

def value {n : ℕ} (gates : List Gate) (w : ℕ) (x : Fin n → Bool) : Bool :=
  Circuit.eval ⟨gates, w⟩ (List.ofFn x)

lemma upper_length (gates : List Gate) (j : Fin gates.length) :
    (upper gates j).length = gates.length := by
  simp [upper]

lemma upper_legal (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j) :
    ∀ g ∈ upper gates j, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  replC_gates gates j hg honly

lemma upper_readsBack {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hback : ∀ i : Fin gates.length, ∀ w ∈ (gates.get i).inputs, w < n + i.val) :
    ∀ i : Fin (upper gates j).length, ∀ w ∈ ((upper gates j).get i).inputs, w < n + i.val := by
  intro i w hw
  have hi : i.val < gates.length := by simpa [upper] using i.isLt
  change w ∈ (upper gates j)[i.val].inputs at hw
  unfold upper at hw
  simp only [List.getElem_set] at hw
  by_cases hij : j.val = i.val
  · simp [hij] at hw
  · simp only [ite_eq_right hij] at hw
    exact hback ⟨i.val, hi⟩ w hw

lemma upper_true {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) :
    value (upper gates j) (n + j.val) x = true :=
  replC_true gates j x

lemma upper_agrees {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool)
    (h : value gates (n + j.val) x = true) (w : ℕ) :
    value (upper gates j) w x = value gates w x :=
  replC_eq gates j 0 x h w

lemma upper_before {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool)
    (w : ℕ) (h : w < n + j.val) : value (upper gates j) w x = value gates w x := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, 0⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates j.val) x ⟨w, hn⟩
      change cval (replC gates j.val) x w = cval ⟨gates, 0⟩ x w
      rw [h1, h2]
    · have hw : w < n + gates.length := by have := j.isLt; omega
      change cval (replC gates j.val) x w = cval ⟨gates, 0⟩ x w
      rw [replC_other gates j.val x w (by omega) hw (by omega),
        orig_value gates 0 x w (by omega) hw]
      apply repl_eval_congr
      intro a _
      by_cases ha : a < w
      · simpa [ha, value, upper, replC, cval, Circuit.eval, Circuit.wires] using ih a ha (ha.trans h)
      · simp [ha]

lemma ao_eval_mono (op : GateOp) (xs : List ℕ) (f f' : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or)
    (hm : ∀ a ∈ xs, f a = true → f' a = true) :
    op.eval (xs.map f) = true → op.eval (xs.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro h _ ⟨a, ha, rfl⟩
    exact hm a ha (h _ ⟨a, ha, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨a, ha, rfl⟩, hv⟩
    exact ⟨_, ⟨a, ha, rfl⟩, hm a ha hv⟩

lemma upper_dominates {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x : Fin n → Bool) (w : ℕ) :
    value gates w x = true → value (upper gates j) w x = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [upper_before gates j x w (by omega)]
      exact id
    by_cases hw : w < n + gates.length
    · by_cases hcut : w = n + j.val
      · subst w
        exact fun _ => upper_true gates j x
      have hk : w - n < gates.length := by omega
      let k : Fin gates.length := ⟨w - n, hk⟩
      have hkj : k ≠ j := by
        intro he
        have hval : w - n = j.val := congrArg Fin.val he
        omega
      have hop : gates[w - n].op = GateOp.and ∨ gates[w - n].op = GateOp.or := by
        have h := (hg gates[w - n] (List.getElem_mem hk)).1
        rcases h with ha | ho | ht
        · exact Or.inl ha
        · exact Or.inr ho
        · exact False.elim (hkj (honly k ht))
      change cval ⟨gates, 0⟩ x w = true → cval (replC gates j.val) x w = true
      rw [orig_value gates 0 x w (by omega) hw, replC_other gates j.val x w (by omega) hw hcut]
      apply ao_eval_mono _ _ _ _ hop
      intro a _ ha
      by_cases hlt : a < w
      · rw [ite_eq_left hlt] at ha ⊢
        exact ih a hlt ha
      · simp [hlt] at ha
    · change cval ⟨gates, 0⟩ x w = true → cval (replC gates j.val) x w = true
      rw [missing_value ⟨gates, 0⟩ x w (by simpa [Circuit.size] using Nat.le_of_not_gt hw)]
      simp

lemma upper_monotone {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value (upper gates j) w x = true → value (upper gates j) w y = true :=
  value_mono (replC gates j.val) (upper_legal gates j hg honly) x y hxy w

lemma before_monotone {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) (hw : w < n + j.val) :
    value gates w x = true → value gates w y = true := by
  rw [← upper_before gates j x w hw, ← upper_before gates j y w hw]
  exact upper_monotone gates j hg honly x y hxy w

lemma before_false_on_subset {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) (hw : w < n + j.val)
    (hy : value gates w y = false) : value gates w x = false := by
  cases hx : value gates w x
  · rfl
  · have ht := before_monotone gates j hg honly x y hxy w hw hx
    simp [hy] at ht

lemma not_value {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool)
    (hop : (gates.get j).op = GateOp.not) (w : ℕ) (hw : w < n + j.val)
    (hhead : ∃ r : List ℕ, (gates.get j).inputs = w :: r) :
    value gates (n + j.val) x = !(value gates w x) := by
  obtain ⟨r, he⟩ := hhead
  change cval ⟨gates, 0⟩ x (n + j.val) = !(cval ⟨gates, 0⟩ x w)
  rw [orig_value gates 0 x (n + j.val) (by omega) (Nat.add_lt_add_left j.isLt n)]
  simp only [Nat.add_sub_cancel_left]
  rw [show gates[j.val].op = GateOp.not from hop, show gates[j.val].inputs = w :: r from he]
  simp [GateOp.eval, hw]

lemma not_off_line {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hop : (gates.get j).op = GateOp.not) (w : ℕ) (hw : w < n + j.val)
    (hhead : ∃ r : List ℕ, (gates.get j).inputs = w :: r)
    (R : Finset (Fin n)) (hco : value gates w (fun p => decide (p ∉ R)) = false)
    (x : Fin n → Bool) (hx : ∀ p ∈ R, x p = false) :
    value gates (n + j.val) x = true := by
  have hsub (p : Fin n) (hp : x p = true) : decide (p ∉ R) = true := by
    by_cases hr : p ∈ R
    · simp [hx p hr] at hp
    · simp [hr]
  have hz := before_false_on_subset gates j hg honly x (fun p => decide (p ∉ R)) hsub w hw hco
  rw [not_value gates j x hop w hw hhead, hz]
  rfl

lemma singleton_support_inside {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (honly : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (w : ℕ) (hw : w < n + j.val)
    (R : Finset (Fin n)) (hco : value gates w (fun q => decide (q ∉ R)) = false)
    (p : Fin n) (hp : value gates w (fun q => decide (q = p)) = true) :
    p ∈ R := by
  by_contra h
  have hsub (q : Fin n) (hq : decide (q = p) = true) : decide (q ∉ R) = true := by
    have he : q = p := of_decide_eq_true hq
    simpa [he] using h
  have hz := before_false_on_subset gates j hg honly (fun q => decide (q = p))
    (fun q => decide (q ∉ R)) hsub w hw hco
  rw [hp] at hz
  contradiction

end PEqualNP.Outside.L_meta_1649.Freeze

namespace PEqualNP.Outside.L_meta_1649.Rim

open PEqualNP.CircuitLowerBounds

abbrev up {n : ℕ} (gates : List Gate) (j : Fin gates.length) (x : Fin n → Bool) (w : ℕ) : Bool :=
  Count.value (Count.replC gates j.val) x w

abbrev orig {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  Count.value ⟨gates, 0⟩ x w

def off {n : ℕ} (R : Finset (Fin n)) (p : Fin n) : Bool := decide (p ∉ R)

noncomputable def charge {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (R : Finset (Fin n)) : Finset ℕ :=
  Count.charged (Count.replC gates j.val) ∅ R (n + j.val)

theorem charge_card {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (R : Finset (Fin n)) (o : ℕ)
    (hgate : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (huniq : ∀ i : Fin gates.length, (gates.get i).op = GateOp.not → i = j)
    (hupper : ∀ x : Fin n → Bool, ∀ w, orig gates x w = true → up gates j x w = true)
    (heval : ∀ x : Fin n → Bool, orig gates x o = decide (∃ v ∈ R, x v = true))
    (hnot : orig gates (off R) (n + j.val) = true) :
    R.card - 1 ≤ (charge gates j R).card := by
  classical
  let C := Count.replC gates j.val
  have hgood := Count.replC_gates gates j hgate huniq
  have hfalse : up gates j (off R) o = false := by
    change Count.value (Count.replC gates j.val) (off R) o = false
    rw [Count.replC_eq gates j 0 (off R) hnot o]
    change orig gates (off R) o = false
    rw [heval]
    simp [off]
  have hsub (w : ℕ) (hw : up gates j (off R) w = false) :
      Count.support (n := n) C w ⊆ R := by
    intro p hp
    by_contra hpR
    have hle (v : Fin n) (hv : decide (v = p) = true) : off R v = true := by
      simpa [off, of_decide_eq_true hv] using hpR
    have htrue := Count.value_mono C hgood (fun v => decide (v = p)) (off R) hle w
      ((Count.mem_support C w p).mp hp)
    exact Bool.false_ne_true (hw.symm.trans htrue)
  have hsupport : Count.support (n := n) C o = R := by
    apply Finset.Subset.antisymm (hsub o hfalse)
    intro p hp
    apply (Count.mem_support C o p).mpr
    apply hupper
    rw [heval]
    exact decide_eq_true ⟨p, hp, by simp⟩
  have hc := Count.charged_count C ∅ R o (n + j.val) (off R)
    (Count.replC_true gates j (off R)) hfalse hsupport
    (fun w hw => by simpa [Count.outsideSupport] using hsub w hw)
    (fun w _ h _ => hgood C.gates[w - n] (List.getElem_mem h))
  simpa [charge, C] using hc

theorem charge_spec {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (R : Finset (Fin n)) (hproper : ∃ p : Fin n, p ∉ R)
    (hback : ∀ i : Fin gates.length, ∀ r ∈ (gates.get i).inputs, r < n + i.val)
    (hupper : ∀ x : Fin n → Bool, ∀ w, orig gates x w = true → up gates j x w = true)
    (w : ℕ) (hw : w ∈ charge gates j R) :
    w ∈ Finset.Ico n (n + gates.length) ∧ w ≠ n + j.val ∧
      (∃ i : Fin gates.length, w = n + i.val ∧ (gates.get i).op = GateOp.or ∧
        (n + j.val) ∉ (gates.get i).inputs) ∧
      Count.support (n := n) (Count.replC gates j.val) w ⊆ R ∧
      2 ≤ (Count.support (n := n) (Count.replC gates j.val) w).card ∧
      Count.outsideSupport ⟨gates, 0⟩ R w = ∅ := by
  classical
  let C := Count.replC gates j.val
  change w ∈ Count.charged C ∅ R (n + j.val) at hw
  unfold Count.charged at hw
  obtain ⟨hI, hsub', hcard', hbranches⟩ := Finset.mem_filter.mp hw
  obtain ⟨hne, hrange'⟩ := Finset.mem_erase.mp hI
  have hrange : w ∈ Finset.Ico n (n + gates.length) := by
    simpa [C, Count.replC_size] using hrange'
  have hsub : Count.support (n := n) C w ⊆ R := by
    simpa [Count.outsideSupport] using hsub'
  have hcard : 2 ≤ (Count.support (n := n) C w).card := by
    simpa [Count.outsideSupport] using hcard'
  have hn := (Finset.mem_Ico.mp hrange).1
  have hlt := (Finset.mem_Ico.mp hrange).2
  let i : Fin gates.length := ⟨w - n, by omega⟩
  have hiw : w = n + i.val := by dsimp [i]; omega
  have hine : j.val ≠ w - n := by omega
  obtain ⟨hidx, hop, _⟩ := hbranches
  have hgate : C.gates[w - n] = gates.get i := by
    simp [C, Count.replC, hine, i]
  refine ⟨hrange, hne, ⟨i, hiw, hgate ▸ hop, ?_⟩, hsub, hcard, ?_⟩
  · intro reads
    obtain ⟨p, hp⟩ := hproper
    have hread : n + j.val ∈ C.gates[w - n].inputs := hgate ▸ reads
    have hreadlt : n + j.val < w := hiw.symm ▸ hback i _ reads
    have hval := (Count.or_value C (fun v : Fin n => decide (v = p)) w hn hidx hop).mpr
      ⟨n + j.val, hread, hreadlt, Count.replC_true gates j _⟩
    exact hp (hsub ((Count.mem_support C w p).mpr hval))
  · apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpOrig, hpOut⟩ := Finset.mem_sdiff.mp hp
    have hval := hupper (fun v => decide (v = p)) w
      ((Count.mem_support ⟨gates, 0⟩ w p).mp hpOrig)
    exact hpOut (hsub ((Count.mem_support C w p).mpr hval))

theorem not_mem_of_thin {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (R : Finset (Fin n)) (w : ℕ)
    (heq : ∀ x : Fin n → Bool, up gates j x w = orig gates x w)
    (hthin : (Count.support (n := n) ⟨gates, 0⟩ w).card ≤ 1) :
    w ∉ charge gates j R := by
  classical
  intro hw
  change w ∈ Count.charged (Count.replC gates j.val) ∅ R (n + j.val) at hw
  unfold Count.charged at hw
  have hcard : 2 ≤ (Count.support (n := n) (Count.replC gates j.val) w).card := by
    simpa [Count.outsideSupport] using (Finset.mem_filter.mp hw).2.2.1
  have hs : Count.support (n := n) (Count.replC gates j.val) w = Count.support ⟨gates, 0⟩ w := by
    ext p
    simp only [Count.mem_support]
    exact Iff.of_eq (congrArg (· = true) (heq (fun v => decide (v = p))))
  rw [hs] at hcard
  omega

end PEqualNP.Outside.L_meta_1649.Rim

namespace PEqualNP.Outside.L_meta_1649.Tally

open PEqualNP.CircuitLowerBounds

lemma slots (n s : ℕ) (u v a b : Finset ℕ)
    (hu : u ⊆ Finset.Ico n (n + s)) (hv : v ⊆ Finset.Ico n (n + s))
    (ha : a ⊆ Finset.Ico n (n + s)) (hb : b ⊆ Finset.Ico n (n + s))
    (duv : Disjoint u v) (dua : Disjoint u a) (dub : Disjoint u b)
    (dva : Disjoint v a) (dvb : Disjoint v b) (dab : Disjoint a b) :
    u.card + v.card + a.card + b.card ≤ s := by
  have d1 : Disjoint (u ∪ v) a := Finset.disjoint_union_left.mpr ⟨dua, dva⟩
  have d2 : Disjoint (u ∪ v ∪ a) b := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨dub, dvb⟩, dab⟩
  have h := Finset.card_le_card (Finset.union_subset (Finset.union_subset
    (Finset.union_subset hu hv) ha) hb)
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
    Finset.card_union_of_disjoint duv, Nat.card_Ico] at h
  omega

lemma bound (q n : ℕ) (hn : 1 ≤ n) (gs : List Gate) (j : Fin gs.length)
    (hw : ℕ) (hwlt : hw < n + j.val)
    (back : ∀ i : Fin gs.length, ∀ w ∈ (gs.get i).inputs, w < n + i.val)
    (u v : Finset ℕ) (cu : (n - 1) * q ≤ u.card) (cv : q ≤ v.card)
    (hu : u ⊆ Finset.Ico n (n + gs.length)) (hv : v ⊆ Finset.Ico n (n + gs.length))
    (duv : Disjoint u v)
    (ju : n + j.val ∉ u) (jv : n + j.val ∉ v)
    (ru : ∀ i : Fin gs.length, n + j.val ∈ (gs.get i).inputs → n + i.val ∉ u)
    (rv : ∀ i : Fin gs.length, n + j.val ∈ (gs.get i).inputs → n + i.val ∉ v) :
    n * q + (Finset.univ.filter (fun i : Fin gs.length => n + j.val ∈ (gs.get i).inputs)).card + 1 ≤ gs.length ∧
    (n ≤ hw → hw ∉ u → hw ∉ v →
      n * q + (Finset.univ.filter (fun i : Fin gs.length => n + j.val ∈ (gs.get i).inputs)).card + 2 ≤ gs.length) := by
  classical
  let readers := Finset.univ.filter fun i : Fin gs.length => n + j.val ∈ (gs.get i).inputs
  let a := readers.image fun i => n + i.val
  have ac : a.card = readers.card := Finset.card_image_of_injective _ (fun x y e => Fin.ext (by simpa using e))
  have ha : a ⊆ Finset.Ico n (n + gs.length) := by
    intro w h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_Ico.mpr ⟨by omega, by have := i.isLt; omega⟩
  have hau : Disjoint u a := by
    apply Finset.disjoint_left.mpr
    rintro w hwu hwa
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hwa
    exact ru i (Finset.mem_filter.mp hi).2 hwu
  have hav : Disjoint v a := by
    apply Finset.disjoint_left.mpr
    rintro w hwv hwa
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hwa
    exact rv i (Finset.mem_filter.mp hi).2 hwv
  have afterGate : ∀ w ∈ a, n + j.val < w := by
    intro w hw'
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw'
    exact back i _ (Finset.mem_filter.mp hi).2
  have jrange : n + j.val ∈ Finset.Ico n (n + gs.length) :=
    Finset.mem_Ico.mpr ⟨by omega, by have := j.isLt; omega⟩
  have split : n * q = (n - 1) * q + q := by
    have he : n - 1 + 1 = n := by omega
    calc n * q = (n - 1 + 1) * q := by rw [he]
         _ = (n - 1) * q + q := by rw [Nat.add_mul, Nat.one_mul]
  change n * q + readers.card + 1 ≤ gs.length ∧ _
  constructor
  · have h := slots n gs.length u v a {n + j.val} hu hv ha
      (Finset.singleton_subset_iff.mpr jrange) duv hau (by simpa using ju)
      hav (by simpa using jv) (by
        apply Finset.disjoint_singleton_right.mpr
        exact fun h => (Nat.lt_irrefl _ (afterGate _ h)))
    rw [Finset.card_singleton, ac] at h
    omega
  · intro hwlo hwu hwv
    change n * q + readers.card + 2 ≤ gs.length
    have other : hw ∈ Finset.Ico n (n + gs.length) :=
      Finset.mem_Ico.mpr ⟨hwlo, hwlt.trans (Finset.mem_Ico.mp jrange).2⟩
    have h := slots n gs.length u v a {hw, n + j.val} hu hv ha
      (Finset.insert_subset other (Finset.singleton_subset_iff.mpr jrange)) duv hau
      (by simp [Finset.disjoint_insert_right, hwu, ju]) hav
      (by simp [Finset.disjoint_insert_right, hwv, jv]) (by
        apply Finset.disjoint_left.mpr
        intro w wa wb
        have e := afterGate w wa
        rcases Finset.mem_insert.mp wb with rfl | wb
        · omega
        · have := Finset.mem_singleton.mp wb
          omega)
    rw [Finset.card_pair (Nat.ne_of_lt hwlt), ac] at h
    omega

end PEqualNP.Outside.L_meta_1649.Tally

namespace PEqualNP.Outside.L_meta_1649.Finish

open PEqualNP.CircuitLowerBounds

theorem tally (q n : ℕ) (L : Fin n → Finset (Fin n)) (i0 : Fin n)
    (hq : 2 ≤ q) (hn : n = q ^ 2 + q + 1) (hs : ∀ t : Fin n, (L t).card = q + 1)
    (gs : List Gate) (o : Fin n → ℕ) (j : Fin gs.length) (w : ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hb : ∀ i : Fin gs.length, ∀ k ∈ (gs.get i).inputs, k < n + i.val)
    (hj : (gs.get j).op = GateOp.not) (hu : ∀ i : Fin gs.length, (gs.get i).op = GateOp.not → i = j)
    (hlt : w < n + j.val) (hhead : ∃ r : List ℕ, (gs.get j).inputs = w :: r)
    (he : ∀ t (x : Fin n → Bool), Rim.orig gs x (o t) = decide (∃ v ∈ L t, x v = true))
    (hco : Freeze.value gs w (Rim.off (L i0)) = false)
    (U : Finset ℕ) (hcU : (n-1)*q ≤ U.card)
    (hU : ∀ k ∈ U, k ∈ Finset.Ico n (n+gs.length) ∧ k ≠ n+j.val ∧
      (∀ i : Fin gs.length, k = n+i.val → n+j.val ∉ (gs.get i).inputs) ∧
      (Count.outsideSupport ⟨gs,0⟩ (L i0) k).Nonempty) :
    n*q + (Finset.univ.filter (fun i : Fin gs.length => n+j.val ∈ (gs.get i).inputs)).card + 1 ≤ gs.length ∧
    (n ≤ w → (Count.support (n := n) ⟨gs,0⟩ w).card ≤ 1 →
      n*q + (Finset.univ.filter (fun i : Fin gs.length => n+j.val ∈ (gs.get i).inputs)).card + 2 ≤ gs.length) := by
  classical
  let R := L i0
  let V := Rim.charge gs j R
  have hsup (x : Fin n → Bool) (k : ℕ) : Rim.orig gs x k = true → Rim.up gs j x k = true :=
    Freeze.upper_dominates gs j hg hu x k
  have hnot : Rim.orig gs (Rim.off R) (n+j.val) = true := by
    change Freeze.value gs (n + j.val) (Rim.off R) = true
    rw [Freeze.not_value gs j _ hj w hlt hhead, hco]
    rfl
  have hproper : ∃ p : Fin n, p ∉ R := by
    by_contra! h
    have heq : R = Finset.univ := Finset.eq_univ_of_forall h
    have hs0 : R.card = q + 1 := hs i0
    rw [heq, Finset.card_univ, Fintype.card_fin] at hs0
    nlinarith
  have cV : q ≤ V.card := by
    have h := Rim.charge_card gs j R (o i0) hg hu hsup (he i0) hnot
    have hsize : R.card = q+1 := hs i0
    change q ≤ (Rim.charge gs j R).card
    omega
  have spec := Rim.charge_spec gs j R hproper hb hsup
  have dUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro k hk hv
    obtain ⟨p, hp⟩ := (hU k hk).2.2.2
    rw [(spec k hv).2.2.2.2.2] at hp
    exact Finset.notMem_empty _ hp
  have rV (i : Fin gs.length) (hr : n + j.val ∈ (gs.get i).inputs) : n+i.val ∉ V := by
    intro h
    obtain ⟨i', e, _, h'⟩ := (spec _ h).2.2.1
    have eq : i = i' := Fin.ext (by omega)
    exact h' (eq ▸ hr)
  have h := Tally.bound q n (by omega) gs j w hlt hb U V hcU cV
    (fun k hk => (hU k hk).1) (fun k hk => (spec k hk).1) dUV
    (fun hk => (hU _ hk).2.1 rfl) (fun hk => (spec _ hk).2.1 rfl)
    (fun i hr hi => (hU _ hi).2.2.1 i rfl hr) rV
  refine ⟨h.1, fun hw hthin => h.2 hw ?_ ?_⟩
  · intro hwU
    obtain ⟨p, hp⟩ := (hU _ hwU).2.2.2
    obtain ⟨hmem, hnotmem⟩ := Finset.mem_sdiff.mp hp
    exact hnotmem (Freeze.singleton_support_inside gs j hg hu w hlt R hco p
      ((Count.mem_support ⟨gs,0⟩ w p).mp hmem))
  · exact Rim.not_mem_of_thin gs j R w (fun x => Freeze.upper_before gs j x w hlt) hthin

end PEqualNP.Outside.L_meta_1649.Finish

open PEqualNP.Outside.L_meta_1649

theorem PEqualNP.Outside.L_meta_1649 : ∀ (q N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N),
    2 ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : Fin N → ℕ) (j : Fin gates.length) (hw : ℕ),
    (∀ gt ∈ gates, (gt.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ gt.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ gt.inputs.length ≤ 2) →
    (∀ (i : Fin gates.length), ∀ w ∈ (gates.get i).inputs, w < N + (i : ℕ)) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    hw < N + (j : ℕ) → (∃ r : List ℕ, (gates.get j).inputs = hw :: r) →
    (∀ (t : Fin N) (x : Fin N → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o t⟩ (List.ofFn x) = decide (∃ v ∈ L t, x v = true)) →
    (∃ x : Fin N → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn x) = true) →
    PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn (fun v : Fin N => decide (v ∉ L i0))) = false →
    N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 1 ≤ gates.length ∧
    (N ≤ hw → (Finset.univ.filter (fun p : Fin N => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, hw⟩ (List.ofFn (fun v : Fin N => decide (v = p))) = true)).card ≤ 1 →
      N * q + (Finset.univ.filter (fun i : Fin gates.length => (N + (j : ℕ)) ∈ (gates.get i).inputs)).card + 2 ≤ gates.length) := by
  intro q n L i0 hq hn hsize hinter _ gs o j w hg hback hj huniq hlt hhead he _ hco
  have hoff := Freeze.not_off_line gs j hg huniq hj w hlt hhead (L i0) hco
  obtain ⟨u, hc, hu⟩ := Count.other_rows q n L i0 hq hn hsize hinter gs o j hg hback huniq he hoff
  exact Finish.tally q n L i0 hq hn hsize gs o j w hg hback hj huniq hlt hhead he hco u hc hu
