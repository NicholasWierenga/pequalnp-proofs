import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1680.Const

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

private def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

private def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

private def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

private def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

private lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

private lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

private def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

private def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

private lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

private lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

private lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

private lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

private lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

private def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

private lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

private lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

private lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

private lemma deleteWire {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length) (r : Bool ⊕ ℕ) (hrv : statValid (m + j) r)
    (hconst : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      statVal (wiresFrom (C.gates.take j) (List.ofFn x)) r)
    (hnc : ∃ x x' : Fin m → Bool, circuitFun m C x ≠ circuitFun m C x') :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  set gs₁ := C.gates.take j with hgs₁
  set gs₂ := C.gates.drop (j + 1) with hgs₂
  have hsplit : C.gates = gs₁ ++ [C.gates[j]] ++ gs₂ := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: gs₂ := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [hgs₁, List.append_assoc, List.singleton_append] using h1.symm
  set init : List (Bool ⊕ ℕ) :=
    List.ofFn (fun i : Fin (m + j) => Sum.inr (i : ℕ)) ++ [r] with hinit
  set acc := elimPass m gs₂ (init, gs₁) with hacc
  have hinv : ∀ x : Fin m → Bool,
      ElimInv m (List.ofFn x) (wiresFrom C.gates (List.ofFn x)) acc := by
    intro x
    rw [hsplit, wiresFrom_append, hacc]
    apply elimInv_pass m (List.ofFn x) gs₂ _ (init, gs₁)
      (fun g hg => (hok g (List.mem_of_mem_drop hg)))
    have hlen1 : (wiresFrom gs₁ (List.ofFn x)).length = m + j := by
      rw [wiresFrom_length, List.length_ofFn, hgs₁, List.length_take, Nat.min_eq_left (by omega)]
    have hlen2 : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).length = m + j + 1 := by
      rw [wiresFrom_append, wiresFrom_length, hlen1]; simp
    refine ⟨by simp, by simp [hinit, hlen2], ?_⟩
    intro i
    by_cases h1 : i < m + j
    · have hget : init.getD i (Sum.inl false) = Sum.inr i := by
        rw [hinit, getD_snoc_lt _ _ _ _ (by simp; exact h1), ofFn_getD_lt _ _ _ h1]
      rw [hget]
      refine ⟨by simp [statValid, hgs₁, List.length_take]; omega, ?_⟩
      simp only [statVal]
      rw [wiresFrom_append]
      exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
    · by_cases h2 : i = m + j
      · have hget : init.getD i (Sum.inl false) = r := by
          rw [hinit, getD_snoc_eq _ _ _ _ (by simp; exact h2)]
        rw [hget]
        refine ⟨by
          have hl : gs₁.length = j := by rw [hgs₁, List.length_take, Nat.min_eq_left (by omega)]
          rw [hl]
          exact hrv, ?_⟩
        have hcx := hconst x
        rw [h2]
        have hEq : (wiresFrom (gs₁ ++ [C.gates[j]]) (List.ofFn x)).getD (m + j) false =
            (C.wires (List.ofFn x)).getD (m + j) false := by
          show _ = (wiresFrom C.gates (List.ofFn x)).getD (m + j) false
          conv_rhs => rw [hsplit, wiresFrom_append]
          exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
        rw [hEq, hcx]
      · rw [List.getD_eq_default _ _ (by simp [hinit]; omega),
            List.getD_eq_default _ _ (by omega)]
        exact ⟨trivial, rfl⟩
  have hval : ∀ x : Fin m → Bool,
      statVal (wiresFrom acc.2 (List.ofFn x)) (acc.1.getD C.output (Sum.inl false)) =
        circuitFun m C x := by
    intro x
    exact ((hinv x).2.2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl b =>
    obtain ⟨x, x', hne⟩ := hnc
    have hx := hval x; have hx' := hval x'
    rw [hst] at hx hx'
    exact absurd (hx.symm.trans hx') hne
  | inr out' =>
    refine ⟨⟨acc.2, out'⟩, elimPass_ok m gs₂ _ (fun g hg => (hok g (List.mem_of_mem_take hg))), ?_, ?_⟩
    · show acc.2.length ≤ C.gates.length - 1
      have hlen := elimPass_len m gs₂ (init, gs₁)
      rw [← hacc] at hlen
      simp only at hlen
      have hl1 : gs₁.length = j := by rw [hgs₁, List.length_take, Nat.min_eq_left (by omega)]
      have hl2 : gs₂.length = C.gates.length - (j + 1) := by rw [hgs₂, List.length_drop]
      omega
    · intro x
      have := hval x
      rw [hst] at this
      exact this

theorem reduce (n s : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (hnc : ∃ x y : Fin n → Bool, f x ≠ f y) (hFan : FanInTwo C) (hSize : C.size ≤ s + 1)
    (hcorrect : ∀ x : Fin n → Bool, circuitFun n C x = f x)
    (j : ℕ) (hj : j < C.gates.length)
    (hcases : (∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b) ∨
      (∃ i : Fin n, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = x i)) :
    HasCircuitSize n f s := by
  have hNC : ∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨x, y, by simpa [hcorrect] using hxy⟩
  have hr : ∃ r : Bool ⊕ ℕ, statValid (n + j) r ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false =
        statVal (wiresFrom (C.gates.take j) (List.ofFn x)) r := by
    rcases hcases with ⟨b, hb⟩ | ⟨i, hi⟩
    · exact ⟨Sum.inl b, trivial, hb⟩
    · refine ⟨Sum.inr i.val, by simp only [statValid]; have := i.isLt; omega, ?_⟩
      intro x
      rw [hi x]
      simp only [statVal]
      rw [wiresFrom_getD_lt _ _ _ (by simp), ofFn_getD_lt _ _ _ i.isLt]
  obtain ⟨r, hrv, hrx⟩ := hr
  obtain ⟨D, hD, hsD, hvD⟩ := deleteWire C hFan j hj r hrv hrx hNC
  refine ⟨D, hD, ?_, fun x => (hvD x).trans (hcorrect x)⟩
  unfold Circuit.size at hSize
  omega

end PEqualNP.Outside.L_meta_1680.Const

theorem PEqualNP.Outside.L_meta_1680 : ∀ (n s : ℕ) (f : (Fin n → Bool) → Bool), (∃ x y : Fin n → Bool, f x ≠ f y) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ s + 1 → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = f x) → (∃ j : ℕ, j < C.gates.length ∧ ((∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b) ∨ (∃ i : Fin n, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = x i))) → PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  intro n s f hnc C hFan hSize hcorrect h
  obtain ⟨j, hj, hcases⟩ := h
  exact PEqualNP.Outside.L_meta_1680.Const.reduce n s f C hnc hFan hSize hcorrect j hj hcases
