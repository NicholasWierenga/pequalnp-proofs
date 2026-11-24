import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1745_2
    (peel : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (S : Finset (Fin n)) (b : ℕ),
      (∃ x y, g x ≠ g y) →
      (∀ i ∈ S, ∀ x, g (Function.update x i false) = g x) →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => g x || decide (∃ i ∈ S, x i = true)) b →
      ∃ t, t + S.card ≤ b ∧ PEqualNP.MetaComplexity.HasCircuitSize n g t)
    (pure : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
      (e : (Fin n → Bool) → Bool),
      (∀ v ∉ S, (G.neighborSet v).ncard = 3) →
      (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 7 ≤ p.length) →
      (∀ u v, G.Adj u v → u ∉ S) → (∃ u v, G.Adj u v) →
      (∀ x, e x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) →
      ∀ t, PEqualNP.MetaComplexity.HasCircuitSize n e t →
        ∃ v ∉ S, ∃ u, u + 4 ≤ t ∧ PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x => e (Function.update x v false)) u)
    (attach : ∀ (n : ℕ) (g : (Fin n → Bool) → Bool) (s : ℕ) (S : Finset (Fin n)),
      PEqualNP.MetaComplexity.HasCircuitSize n g s →
      PEqualNP.MetaComplexity.HasCircuitSize n
        (fun x => g x || decide (∃ i ∈ S, x i = true)) (s + S.card)) :
∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : Finset (Fin x1)) (x4 : (Fin x1 → Bool) → Bool) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   (∀ x6 ∉ x3, (x2.neighborSet x6).ncard = (3 : ℕ)) →     (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) →       (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x3) →         (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) →           (∀ (x10 : Fin x1 → Bool), x4 x10 = Bool.true ↔ (∃ x11 ∈ x3, x10 x11 = Bool.true) ∨ ∃ (x11 : Fin x1) (x12 : Fin x1), x2.Adj x11 x12 ∧ x10 x11 = Bool.true ∧ x10 x12 = Bool.true) →             PEqualNP.MetaComplexity.FanInTwo x5 →               PEqualNP.MetaComplexity.circuitFun x1 x5 = x4 →                 (∀ (x13 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x4 x13 → x5.size ≤ x13) →                   (∀ x14 ∉ x3,                       have x16 : List PEqualNP.CircuitLowerBounds.Gate := List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x14) x5.gates;                       x16.length ≤ (3 : ℕ) ∧ (x16.length = (3 : ℕ) → ∀ x18 ∈ x16, x18.op = PEqualNP.CircuitLowerBounds.GateOp.or)) →                     ∃ x15 ∉ x3, ∃ (x16 : ℕ), x16 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x17 : Fin x1 → Bool) => x4 (Function.update x17 x15 Bool.false)) x16 := by
  classical
  intro n G S f C hdegree hgirth hdisj hedge hf hfan hfun _hmin _hread
  let e : (Fin n → Bool) → Bool := fun x =>
    decide (∃ (u v : Fin n), G.Adj u v ∧ x u = true ∧ x v = true)
  have he (x) : e x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simp [e]
  have hcombine (x) : f x = (e x || decide (∃ i ∈ S, x i = true)) := by
    apply Bool.eq_iff_iff.mpr
    simp only [hf, Bool.or_eq_true, decide_eq_true_eq, he, or_comm]
  have hnc : ∃ x y, e x ≠ e y := by
    refine ⟨fun _ => true, fun _ => false, ?_⟩
    obtain ⟨u,v,huv⟩ := hedge
    have hyes := (he (fun _ => true)).mpr ⟨u,v,huv,rfl,rfl⟩
    simp [hyes, e]
  have hind (i) (hi : i ∈ S) (x) : e (Function.update x i false) = e x := by
    apply Bool.eq_iff_iff.mpr
    rw [he, he]
    constructor <;> rintro ⟨u,v,ha,hu,hv⟩ <;> refine ⟨u,v,ha,?_,?_⟩
    all_goals
      have hui : u ≠ i := fun h => hdisj u v ha (h ▸ hi)
      have hvi : v ≠ i := fun h => hdisj v u ha.symm (h ▸ hi)
      first | simpa [Function.update_of_ne hui] using hu | simpa [Function.update_of_ne hvi] using hv
  have hc : PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x => e x || decide (∃ i ∈ S, x i = true)) C.size := by
    refine ⟨C, hfan, le_rfl, ?_⟩
    intro x
    exact (congrFun hfun x).trans (hcombine x)
  obtain ⟨t,ht,htc⟩ := peel n e S C.size hnc hind hc
  obtain ⟨v,hv,u,hu,huc⟩ := pure n G S e hdegree hgirth hdisj hedge he t htc
  refine ⟨v, hv, u + S.card, by omega, ?_⟩
  have hlit (x : Fin n → Bool) :
      (∃ i ∈ S, (Function.update x v false) i = true) ↔ ∃ i ∈ S, x i = true := by
    constructor <;> rintro ⟨i,hi,h⟩ <;> refine ⟨i,hi,?_⟩
    all_goals
      have hiv : i ≠ v := fun eq => hv (eq ▸ hi)
      simpa [Function.update_of_ne hiv] using h
  have heq : (fun x => e (Function.update x v false) || decide (∃ i ∈ S, x i = true)) =
      (fun x => f (Function.update x v false)) := by
    funext x
    rw [hcombine, decide_eq_decide.mpr (hlit x)]
  exact heq ▸ (attach n (fun x => e (Function.update x v false)) u S huc)
