import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1582 : ∀ (q m N : ℕ) (L : Fin N → Finset (Fin N)) (i0 : Fin N) (T0 : Finset (Fin N)),
    3 ≤ q → 3 ≤ m → m ≤ q → N = q ^ 2 + q + 1 → (∀ i : Fin N, (L i).card = q + 1) → (∀ i j : Fin N, i ≠ j → (L i ∩ L j).card = 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃ i : Fin N, p ∈ L i ∧ p' ∈ L i) →
    T0 ⊆ L i0 → T0.card = m →
    (∀ x y : Fin N → Bool, ((∃ v ∈ T0, x v = true) ∨ ∀ v : Fin N, v ∉ L i0 → x v = true) → (∀ v : Fin N, x v = true → y v = true) → ((∃ v ∈ T0, y v = true) ∨ ∀ v : Fin N, v ∉ L i0 → y v = true)) ∧
    (∀ t : Fin N, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t)) v = true)) ∧ (∀ t : Fin N, t ≠ i0 → m - 1 ≤ (T0.filter (fun x => x ∉ L t)).card) ∧
    (∀ x ∈ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v = x)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v = x)) v = true)) ∧ ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0)) v = true) ∧ (∀ r ∈ L i0 \ T0, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L i0 ∨ v = r)) v = true)) ∧
    (∀ t : Fin N, decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t)) v = true) = false ∧
      ∀ p ∈ L t, ((∃ v ∈ T0, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∨ ∀ v : Fin N, v ∉ L i0 → (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) ∧
        decide (∃ v ∈ L t, (fun v : Fin N => decide (v ∉ L t ∨ v = p)) v = true) = true) := by
  intro q m N L i0 T0 _ hm _ _ _ hinter _ hsub hcard
  have bound (t : Fin N) (ht : t ≠ i0) : m - 1 ≤ (T0.filter (fun v => v ∉ L t)).card := by
    have hle : (T0 ∩ L t).card ≤ 1 :=
      (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans (hinter i0 t ht.symm).le
    have he : T0.filter (fun v => v ∉ L t) = T0 \ L t := by ext v; simp
    rw [he]
    have h := Finset.card_sdiff_add_card_inter T0 (L t)
    omega
  have coline (t : Fin N) : (∃ v ∈ T0, v ∉ L t) ∨ ∀ v : Fin N, v ∉ L i0 → v ∉ L t := by
    by_cases h : t = i0
    · subst t
      exact Or.inr fun _ hv => hv
    · have hb := bound t h
      have hpos : 0 < (T0.filter (fun v => v ∉ L t)).card := by omega
      obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
      exact Or.inl ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  refine ⟨?_, ?_, bound, ?_, ?_, ?_, ?_⟩
  · intro x y hx hxy
    rcases hx with ⟨v, hv, hxv⟩ | hall
    · exact Or.inl ⟨v, hv, hxy v hxv⟩
    · exact Or.inr fun v hv => hxy v (hall v hv)
  · intro t
    simpa only [decide_eq_true_eq] using coline t
  · intro x hx
    exact Or.inl ⟨x, hx, decide_eq_true rfl⟩
  · exact Or.inr fun v hv => decide_eq_true hv
  · intro r _
    exact Or.inr fun v hv => decide_eq_true (Or.inl hv)
  · intro t
    refine ⟨by simp, ?_⟩
    intro p hp
    refine ⟨?_, decide_eq_true ⟨p, hp, decide_eq_true (Or.inr rfl)⟩⟩
    rcases coline t with ⟨v, hv, hvt⟩ | hall
    · exact Or.inl ⟨v, hv, decide_eq_true (Or.inl hvt)⟩
    · exact Or.inr fun v hv => decide_eq_true (Or.inl (hall v hv))
