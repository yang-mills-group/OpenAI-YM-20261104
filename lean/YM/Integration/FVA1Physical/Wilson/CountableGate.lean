import YM.Integration.FVA1Physical.Wilson.SceneReadout

/-! A finite menu at each moving RG stage. The resulting numerical delay pays
for every fixed field radius, perturbative order and positive slack eventually. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset Lattice RG YM.Wilson Tree Precision Exterior MSbar MSbar.Heath
open scoped Classical
variable {G : Gauge}

def margin (i : ℕ) := ((i:ℝ)+2)⁻¹
lemma margin_pos (i : ℕ) : 0 < margin i := by unfold margin; positivity
lemma margin_lt_one (i : ℕ) : margin i < 1 := by
  unfold margin
  rw [inv_lt_one₀ (by positivity)]
  linarith only [Nat.cast_nonneg (α:=ℝ) i]

lemma margin_fits (p i : ℕ) : 0 < (p:ℝ)+1-margin i := by
  linarith only [margin_lt_one i,Nat.cast_nonneg (α:=ℝ) p]

lemma margin_eventually {η : ℝ} (hη : 0 < η) : ∃ i : ℕ, margin i ≤ η := by
  obtain ⟨i,hi⟩ := exists_nat_ge η⁻¹
  exact ⟨i,(inv_anti₀ (inv_pos.mpr hη) (hi.trans (by linarith : (i:ℝ) ≤ (i:ℝ)+2))).trans_eq (inv_inv η)⟩

def countableGate (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  ∑ t : Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1),
    |forestGate J cle simple (Nat.cast_nonneg (α:=ℝ) t.1.val)
      (margin_fits t.2.1.val t.2.2.val) (half_pos (margin_pos t.2.2.val)) H H' P K|

theorem countableGate_le (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) {d p i : ℕ}
    (hd : d ≤ H.order) (hp : p ≤ H.order) (hi : i ≤ H.order) :
    forestGate J cle simple (Nat.cast_nonneg (α:=ℝ) d) (margin_fits p i)
      (half_pos (margin_pos i)) H H' P K ≤ countableGate J cle simple H H' P K := by
  let t : Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) :=
    (⟨d,Nat.lt_succ_iff.mpr hd⟩,⟨p,Nat.lt_succ_iff.mpr hp⟩,⟨i,Nat.lt_succ_iff.mpr hi⟩)
  let bill (a : Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1)) :=
    forestGate J cle simple (Nat.cast_nonneg (α:=ℝ) a.1.val) (margin_fits a.2.1.val a.2.2.val)
      (half_pos (margin_pos a.2.2.val)) H H' P K
  exact (le_abs_self (bill t)).trans (single_le_sum (fun a _=>abs_nonneg (bill a)) (mem_univ t))

end YM.Integration.FVA1Physical.Wilson
