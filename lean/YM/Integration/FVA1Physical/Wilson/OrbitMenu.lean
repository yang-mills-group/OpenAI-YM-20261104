import YM.Integration.FVA1Physical.Wilson.SceneOrbit
import YM.Integration.FVA1Physical.Wilson.CountableGate

/-! A finite menu at each moving RG stage. The resulting numerical delay pays
for every fixed field radius, perturbative order and positive slack eventually. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset Lattice RG YM.Wilson Tree Precision Exterior MSbar MSbar.Heath
open scoped Classical
variable {G : Gauge}

def orbitMenu (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  ∑ t : Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1),
    |orbitGate J cle simple (Nat.cast_nonneg (α:=ℝ) t.1.val)
      (margin_fits t.2.1.val t.2.2.val) (half_pos (margin_pos t.2.2.val)) H H' P K|

theorem orbitMenu_le (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) {d p i : ℕ}
    (hd : d ≤ H.order) (hp : p ≤ H.order) (hi : i ≤ H.order) :
    orbitGate J cle simple (Nat.cast_nonneg (α:=ℝ) d) (margin_fits p i)
      (half_pos (margin_pos i)) H H' P K ≤ orbitMenu J cle simple H H' P K := by
  let t : Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) :=
    (⟨d,Nat.lt_succ_iff.mpr hd⟩,⟨p,Nat.lt_succ_iff.mpr hp⟩,⟨i,Nat.lt_succ_iff.mpr hi⟩)
  let bill (a : Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1)) :=
    orbitGate J cle simple (Nat.cast_nonneg (α:=ℝ) a.1.val) (margin_fits a.2.1.val a.2.2.val)
      (half_pos (margin_pos a.2.2.val)) H H' P K
  exact (le_abs_self (bill t)).trans (single_le_sum (fun a _=>abs_nonneg (bill a)) (mem_univ t))

end YM.Integration.FVA1Physical.Wilson
