import YM.Integration.WilsonEmittedCouplingSlice
import YM.Comparison.Density.Mirrors.Anchor

/-! Cutting the original signed marked word leaves both the original
group function and its named root. The whole short sum sees one common
axial patch, including every original operand's own complete healthy mask. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedCutGrouping
open Finset Function Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open Comparison.Density.Mirrors AnalyticBridge.SectorAffine.Offset
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
variable {P : Passport n V} {Γ : Census V} (M : ι → Row P Γ G X)
variable (q : ι → ℂ) (grades : V → ℕ) {σ : ℝ} {p : ℕ}
variable (staff : Air.Staff M q grades σ p) (s : Γ.Mode)

def picked (i : ι) : Prop := s=(M i).mode

def early (m : ℕ) (i : ι) : Prop := picked M s i ∧ (M i).length < m

def late (m : ℕ) (i : ι) : Prop := picked M s i ∧ m ≤ (M i).length

include staff in
theorem divided (m : ℕ) (g : ℝ) (U : Config G n) :
    Air.sums M q (picked M s) g U =
      Air.sums M q (early M s m) g U + Air.sums M q (late M s m) g U := by
  rw [Air.sums,Air.sums,Air.sums,←Summable.tsum_add
    (Air.usable_all M q grades staff U g (early M s m))
    (Air.usable_all M q grades staff U g (late M s m))]
  apply tsum_congr
  intro i
  by_cases h : picked M s i
  · by_cases hm : (M i).length < m
    · simp [early,late,h,hm,Nat.not_le_of_lt hm]
    · simp [early,late,h,hm,Nat.le_of_not_gt hm]
  · simp [early,late,h]

theorem positioned (B : BudgetPoint) (m : ℕ) (v : V) (hv : v∈s.val)
    {i : ι} (hi : early M s m i) :
    (M i).ground B ⊆ neighborhood (2*(B.B+1+m)) (P.origin v) := by
  intro y hy
  have ho : P.origin v ∈ (M i).ground B := (M i).heard _ v (hi.1 ▸ hv) (P.born v)
  have l := (M i).near B.B (P.origin v) ho
  have r := (M i).near B.B y hy
  rw [separation_comm] at l
  apply (neighborhood_iff ..).2
  have d := separation_triangle (P.origin v) (M i).center y
  unfold Row.radius at l r
  have hm := hi.2
  omega

include staff in
theorem local_field (B : BudgetPoint) (m : ℕ) (v : V) (hv : v∈s.val) (g : ℝ) :
    LocalOn (neighborhood (2*(B.B+1+m)) (P.origin v))
      (Air.sums M q (early M s m) g) ∧
    GaugeInvariant (Air.sums M q (early M s m) g) ∧
    Measurable (Air.sums M q (early M s m) g) := by
  refine ⟨?_,?_,(Air.continuous M q grades staff g (early M s m)).measurable⟩
  · intro U W hw
    apply tsum_congr
    intro i
    by_cases hi : early M s m i
    · simp only [if_pos hi,ScatterR.familyAt,Sunrise.Loan.letter]
      have eqn := ((M i).regular B 1).sites U W (agrees_mono hw (positioned M s B m v hv hi))
      simpa only [Row.grain,one_zpow,one_mul] using
        congrArg (fun z : ℝ => q i * ((g^(M i).lamp.stamp*z:ℝ):ℂ)) eqn
    · simp [hi]
  · intro z U
    apply tsum_congr
    intro i
    by_cases hi : early M s m i
    · simp only [if_pos hi,ScatterR.familyAt,Sunrise.Loan.letter]
      have eqn := ((M i).regular B 1).symmetry z U
      simpa only [Row.grain,one_zpow,one_mul] using
        congrArg (fun u : ℝ => q i * ((g^(M i).lamp.stamp*u:ℝ):ℂ)) eqn
    · simp [hi]

end YM.Integration.WilsonEmittedCutGrouping
