import YM.Integration.WilsonCenteredNestedActual
import YM.Integration.WilsonMacroscopicLoggedRow

/-! On a comparable vertex its actual public coefficient already has a
ticketed polylogarithmic price through the matrix on the chosen run. The
degree of the logarithm is set before any independent comparison order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedLoggedRow
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Atom OPE.Log
open Filter Extraction Table Spec
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def shell (r : ℝ) := 1+|Real.log r|

theorem shell_one (r : ℝ) : 1 ≤ shell r := by unfold shell;linarith [abs_nonneg (Real.log r)]

theorem original (fac : Services C f S) (log : SingleLog F Q.port) {n : ℕ} (v : Fin n→S.Tag)
    (m : ℕ) (c : Q.channels m) {M η : ℝ} (Mn : 0 ≤ M) (ηp : 0 < η) :
    ∃ (k : ℕ) (B : ℝ),0 ≤ B ∧ ∀ᶠ r:ℝ in 𝓝[>]0,∀ (x : Fin n→E4) (o : E4),
      (∀ i,‖x i-o‖ ≤ M*r) → (∀ i j,i ≠ j → η*r ≤ ‖x i-x j‖) →
      ‖express Q m c x v o‖ ≤ B * shell r^k * (r^m / ∏ i,r^(v i).1) := by
  obtain ⟨k,B,Bp,paid⟩ := WilsonMacroscopicLoggedRow.original F Q (voices v) fac Mn ηp m
    (WilsonMacroscopicLoggedRow.issued F Q (voices v) log Mn ηp m)
  let D := Q.stratum m
  let read : S.Field m →L[ℂ] ℂ := (((Q.basis m).coord c).comp D.subtype.leftInverse).toContinuousLinearMap
  obtain ⟨K,Kp,bounded⟩ := read.bound
  refine ⟨k,K*B,mul_nonneg Kp.le Bp.le,?_⟩
  filter_upwards [paid,(show ∀ᶠ r:ℝ in 𝓝[>]0,0<r from self_mem_nhdsWithin),
    mem_nhdsWithin_of_mem_nhds (ge_mem_nhds (show (0:ℝ)<1 by norm_num))] with r atR rp r1 x o close clear
  have sheet := atR x o ⟨close,clear⟩
  have lr : Real.log r ≤ 0 := Real.log_nonpos rp.le r1
  have same : badge r = shell r := by unfold badge OPE.run shell;rw [abs_of_nonpos lr]
  rw [same,Real.rpow_sub rp,Real.rpow_natCast] at sheet
  have scales : r^weight (degrees v) = ∏ i,r^(v i).1 := by
    rw [Finset.prod_pow_eq_pow_sum,←Real.rpow_natCast]
    congr 1
    simp only [weight,degrees,Nat.cast_sum]
  rw [scales] at sheet
  let z : D := ⟨Q.fresh m x o (voices v),Q.fresh_mem m x o (voices v)⟩
  have seen := bounded z.val
  change ‖(Q.basis m).coord c (D.subtype.leftInverse z.val)‖ ≤ _ at seen
  have back : D.subtype.leftInverse z.val = z := LinearMap.leftInverse_apply_of_inj D.ker_subtype z
  rw [back] at seen
  exact seen.trans ((mul_le_mul_of_nonneg_left sheet Kp.le).trans (le_of_eq (by ring)))

end YM.Integration.WilsonCenteredNestedLoggedRow
