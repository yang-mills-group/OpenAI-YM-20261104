import YM.Integration.FVA1Physical.Round2.FormalFieldTruncation
import YM.Integration.FVA1Physical.Wilson.EmittedDegree

/-! No extra action orders are needed to pay the full spatial degree of the
coefficients retained in the physical comparison scene. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Finset Lattice MvPolynomial MSbar MSbar.Whisk MSbar.Cacao MSbar.CrossH MSbar.Rolling
open MSbar.Lis MSbar.Mosaic MSbar.Heath MSbar.Heath.Stock MSbar.Duel Push.Uniform
open MSbar.Bakery MSbar.Bakery.Film MSbar.Kelvin Tree
open YM.Integration.FVA1Physical.Wilson RG YM.Wilson Precision Exterior RGComparison.Core16.Spool
open scoped Classical Topology BigOperators
variable {G:Gauge} {ι:Type} [Fintype ι]

theorem emitted_degree_exact_order (A:Issue G) (χ:ChartRatio G) (J:ι→Lamp G) (o:ι → Site A.f)
    (part:Bool) (p:ℕ) (kind:Kind A.T) (profile:Expanse A.T 1 p) (pd:(mold A.pre A.F A.v).PosDef)
    (i:ℕ) (hi:i≤p) : (PowerSeries.coeff i (emittedRows A χ (jointFieldBank J A o part) p)).totalDegree ≤ emittedDegree p := by
  let B:=cropIssue A p
  have base:Kind B.T:=by
    unfold Kind at kind
    change PowerSeries.coeff 0 (cropAction p A.T)=0
    simpa only [cropAction,PowerSeries.coeff_mk,zero_le,if_true] using kind
  have all:Expanse B.T 1 (p+1+p):=by
    change Expanse (cropAction p A.T) 1 (p+1+p)
    constructor
    intro j _
    by_cases h:j≤p
    · simpa only [cropAction,PowerSeries.coeff_mk,if_pos h] using profile.profile j h
    simp [cropAction,h]
  have eqn:=crop_action_prefix A χ p (jointFieldBank J A o part) kind pd i hi
  have target:=emitted_field_degree B χ J o part p base all hi
  simp only [emittedRows,PowerSeries.coeff_map] at target ⊢
  rw [eqn]
  exact target

theorem rendered_degree {σ:Type} (B:PowerSeries (Pot σ)) (p M:ℕ) (g:ℝ)
    (caps:∀ i≤p,(PowerSeries.coeff i B).totalDegree ≤ M) :
    (renderedPolynomial B p g).totalDegree ≤ M := by
  apply totalDegree_finsetSum_le
  intro i hi
  exact (MvPolynomial.totalDegree_smul_le _ _).trans (caps i (Nat.lt_succ_iff.mp (mem_range.mp hi)))

end YM.Integration.FVA1Physical.Round2.Curvature
