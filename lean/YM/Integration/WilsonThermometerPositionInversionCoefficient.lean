import YM.Integration.WilsonThermometerPositionInversionWords
import YM.Integration.WilsonPositionFiniteLaurentCoefficient

/-! The raw finite Wilson face and the independent position publication share a
single normalized Haar integral on this actual finite period. Multiplication
by a common Laurent denominator is performed only at the fixed regulator. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionInversionCoefficient
open Filter Function Finset Lattice Wilson RG PertExtension Orb PertExtension.Series
open PertExtension.Series.Tested XSpace RegulatorIR.FVAAlt2 PhysicalNext.Repeat.Legato
open WilsonThermometerPositionInversionWords
open private sum_ratio from YM.Integration.WilsonThermometerInversionFaces
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [Fintype V] [LinearOrder V] (d : V → ℕ)
    (p : XSpace.Period) (o : V → Site p.side) (g τ : ℝ)
    (v : (j : V) → R.family.label (d j)) (t : V → T → ℂ) (x : T) (L : ℂ →L[ℝ] ℝ)

def sheet (b : Basis R d) (T₀ : p.Tree) :=
  WilsonPositionProgramCopyTop.normalized R p (fun j : ↥(occupied R d b) => d j.val)
    (fun j => lift (o j.val)) (axisOf R d b) T₀

/-- Every term uses its submitted field rank, the independently placed children
and the same true inversion tree. There is no restriction on the signed fit. -/
theorem original (T₀ : p.Tree) (k : ℕ) :
    WilsonThermometerInversionFaces.series R d o g τ v t x L k =
      ∑ b : Basis R d, L (amplitude R d g τ v t x b) *
        (PowerSeries.coeff (k+grade R d b) (sheet R d p o b T₀)).re := by
  let weight := fun b => L (amplitude R d g τ v t x b)
  let O := point R d p o
  have allowed (b : Basis R d) : PreTest (O b) :=
    WilsonPositionProgramCopyTop.allowed R p (fun j : ↥(occupied R d b) => d j.val)
      (fun j => lift (o j.val)) (axisOf R d b)
  have ev := even_iff_two_dvd.mpr p.even
  have phase (u : ℝ) (hu : 0<u) :
      preExpectation (WilsonThermometerInversionFaces.face R d o g τ v t x L u) u =
      ∑ b, weight b * (u⁻¹)^(grade R d b) * preExpectation (O b) u := by
    have hz : WilsonThermometerInversionFaces.face R d o g τ v t x L u =
        ∑ b, (weight b * (u⁻¹)^(grade R d b)) • O b := by
      funext U
      rw [WilsonThermometerPositionInversionWords.placed R d p o g τ v t x L u hu.ne']
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,weight,O]
    rw [hz,sum_ratio O (fun b => (allowed b).continuous)]
  have read := WilsonPositionFiniteLaurentCoefficient.identify (grade R d) weight _ _
    (fun b u => preExpectation (O b) u) (fun b => Orb.diag (restrictedO (O b)))
    (WilsonThermometerInversionFaces.finite R d o g τ v t x L ev)
    (fun b => before_tree_formula ev (traySpec G) (allowed b)) phase k
  rw [read]
  apply sum_congr rfl
  intro b _
  have one := YM.FVA2.XPos.genuine_X T₀ (allowed b)
  change _ = _ * (PowerSeries.coeff (k+grade R d b)
    (XSpace.Bare.normalized T₀ G (XSpace.Taylor.expandTaylor (T₀.basis G)
    (Complex.ofRealCLM ∘ (O b ∘ T₀.links))))).re
  rw [one,PowerSeries.coeff_map,PowerSeries.coeff_mk,add_comm k]
  rfl
end YM.Integration.WilsonThermometerPositionInversionCoefficient
