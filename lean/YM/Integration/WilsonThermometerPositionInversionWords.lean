import YM.Integration.WilsonThermometerProgramSubmittedWords
import YM.Integration.WilsonThermometerInversionFaces
import YM.Integration.WilsonPositionProgramCopyTop

/-! The honest compact-period Wilson integrand expressed in the submitted
position words, before integration over the physical Haar measure. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionInversionWords
open Finset Function Lattice Wilson RG XSpace RegulatorIR.FVAAlt2
open PhysicalNext.Repeat.Legato WilsonCoeffUV
open WilsonThermometerProgramSubmittedWords
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [Fintype V] [LinearOrder V] (d : V → ℕ)
    (p : XSpace.Period) (o : V → Site p.side) (g τ : ℝ)
    (v : (j : V) → R.family.label (d j)) (t : V → T → ℂ) (x : T)

abbrev Basis := (j : V) → Option (R.family.labels.level (d j)).Index
def occupied (b : Basis R d) := univ.filter fun j => (b j).isSome
def axisOf (b : Basis R d) (j : ↥(occupied R d b)) := (b j.val).getD 0
def grade (b : Basis R d) := Kick.depthF univ (fun j : ↥(occupied R d b) => d j.val) (axisOf R d b)
def amplitude (b : Basis R d) := ∏ j, dose R d g τ v t x j (b j)
def point (b : Basis R d) : Config G p.side → ℝ :=
    WilsonPositionProgramCopyTop.planted R p (fun j : ↥(occupied R d b) => d j.val)
      (fun j => lift (o j.val)) (axisOf R d b)

private theorem word (b : Basis R d) (u : ℝ) (U : Config G p.side) :
    (∏ j, row R d u U j (o j) (b j)) =
      ((u : ℂ)^(grade R d b))⁻¹ * (point R d p o b U : ℂ) := by
  let S := occupied R d b
  have shrink := Finset.prod_subset (s₁:=S) (s₂:=univ)
    (f:=fun j => row R d u U j (o j) (b j)) (subset_univ _)
  rw [← shrink (fun j _ hj => by
    cases eqn : b j with
    | none => rfl
    | some a => exact (hj (by simp [S,occupied,eqn])).elim), ←Finset.prod_coe_sort]
  have slot (j : ↥S) : b j.val = some (axisOf R d b j) := by
    cases eqn : b j.val with
    | none =>
      have live : (b j.val).isSome := (Finset.mem_filter.mp j.property).2
      simp [eqn] at live
    | some a => simp [axisOf,eqn]
  have sheet := congrFun (Boot.combined R (univ : Finset ↥S) (fun j => d j.val)
    (axisOf R d b) (fun j : ↥S => lift (o j.val)) p.side) U
  simp only [Function.comp_apply, wrap_lift, Finset.prod_apply] at sheet
  change _ = ((u:ℂ)^(grade R d b))⁻¹ * ((Kick.topMark (Lodge.basisR R) univ _ _
    p.side (fun j : ↥S => lift (o j.val)) U : ℝ) : ℂ)
  rw [sheet]
  calc
    _ = ∏ j : ↥S, ((u:ℂ)^ActualRunGradedKernels.rank R (d j.val) (axisOf R d b j))⁻¹ *
        (R.family.localSection (d j.val)).places (Pi.single (axisOf R d b j) 1) (o j.val) U := by
      apply Finset.prod_congr rfl
      intro j _
      rw [slot j]
      rfl
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
      congr 2
      exact Finset.prod_pow_eq_pow_sum _ _ _

/-- The original seven-face preparation uses the same pre-elected field amplitudes
at all positive input temperatures. A proper face takes its index subtype. -/
theorem placed (L : ℂ →L[ℝ] ℝ) (u : ℝ) (hu : u ≠ 0) (U : Config G p.side) :
    WilsonThermometerInversionFaces.face R d o g τ v t x L u U =
      ∑ b : Basis R d, L (amplitude R d g τ v t x b) *
        (u⁻¹)^(grade R d b) * point R d p o b U := by
  let X := fun j => ∑ a : WilsonThermometerDeclaredSeeds.Choice R d j,
    WilsonThermometerFrozenCopies.word R d g τ v t
      (WilsonThermometerDeclaredSeeds.entry R d j a) u x (o j) U
  let div := fun j => (u^(d j+1))⁻¹
  have one (j : V) : ((div j:ℝ):ℂ)*X j =
      ∑ b, dose R d g τ v t x j b * row R d u U j (o j) b := by
    have coef := WilsonThermometerProgramBasis.placed R d g τ v t j u x (o j) U hu
    change (((u^(d j+1))⁻¹:ℝ):ℂ) * _ = _
    rw [Complex.ofReal_inv]
    rw [coef,Fintype.sum_option]
    change t j x * v j 0 + _ = t j x * v j 0 * 1 + _
    rw [mul_one]
    apply congrArg (fun w : ℂ => t j x * v j 0 + w)
    apply Finset.sum_congr rfl
    intro a _
    simp only [dose,row,WilsonThermometerProgramBasis.weight,div_eq_mul_inv,mul_pow,
      Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_inv,inv_pow]
    ring
  have all : (∏ j, div j) • (∏ j, X j) =
      ∏ j, ∑ b, dose R d g τ v t x j b * row R d u U j (o j) b := by
    rw [Complex.real_smul,Complex.ofReal_prod,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => one j)
  change (∏ j, div j) * L (∏ j, X j) = _
  rw [← smul_eq_mul,← L.map_smul,all,Fintype.prod_sum,map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_mul_distrib,word R d p o b u U]
  have pull := L.map_smul ((u⁻¹)^(grade R d b)* point R d p o b U) (amplitude R d g τ v t x b)
  simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_inv,
    smul_eq_mul,inv_pow] at pull
  change L (amplitude R d g τ v t x b * _) = _
  rw [← mul_assoc, mul_comm (amplitude R d g τ v t x b),mul_assoc]
  convert pull using 1 <;> ring_nf
end YM.Integration.WilsonThermometerPositionInversionWords
