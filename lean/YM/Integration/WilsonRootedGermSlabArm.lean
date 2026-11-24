import YM.Integration.WilsonMatrixOriginalGermNearFields
import YM.Integration.WilsonMatrixOriginalGermReturnRegular

/-! The full earlier signed forced insertion is bounded on the genuine original
mesh interval by transporting its own terminal Wilson observable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedGermSlabArm
open Lattice Wilson RG RG17 Spec Table FVA2 PhysicalNext.Repeat.Legato
open Extra.Multi.BasisCost Next.UVStress WilsonInheritedRegisteredField Trace.Physical.GermGraph Next.Rank.Price
open WilsonMatrixOriginalGermNearFields
open scoped Classical
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
    (F : Spec.Final R.family f S) (L : Layout F)
local notation "β" => R.family.path.levels.clock.hatBeta

theorem original (r : ℝ) {N p e : ℕ} (w : R.family.label 4) (age : R.family.ref 4 ≤ L.level r)
    (live : L.level r ≤ N) (width : R.family.S.a (L.level r)/R.family.S.a N ≤ β (L.level r))
    (heat : β N ≤ β (L.level r)^2) (cheap : stock R.family (L.level r) ≤ β (L.level r))
    (fee : quota R.family 4 (L.level r) N p (atRef L 4 r (N,p) w) ≤
      R.family.S.a (L.level r)^4*β (L.level r)^e) (x : Site (R.family.side (L.level r) p))
    (U : Config G (R.family.side (L.level r) p)) :
    ‖forced R.makes live (atRef L 4 r (N,p) w) x U‖ ≤
      (price (R.family.localSection 4)+3)*β (L.level r)^(exponent R e) := by
  let a := atRef L 4 r (N,p) w
  let i := L.level r
  have capUV := cutoff R F L r (e:=e) (M:=1) w age live width heat (by simpa only [mul_one] using fee)
  have hFull : ‖field R.makes live a x U‖ ≤ cap R i e 1 := by
    rw [←WilsonInheritedRegisteredField.original R.makes live age a x]
    exact actualTransport_norm_le R.family R.makes le_rfl (capUV ((R.family.S.toDepth live p).embed x)) live U
  have hReg := WilsonMatrixOriginalGermReturnRegular.cap R age live cheap e a fee x U
  have split : forced R.makes live a x U = field R.makes live a x U-regular R.makes live a x U := by
    rw [separated R.makes live a x U, add_sub_cancel_left]
  have power : β i^(e+1) ≤ β i^(exponent R e) :=
    pow_le_pow_right₀ (R.family.path.levels.fits.delayed i).le (by unfold exponent; omega)
  rw [split]
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ cap R i e 1 + 3*β i^(exponent R e) := add_le_add hFull (hReg.trans (mul_le_mul_of_nonneg_left power (by norm_num)))
    _ = _ := by unfold cap; ring

end YM.Integration.WilsonRootedGermSlabArm
