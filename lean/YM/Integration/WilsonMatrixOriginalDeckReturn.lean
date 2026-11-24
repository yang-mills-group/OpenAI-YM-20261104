import YM.Integration.WilsonMatrixOriginalDeckMixed

/-! Read an arbitrary second scale from the measured mixed rows on one fixed compact spatial test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckReturn
open Matrix Filter Set MeasureTheory Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Extraction Table Spec Climb FVA2 FVA2.ColorCode OPE.Levy RG11.Fields PhysicalNext.Repeat.Legato
open scoped Classical Topology Matrix BigOperators

variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- All intermediate physical changes compose on the complete independent field space. -/
theorem compose (r s t:ℝ) :
    WilsonMatrixOriginalDeckMixed.change B J h r s * WilsonMatrixOriginalDeckMixed.change B J h s t =
      WilsonMatrixOriginalDeckMixed.change B J h r t := by
  classical
  let E := WilsonMatrixOriginalDeckColumns.basis R.family B h
  let T (a b:ℝ) := (J a h).symm.toLinearMap.comp (J b h).toLinearMap
  have kernel (a b:ℝ) : WilsonMatrixOriginalDeckMixed.change B J h a b = LinearMap.toMatrix E E (T a b) := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    rfl
  have roll : (T r s).comp (T s t)=T r t := by
    ext v
    simp only [T,LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  rw [kernel,kernel,kernel,←LinearMap.toMatrix_comp,roll]

/-- On the selected test the true mixed physical measurement determines every entry of the relative frame.
The same fixed inverse bounds the error of any proposed signed mixed measurement column by column. -/
theorem measured (L:PhysMS.Leading F J) (M:MS_Data G O) {p:E4} (hp:(0:E4)≠p)
    (U:Set (Points 2)) (near:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃ (g:Test 2) (c:ℝ), 0<c ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧
      (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      ∀ᶠ r in Trace.Pilot.trail, ∀s:ℝ,
        let A := WilsonMatrixOriginalDeckGram.bank B F J h g r
        let cross := WilsonMatrixOriginalDeckMixed.mixed B J h g r s
        let trueChange := WilsonMatrixOriginalDeckMixed.change B J h r s
        A⁻¹*cross=trueChange ∧
        ∀(trial:Matrix (Glyph B h) (Glyph B h) ℂ) (b:Glyph B h),
          (∑i,‖trueChange i b-trial i b‖) ≤ c*(∑i,‖cross i b-(A*trial) i b‖) := by
  classical
  obtain ⟨g,c,hc,supp,real,center,mass,lim,paid⟩ := WilsonMatrixOriginalDeckInverse.purchased R B F J L M h hp U near
  refine ⟨g,c,hc,supp,real,center,mass,fun μ=>(lim μ).1,?_⟩
  filter_upwards [paid,RG17.positiveLength] with r bill hr
  intro s
  let A := WilsonMatrixOriginalDeckGram.bank B F J h g r
  let cross := WilsonMatrixOriginalDeckMixed.mixed B J h g r s
  let trueChange := WilsonMatrixOriginalDeckMixed.change B J h r s
  have observed : cross=A*trueChange := WilsonMatrixOriginalDeckMixed.observed B F J h g hr s
  refine ⟨?_,?_⟩
  · change A⁻¹*cross=trueChange
    rw [observed,←Matrix.mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp bill.1),Matrix.one_mul]
  · intro trial b
    let z := fun i=>trueChange i b-trial i b
    have read (i:Glyph B h) : (A *ᵥ z) i=cross i b-(A*trial) i b := by
      rw [observed]
      simp only [Matrix.mulVec,Matrix.mul_apply,dotProduct,z,mul_sub,Finset.sum_sub_distrib]
    change (∑i,‖z i‖) ≤ c*(∑i,‖cross i b-(A*trial) i b‖)
    simpa only [←read] using bill.2 z

end YM.Integration.WilsonMatrixOriginalDeckReturn
