import YM.Integration.WilsonMacroscopicRichRegister
import YM.Integration.WilsonMacroscopicRichSignedInverse

/-! Normalize the genuine physical field coordinates by one independently
presold, held, smooth two-slot register. The old right-hand spectator and
the positive physical law are unchanged. This is a diagnostic prescription,
not a comparison for other observables. -/

noncomputable section
namespace YM.Integration.WilsonOrdinaryPivotFrame
open Function Matrix Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open FVA2 FVA2.ColorCode Extra.FD OPE.Levy RG11.Fields Pert.RawLabels Pert.Scale
open Extraction Table Spec Climb Filter Set Finset PhysMS MeasureTheory Next.UVStress
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} (B : Deck G) {O : Booked B} (M : MS_Data G O)
variable (F : Spec.Final C f S) (J : ℝ→PhysMS.tower S)


open WilsonMacroscopicRichMeasuredGram WilsonMacroscopicRichRegister
open WilsonMacroscopicRichFree
variable (h : ℕ) (g : Test 2)
local notation "Iₕ" => Glyph B h

private def action (A Z : Matrix Iₕ Iₕ ℂ) (left : Z*A=1) :
    (Iₕ→ℂ) ≃ₗ[ℂ] (Iₕ→ℂ) :=
  LinearEquiv.ofBijective A.vecMulLinear (by
    have onto : Function.Surjective A.vecMulLinear := by
      intro v;refine ⟨Z.vecMulLinear v,?_⟩
      change A.vecMul (Z.vecMul v)=v
      rw [Matrix.vecMul_vecMul,left,Matrix.vecMul_one]
    exact ⟨LinearMap.injective_iff_surjective.mpr onto,onto⟩)

private theorem cancels (P W : Matrix Iₕ Iₕ ℂ) (hp : IsUnit P) (hw : IsUnit W) :
    (W*P⁻¹)*(P*W⁻¹)=1 := by
  have yes := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det _).mp hp)
  have last := Matrix.mul_nonsing_inv W ((Matrix.isUnit_iff_isUnit_det _).mp hw)
  calc
    _ = W*(P⁻¹*P)*W⁻¹ := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [yes,Matrix.mul_one,last]

/-- A true equivalence into S on the original phase at every r. Its
diagnostic is prescribed only in the small-radius regime. -/
def frame (P : ℝ→Matrix Iₕ Iₕ ℂ) (r : ℝ) : (Bel C.book).Field h ≃ₗ[ℂ] S.Field h :=
  let W := bank B F J h g r
  let e := (WilsonMacroscopicRichFree.basis C B h).equivFun
  if ok : IsUnit (P r) ∧ IsUnit W then
    ((e.trans (action B h (P r*W⁻¹) (W*(P r)⁻¹) (cancels B h (P r) W ok.1 ok.2))).trans e.symm).trans (J r h)
  else J r h

theorem coordinates (P : ℝ→Matrix Iₕ Iₕ ℂ) (r : ℝ) (hp : IsUnit (P r)) (hw : IsUnit (bank B F J h g r))
    (v : (Bel C.book).Field h) :
    coords B J (τ:=r) (frame B F J h g P r v) =
      (P r*(bank B F J h g r)⁻¹).vecMul ((WilsonMacroscopicRichFree.basis C B h).equivFun v) := by
  rw [frame,dif_pos ⟨hp,hw⟩]
  simp only [WilsonMacroscopicRichRegister.coords,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,LinearEquiv.apply_symm_apply]
  rfl

/-- Every field in the authentic new equivalence is measured by the OLD
held exterior exactly at the independently prescribed row, on all simultaneous
inputs v (in particular on each genuine independent glyph). -/
theorem row (P : ℝ→Matrix Iₕ Iₕ ℂ) {r : ℝ} (hr : 0<r) (hp : IsUnit (P r)) (hw : IsUnit (bank B F J h g r))
    (v : (Bel C.book).Field h) (b : Iₕ) :
    (exterior B J g hr b).charge F h (frame B F J h g P r v)=(P r).vecMul ((WilsonMacroscopicRichFree.basis C B h).equivFun v) b := by
  rw [read_field B F J g hr b,coordinates B F J h g P r hp hw,Matrix.vecMul_vecMul,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hw),Matrix.mul_one]

/-- Any prescribed family converging to the independently supplied common
tree is attained on this actual Wilson measuring register, and the actual
relative free-coordinate map tends to the identity. -/
theorem calibrated (leading : PhysMS.Leading F J) (μ : ℝ) (live : IsUnit (MSSeparatedTestGram.matrix M h μ 0 g))
    (P : ℝ→Matrix Iₕ Iₕ ℂ) (arrives : Tendsto P Trace.Pilot.trail (𝓝 (MSSeparatedTestGram.matrix M h μ 0 g))) :
    (∀ᶠ r in Trace.Pilot.trail,∀ hr : 0<r,∀ v b,(exterior B J g hr b).charge F h (frame B F J h g P r v)=
      (P r).vecMul ((WilsonMacroscopicRichFree.basis C B h).equivFun v) b) ∧
      ∀ v : (Bel C.book).Field h,Tendsto (fun r=>(J r h).symm (frame B F J h g P r v)) Trace.Pilot.trail (𝓝 v) := by
  let T := MSSeparatedTestGram.matrix M h μ 0 g
  let e := (WilsonMacroscopicRichFree.basis C B h).equivFun
  let W := bank B F J h g
  have det : T.det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp live)
  have dets := ((continuous_id.matrix_det).continuousAt (x:=T)).tendsto.comp arrives
  have pr : ∀ᶠ r in Trace.Pilot.trail,IsUnit (P r) :=
    (dets.eventually_ne det).mono fun r u=>(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr u)
  obtain ⟨realized,invlim⟩ := invertible B F J leading M h g μ live
  have each : ∀ᶠ r in Trace.Pilot.trail,IsUnit (P r)∧IsUnit (W r) := pr.and realized
  refine ⟨each.mono (fun r ok hr v b=>row B F J h g P hr ok.1 ok.2 v b),?_⟩
  intro v
  have rel : Tendsto (fun r=>P r*(W r)⁻¹) Trace.Pilot.trail (𝓝 1) := by
    have got : Tendsto (fun r=>P r*(W r)⁻¹) Trace.Pilot.trail (𝓝 (T*T⁻¹)) := arrives.mul invlim
    rwa [Matrix.mul_nonsing_inv T ((Matrix.isUnit_iff_isUnit_det _).mp live)] at got
  have lin : Continuous (fun A : Matrix Iₕ Iₕ ℂ=>A.vecMul (e v)) := by
    apply continuous_pi;intro j
    apply continuous_finsetSum;intro i _
    exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  have run : Tendsto (fun r=>(P r*(W r)⁻¹).vecMul (e v)) Trace.Pilot.trail (𝓝 (e v)) := by
    have got : Tendsto (fun r=>(P r*(W r)⁻¹).vecMul (e v)) Trace.Pilot.trail (𝓝 ((1 : Matrix Iₕ Iₕ ℂ).vecMul (e v))) := lin.continuousAt.tendsto.comp rel
    rwa [Matrix.vecMul_one] at got
  have num : Tendsto (fun r=>coords B J (τ:=r) (frame B F J h g P r v)) Trace.Pilot.trail (𝓝 (e v)) :=
    run.congr' (each.mono fun r ok=>(coordinates B F J h g P r ok.1 ok.2 v).symm)
  have final := e.symm.continuous_of_finiteDimensional.continuousAt.tendsto.comp num
  change Tendsto (fun r=>e.symm (e ((J r h).symm (frame B F J h g P r v)))) Trace.Pilot.trail (𝓝 (e.symm (e v))) at final
  simpa only [LinearEquiv.symm_apply_apply] using final

/-- The concrete independent MS coefficient bank, at any finite order. -/
theorem prescribed (hG : G.Simple) (leading : PhysMS.Leading F J) (μ : ℝ)
    (live : IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) (q : ℕ) {γ : ℝ→ℝ} (hγ : Trace.Pilot.Coupling G γ) :
    let P := fun r=>WilsonMacroscopicRichSignedMS.jet B M h g μ q (γ r)
    (∀ᶠ r in Trace.Pilot.trail,∀ hr : 0<r,∀ v b,(exterior B J g hr b).charge F h (frame B F J h g P r v)=
      (P r).vecMul ((WilsonMacroscopicRichFree.basis C B h).equivFun v) b) ∧
      ∀ v : (Bel C.book).Field h,Tendsto (fun r=>(J r h).symm (frame B F J h g P r v)) Trace.Pilot.trail (𝓝 v) := by
  apply calibrated B M F J h g leading μ live
  have named := (WilsonMacroscopicRichSignedMS.continuous B M h g μ q).continuousAt.tendsto.comp (hγ.conforms hG)
  rw [WilsonMacroscopicRichSignedMS.at_zero] at named
  exact named

end YM.Integration.WilsonOrdinaryPivotFrame
