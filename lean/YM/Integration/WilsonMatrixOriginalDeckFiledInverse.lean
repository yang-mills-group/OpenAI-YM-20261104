import YM.Integration.WilsonMatrixOriginalDeckFiledDebit
import YM.Integration.WilsonMatrixOriginalDeckCutoff

/-! Invert the empirical full self-Gram of the before-cutoff deposited Wilson fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckFiledInverse
open Filter Set Finset MeasureTheory Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Extraction Extraction.Order Table Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open Trace.Pilot Ward PhysMS RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalDeckFiledDebit WilsonMatrixOriginalDeckMixed WilsonMatrixOriginalDeckColumns
open private identity inverse_limit from YM.Integration.WilsonMatrixOriginalDeckCutoff
open private matrixSize vectorSize image_size cost_continuous from YM.Integration.WilsonMatrixOriginalDeckInverse
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (L:Layout F) (J:ℝ→PhysMS.tower S) (h:ℕ) {O:Booked B}

theorem measured (g:Test 2){r s:ℝ}(hr:0<r)(ages:R.family.ref h≤L.level r)(agt:R.family.ref h≤L.level s)
    (w v:Glyph B h→R.family.label h)(hw:∀a,master L h r (w a)=J r h (WilsonMatrixOriginalDeckColumns.basis R.family B h a))
    (hv:∀a,master L h s (v a)=J s h (WilsonMatrixOriginalDeckColumns.basis R.family B h a))(u:Filter (ℕ×ℕ)) [u.NeBot] (cut:u≤L.lens):
    Tendsto (field R B F L h g hr s w v) u (𝓝 (mixed B J h g r s)):=by
  apply tendsto_pi_nhds.mpr;intro a;apply tendsto_pi_nhds.mpr;intro b
  exact WilsonMatrixOriginalDeckFiled.issued R B F L J h g hr ages agt a b (w a) (v b) (hw a) (hv b) u cut

/-- The inverse constant is fixed on the independent Gram before both physical dates. -/
theorem purchased (lead:PhysMS.Leading F J)(M:MS_Data G O)(g:Test 2)(pivot:IsUnit (MSSeparatedTestGram.matrix M h 0 0 g)):
    ∃C:ℝ,0<C ∧ ∀ᶠr:ℝ in trail, ∀(hr:0<r)(_:R.family.ref h≤L.level r)(a:Glyph B h→R.family.label h),
      (∀b,master L h r (a b)=J r h (WilsonMatrixOriginalDeckColumns.basis R.family B h b)) → ∀(u:Filter (ℕ×ℕ)) [u.NeBot],u≤L.lens →
      (∀ᶠz in u,IsUnit (field R B F L h g hr r a a z) ∧ ∀v:Glyph B h→ℂ,
        (∑i,‖v i‖)≤ C*∑i,‖(field R B F L h g hr r a a z*ᵥ v) i‖) ∧
      ∀(s:ℝ)(_:R.family.ref h≤L.level s)(v:Glyph B h→R.family.label h),
        (∀b,master L h s (v b)=J s h (WilsonMatrixOriginalDeckColumns.basis R.family B h b)) →
        Tendsto (fun z=>(field R B F L h g hr r a a z)⁻¹*field R B F L h g hr s a v z) u (𝓝 (change B J h r s)):=by
  classical
  let K:=MSSeparatedTestGram.matrix M h 0 0 g
  let C:=matrixSize K⁻¹+2
  have hC:0<C:=by dsimp [C,matrixSize];positivity
  refine ⟨C,hC,?_⟩
  let A:=WilsonMatrixOriginalDeckGram.bank B F J h g
  have tail:=WilsonMatrixOriginalDeckGram.invertible B F J lead M h g 0 pivot
  have outer:Tendsto (fun r=>matrixSize (A r)⁻¹) trail (𝓝 (matrixSize K⁻¹)):=cost_continuous.continuousAt.tendsto.comp tail.2
  filter_upwards [tail.1,outer.eventually (gt_mem_nhds (show matrixSize K⁻¹<C by dsimp [C];linarith))] with r hrank room
  intro hr age a ha u _ cut
  have self:=measured R B F L J h g hr age age a a ha ha u cut
  have equal:=WilsonMatrixOriginalDeckMixed.observed B F J h g hr r
  rw [identity R B J h r,Matrix.mul_one] at equal
  rw [equal] at self
  have back:=inverse_limit self hrank
  refine ⟨?_,?_⟩
  · have inc:Tendsto (fun z=>matrixSize (field R B F L h g hr r a a z)⁻¹) u (𝓝 (matrixSize (A r)⁻¹)):=cost_continuous.continuousAt.tendsto.comp back.2
    filter_upwards [back.1,inc.eventually (gt_mem_nhds room)] with z live paid
    refine ⟨live,?_⟩;intro v
    let X:=field R B F L h g hr r a a z
    have fixed:X⁻¹*ᵥ(X*ᵥv)=v:=by rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp live),Matrix.one_mulVec]
    calc vectorSize v = vectorSize (X⁻¹*ᵥ(X*ᵥv)):=congr_arg vectorSize fixed.symm
         _ ≤ matrixSize X⁻¹*vectorSize (X*ᵥv):=image_size _ _
         _ ≤ C*vectorSize (X*ᵥv):=mul_le_mul_of_nonneg_right paid.le (sum_nonneg fun _ _=>norm_nonneg _)
  · intro s agt v hv
    have recovered:=back.2.mul (measured R B F L J h g hr age agt a v ha hv u cut)
    rw [WilsonMatrixOriginalDeckMixed.observed B F J h g hr s,←mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hrank),one_mul] at recovered
    exact recovered

end YM.Integration.WilsonMatrixOriginalDeckFiledInverse
