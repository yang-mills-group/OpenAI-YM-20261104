import YM.Integration.WilsonMatrixOriginalDeckRegulated

/-! Obtain the inverse of the whole measured field space directly from finite Wilson products. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixOriginalDeckCutoff
open Filter Set MeasureTheory Pert Pert.Position MS MS.Local.Physical MS.Menus MS.Land MS.Theater
open Extraction Extraction.Order Table Spec Climb FVA2 FVA2.ColorCode OPE OPE.Orbits OPE.Levy RG11.Fields
open RG17 Next.UVStress Push.GridApprox PhysicalNext.Repeat.Legato
open WilsonMatrixOriginalDeckRegulated
open private matrixSize vectorSize image_size cost_continuous from YM.Integration.WilsonMatrixOriginalDeckInverse
open scoped Classical Topology BigOperators Matrix
variable {G:Gauge} (R:Run G) (B:Deck G) {O:Booked B} {f:Extraction.Order} {S:Table R.family.book}
variable (F:Spec.Final R.family f S) (J:ℝ→PhysMS.tower S) (h:ℕ)

/-- The entire product matrix on one genuine finite lattice, with each source at its indicated scale. -/
def raw (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) (z:ℕ×ℕ) : Matrix (Glyph B h) (Glyph B h) ℂ :=
  fun a b=>reading (R:=R) h g hr (fun _ i=>S.representative h (arms (R:=R) B J h r s a b i)) z

include F in
/-- All entries use the same cutoff, torus, Wilson law and signed compact test. -/
theorem limit (g:Test 2) {r:ℝ} (hr:0<r) (s:ℝ) (u:Filter (ℕ×ℕ)) [u.NeBot] (per:u≤f.fuse) :
    Tendsto (raw R B J h g hr s) u (𝓝 (WilsonMatrixOriginalDeckMixed.mixed B J h g r s)) :=
  tendsto_pi_nhds.mpr fun a=>tendsto_pi_nhds.mpr fun b=>pinned B F J h g hr s a b u per

private theorem identity (r:ℝ) : WilsonMatrixOriginalDeckMixed.change B J h r r = 1 := by
  classical
  ext i b
  let E := WilsonMatrixOriginalDeckColumns.basis R.family B h
  change E.repr ((J r h).symm (J r h (E b))) i = (1:Matrix (Glyph B h) (Glyph B h) ℂ) i b
  rw [LinearEquiv.symm_apply_apply,E.repr_self,Matrix.one_apply]
  simp [Finsupp.single_apply,eq_comm]

private theorem inverse_limit {I T:Type*} [Fintype I] [DecidableEq I]
    {u:Filter T} {A:T→Matrix I I ℂ} {M:Matrix I I ℂ} (t:Tendsto A u (𝓝 M)) (live:IsUnit M) :
    (∀ᶠ z in u, IsUnit (A z)) ∧ Tendsto (fun z=>(A z)⁻¹) u (𝓝 M⁻¹) := by
  have det : M.det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp live)
  have invs : ContinuousAt Inv.inv M := continuousAt_matrix_inv M (by rw [Ring.inverse_eq_inv'];exact continuousAt_inv₀ det)
  have dets := ((continuous_id.matrix_det).continuousAt (x:=M)).tendsto.comp t
  refine ⟨?_,invs.tendsto.comp t⟩
  filter_upwards [dets.eventually_ne det] with z nz
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr nz)

/-- One localized test and one inverse bound work for every sufficiently fine radius, every second
radius, and eventually every actual cutoff and period at the chosen reporting radii. -/
theorem original (L:PhysMS.Leading F J) (M:MS_Data G O) {p:E4} (hp:(0:E4)≠p)
    (U:Set (Points 2)) (near:U∈𝓝 (Extra.FD.couple 0 p)) :
    ∃ (g:Test 2) (C:ℝ), 0<C ∧ tsupport g⊆U ∧ (∀x,(g x).im=0 ∧ 0≤(g x).re) ∧
      0<(g (Extra.FD.couple 0 p)).re ∧ (∫x,g x)=1 ∧ (∀μ,IsUnit (MSSeparatedTestGram.matrix M h μ 0 g)) ∧
      ∀ᶠ r in Trace.Pilot.trail, ∀ (hr:0<r) (u:Filter (ℕ×ℕ)) [u.NeBot], u≤f.fuse →
        (∀ᶠ z in u,IsUnit (raw R B J h g hr r z) ∧ ∀v : Glyph B h→ℂ,
          (∑i,‖v i‖) ≤ C*(∑i,‖(raw R B J h g hr r z *ᵥ v) i‖)) ∧
        ∀s:ℝ,Tendsto (fun z=>(raw R B J h g hr r z)⁻¹ * raw R B J h g hr s z) u
          (𝓝 (WilsonMatrixOriginalDeckMixed.change B J h r s)) := by
  classical
  obtain ⟨g,supp,real,point,mass,all⟩ := MSSeparatedTestGram.simultaneous
    (WilsonMatrixTicketLanesNativePrices.warehouse R) M h hp U near
  let K := MSSeparatedTestGram.matrix M h 0 0 g
  let C := matrixSize K⁻¹+2
  have hC : 0<C := by dsimp [C,matrixSize]; positivity
  refine ⟨g,C,hC,supp,real,point,mass,all,?_⟩
  let A := WilsonMatrixOriginalDeckGram.bank B F J h g
  have tail := WilsonMatrixOriginalDeckGram.invertible B F J L M h g 0 (all 0)
  have outer : Tendsto (fun r=>matrixSize (A r)⁻¹) Trace.Pilot.trail (𝓝 (matrixSize K⁻¹)) :=
    cost_continuous.continuousAt.tendsto.comp tail.2
  filter_upwards [tail.1,outer.eventually (gt_mem_nhds (show matrixSize K⁻¹<C by dsimp [C];linarith))] with r hrank room
  intro hr u _ per
  have equal := WilsonMatrixOriginalDeckMixed.observed B F J h g hr r
  rw [identity R B J h r,Matrix.mul_one] at equal
  have self := limit R B F J h g hr r u per
  rw [equal] at self
  have back := inverse_limit self hrank
  refine ⟨?_,?_⟩
  · have enter : Tendsto (fun z=>matrixSize (raw R B J h g hr r z)⁻¹) u (𝓝 (matrixSize (A r)⁻¹)) :=
      cost_continuous.continuousAt.tendsto.comp back.2
    filter_upwards [back.1,enter.eventually (gt_mem_nhds room)] with z unit paid
    refine ⟨unit,fun v=>?_⟩
    let X := raw R B J h g hr r z
    have fixed : X⁻¹ *ᵥ (X *ᵥ v)=v := by rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul X ((Matrix.isUnit_iff_isUnit_det _).mp unit),Matrix.one_mulVec]
    calc
      vectorSize v = vectorSize (X⁻¹ *ᵥ (X *ᵥ v)) := congrArg vectorSize fixed.symm
      _ ≤ matrixSize X⁻¹ * vectorSize (X *ᵥ v) := image_size _ _
      _ ≤ C * vectorSize (X *ᵥ v) := mul_le_mul_of_nonneg_right paid.le (Finset.sum_nonneg fun _ _=>norm_nonneg _)
  · intro s
    have mixed := limit R B F J h g hr s u per
    have recovered := back.2.mul mixed
    rw [WilsonMatrixOriginalDeckMixed.observed B F J h g hr s,←mul_assoc,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hrank),one_mul] at recovered
    exact recovered

end YM.Integration.WilsonMatrixOriginalDeckCutoff
