import YM.Integration.WilsonPositionThermometerAtRef
import YM.Integration.WilsonPositionThermometerTest
import YM.Integration.WilsonRegulatorPointDetector

/-! Signed original Wilson-minus-MS three-point assay on one common filed lift.
The lens and the charged fields are selected before cutoffs, periods or tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerAtRefAssay
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open FVA2 FVA2.Arrival FVA2.Register FVA2.Scale MS MS.Land WilsonIndependentSchemeTruncation
open WilsonPositionThermometerReading
open private addressable from YM.Integration.WilsonRegulatorPointDetector
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) (r : ℝ)

variable (L : Layout F) (E : RG17.Free R.family 6 →L[ℂ] R.family.label 6)
theorem cells (hG : G.Simple) {l : Filter UVIndex} [l.NeBot] (hl : l ≤ L.lens)
    (admit : R.family.ref 6 ≤ L.level r) (lifted : ∀ v,RG17.master L 6 r (E v)=J r 6 v) (hr : 0<r)
    {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in l,∀ x∈K,
      ‖WilsonPositionThermometerAtRef.full F r L E z x-WilsonPositionThermometerPhases.raw F J none r x‖ < ε := by
  let A := WilsonPositionThermometerReading.sample F J r
  let B (z : UVIndex) (x : Points 3) (s : Badge) := WilsonPositionThermometerAtRef.moment F r L E s z x
  have cont : ContinuousOn A K := by
    apply continuousOn_pi.mpr
    intro s
    let v (i : Fin 3) : S.Tag := ⟨6,J r 6 (leg R.family s i)⟩
    exact ((S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn).comp
      (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr (sep hx))
  let V := A '' K
  have vc : IsCompact V := hk.image_of_continuousOn cont
  let W := cthickening (1:ℝ) V
  have wc : IsCompact W := vc.cthickening
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp
    (wc.uniformContinuousOn_of_continuous WilsonPositionThermometerConnected.continuous_value.continuousOn) ε he
  have dpos : 0 < min 1 δ := lt_min one_pos hδ
  have bank := WilsonPositionThermometerAtRef.cut F J r L E hG hl admit lifted hr hk sep dpos
  filter_upwards [bank] with z ready x hx
  have near : dist (B z x) (A x) < min 1 δ := (dist_pi_lt_iff dpos).mpr (fun s => by
    simpa only [dist_eq_norm,A,B] using ready s x hx)
  have av : A x ∈ V := ⟨x,hx,rfl⟩
  have bw : B z x ∈ W := mem_cthickening_of_dist_le (B z x) (A x) 1 V av (near.le.trans (min_le_left _ _))
  change ‖WilsonPositionThermometerConnected.value (B z x) - WilsonPositionThermometerConnected.value (A x)‖ < ε
  simpa only [dist_eq_norm] using
    move (B z x) bw (A x) (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))

theorem measurable (z : UVIndex) : Measurable (WilsonPositionThermometerAtRef.full F r L E z) := by
  let I (x : Fin 3 → Cover) := WilsonPositionThermometerConnected.value (fun s =>
    R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6) (wrap _ ∘ x)
      (fun i=>RG17.atRef L 6 r z (E (leg R.family s i))))
  exact (measurable_of_countable I).comp ((addressable R z.1 3).comp (continuous_const_smul r).measurable)

variable {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)

def finite (z : UVIndex) : ℝ :=
  ((Rose.test K).applyTo (WilsonPositionThermometerAtRef.full F r L E z)).re / Rose.cT K.cut G K.image

theorem signed (hG : G.Simple) {l : Filter UVIndex} [l.NeBot] (hl : l ≤ L.lens)
    (admit : R.family.ref 6 ≤ L.level r) (lifted : ∀ v,RG17.master L 6 r (E v)=J r 6 v) (hr : 0<r) :
    Tendsto (fun z => (Rose.test K).applyTo (WilsonPositionThermometerAtRef.full F r L E z)) l
      (𝓝 (tested F J K r)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let Φ := Rose.test K
  let u := WilsonPositionThermometerPhases.raw F J none r
  let M := WilsonPositionThermometerTest.mass K
  have hm : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  let t := (ε/2)/(M+1)
  have ht : 0<t := div_pos (half_pos he) (by linarith)
  have price : M*t < ε := by
    calc M*t ≤ (M+1)*t := mul_le_mul_of_nonneg_right (by linarith) ht.le
         _ = ε/2 := by dsimp only [t];field_simp [show M+1≠0 by linarith]
         _ < ε := half_lt_self he
  have gi : Integrable (fun x : Points 3 => Φ x) := Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
  have target := Φ.smearing (WilsonPositionThermometerTest.continuous F J none hr)
  filter_upwards [cells F J r L E hG hl admit lifted hr Φ.hasCompactSupport Φ.tsupport_subset ht] with z bound
  let v := WilsonPositionThermometerAtRef.full F r L E z
  have am : AEStronglyMeasurable (fun x : Points 3 => Φ x*v x) volume :=
    (Φ.continuous.measurable.mul (measurable F r L E z)).aestronglyMeasurable
  have point (x : Points 3) : ‖Φ x*v x-Φ x*u x‖ ≤ ‖Φ x‖*t := by
    by_cases hz : Φ x=0
    · simp [hz]
    · rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (bound x (subset_closure hz)).le (norm_nonneg _)
  have oi : Integrable (fun x : Points 3 => Φ x*u x) := target
  have di := (gi.norm.mul_const t).mono' (am.sub oi.aestronglyMeasurable) (Eventually.of_forall point)
  have vi : Integrable (fun x : Points 3 => Φ x*v x) :=
    (di.add oi).congr (Eventually.of_forall fun _ => sub_add_cancel _ _)
  rw [dist_eq_norm]
  change ‖(∫x, Φ x*v x)-(∫x, Φ x*u x)‖ < ε
  rw [←integral_sub vi oi]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point))
  rw [integral_mul_const]
  exact price

theorem original (hG : G.Simple) {l : Filter UVIndex} [l.NeBot] (hl : l ≤ L.lens)
    (admit : R.family.ref 6 ≤ L.level r) (lifted : ∀ v,RG17.master L 6 r (E v)=J r 6 v) (hr : 0<r) :
    Tendsto (finite F r L E K) l (𝓝 (reading F J K r)) :=
  ((Complex.continuous_re.tendsto _).comp (signed F J r L E K hG hl admit lifted hr)).div_const _

variable (Z : WilsonPrescription G) (ν : ℝ)
variable (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (q : ℕ) (t : ℝ)

def residue (z : UVIndex) : ℝ :=
  ((Rose.test Z.criterion).applyTo (fun x =>
    WilsonPositionThermometerAtRef.full F r L E z x -
      WilsonPositionIndependentIntegral.positive Z ν T q t x)).re / Rose.c_T Z.criterion

private theorem integrable_fine (z : UVIndex) :
    Integrable (fun x : Points 3 => Rose.test Z.criterion x*WilsonPositionThermometerAtRef.full F r L E z x) := by
  let Φ := Rose.test Z.criterion
  let X := R.family.side z.1 z.2
  let a (x : Fin 3 → Site X) := WilsonPositionThermometerConnected.value (fun s =>
    R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6) x (fun i=>RG17.atRef L 6 r z (E (leg R.family s i))))
  let m := ∑ x : Fin 3 → Site X,‖a x‖
  have ga : Integrable (fun x : Points 3 => Φ x) := Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
  apply (ga.norm.mul_const m).mono' (Φ.continuous.measurable.mul (measurable F r L E z)).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  let v : Fin 3 → Site X := wrap X ∘ Extraction.address (R.family.S.a z.1) (r • x)
  change ‖Φ x*WilsonPositionThermometerAtRef.full F r L E z x‖ ≤ ‖Φ x‖*m
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.single_le_sum (f:=fun y => ‖a y‖) (fun _ _=>norm_nonneg _) (Finset.mem_univ v)

private theorem subtracted (φ : Test 3) {A B : Points 3 → ℂ}
    (ha : Integrable (fun x => φ x*A x)) (hb : Integrable (fun x => φ x*B x)) :
    φ.applyTo (fun x => A x-B x) = φ.applyTo A-φ.applyTo B := by
  unfold Test.applyTo
  simp only [mul_sub]
  exact integral_sub ha hb

theorem actual (z : UVIndex) :
    residue F r L E Z ν T q t z = finite F r L E Z.criterion z -
      ((WilsonIndependentSchemeTruncation.finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ)).re := by
  rw [WilsonPositionIndependentIntegral.real_polynomial]
  unfold residue finite
  rw [subtracted _ (integrable_fine F r L E Z z) ((Rose.test Z.criterion).smearing
    (WilsonPositionIndependentIntegral.positive_continuous Z ν T q t)),Complex.sub_re,sub_div]


/-- The complete signed residual on the filed reporting fields tends to the
literal measured-minus-independent residual on the selected position frame. -/
theorem defect (hG : G.Simple) {l : Filter UVIndex} [l.NeBot] (hl : l ≤ L.lens)
    (admit : R.family.ref 6 ≤ L.level r) (lifted : ∀ v,RG17.master L 6 r (E v)=J r 6 v) (hr : 0<r) :
    Tendsto (residue F r L E Z ν T q t) l (𝓝 (WilsonPositionThermometerDefect.continuum F J Z ν T q r t)) := by
  rw [WilsonPositionThermometerDefect.reference F J Z ν T q r t hr]
  apply ((original F J r L E Z.criterion hG hl admit lifted hr).sub_const
    ((WilsonIndependentSchemeTruncation.finite q (Measure.chi Z.criterion ν T)).eval (t:ℂ)).re).congr'
  exact Eventually.of_forall (fun z => (actual F r L E Z ν T q t z).symm)

theorem purchased (hG : G.Simple) (scene : Pier.Scene.ScenePlan R F L)
    (funds : Pier.Lair.Paying F (Pier.Lair.tender F L J) 6) :
    ∃ (p : ℕ) (c : ℝ) (B : ℝ→RG17.Free R.family 6 →L[ℂ] R.family.label 6),0≤c ∧
    ∀ᶠ r in Trace.Pilot.trail,(∀ v,RG17.master L 6 r (B r v)=J r 6 v) ∧
      ‖B r‖≤c*R.family.path.levels.clock.hatBeta (L.level r)^p ∧
      ∀(Z : WilsonPrescription G) (ν : ℝ) (T : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
        (q : ℕ) (t : ℝ) (l : Filter UVIndex), l.NeBot → l ≤ L.lens →
        Tendsto (residue F r L (B r) Z ν T q t) l (𝓝 (WilsonPositionThermometerDefect.continuum F J Z ν T q r t)) := by
  obtain ⟨p,c,B,hc,entries⟩ := WilsonPositionThermometerAtRef.purchased F J L scene funds
  refine ⟨p,c,B,hc,?_⟩
  filter_upwards [entries,scene.layout.level.growing.eventually_ge_atTop (R.family.ref 6),RG17.positiveLength] with r stock admit hr
  refine ⟨stock.1,stock.2,?_⟩
  intro Z ν T q t l hl sub
  haveI := hl
  exact defect F J r L (B r) Z ν T q t hG sub admit stock.1 hr

end YM.Integration.WilsonPositionThermometerAtRefAssay
