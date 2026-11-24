import YM.Integration.WilsonPositionThermometerRegulator
import YM.Integration.WilsonPositionThermometerTest

/-! Complete finite original Wilson measurement of the real, normalized
position thermometer. Smear the seven-moment polynomial on common lattice
addresses before the original regulator limit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerFinite
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) (r : ℝ)

theorem cells (hG : G.Simple) {l : Filter UVIndex} (hl : l ≤ f.fuse) (hr : 0<r)
    {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in l,∀ x∈K,
      ‖WilsonPositionThermometerRegulator.full J r z x-WilsonPositionThermometerPhases.raw F J none r x‖ < ε := by
  let A := WilsonPositionThermometerReading.sample F J r
  let B (z : UVIndex) (x : Points 3) (s : Badge) := WilsonPositionThermometerRegulator.original J r s z x
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
  have bank := WilsonPositionThermometerRegulator.cut F J r hG hl hr hk sep dpos
  filter_upwards [bank] with z ready x hx
  have near : dist (B z x) (A x) < min 1 δ := (dist_pi_lt_iff dpos).mpr (fun s => by
    simpa only [dist_eq_norm,A,B] using ready s x hx)
  have av : A x ∈ V := ⟨x,hx,rfl⟩
  have bw : B z x ∈ W := mem_cthickening_of_dist_le (B z x) (A x) 1 V av (near.le.trans (min_le_left _ _))
  change ‖WilsonPositionThermometerConnected.value (B z x) - WilsonPositionThermometerConnected.value (A x)‖ < ε
  simpa only [dist_eq_norm] using
    move (B z x) bw (A x) (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))

theorem measurable (z : UVIndex) : Measurable (WilsonPositionThermometerRegulator.full J r z) := by
  let I (x : Fin 3 → Cover) := WilsonPositionThermometerConnected.value (fun s =>
    R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6) (wrap _ ∘ x)
      (WilsonPositionThermometerRegulator.written J r s))
  have grid : Measurable (address (R.family.S.a z.1) : Points 3 → (Fin 3 → Cover)) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  exact (measurable_of_countable I).comp (grid.comp (continuous_const_smul r).measurable)

variable {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)

def finite (z : UVIndex) : ℝ :=
  ((Rose.test K).applyTo (WilsonPositionThermometerRegulator.full J r z)).re / Rose.cT K.cut G K.image

theorem signed (hG : G.Simple) {l : Filter UVIndex} (hl : l ≤ f.fuse) (hr : 0<r) :
    Tendsto (fun z => (Rose.test K).applyTo (WilsonPositionThermometerRegulator.full J r z)) l
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
  filter_upwards [cells F J r hG hl hr Φ.hasCompactSupport Φ.tsupport_subset ht] with z bound
  let v := WilsonPositionThermometerRegulator.full J r z
  have am : AEStronglyMeasurable (fun x : Points 3 => Φ x*v x) volume :=
    (Φ.continuous.measurable.mul (measurable J r z)).aestronglyMeasurable
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

theorem original (hG : G.Simple) {l : Filter UVIndex} (hl : l ≤ f.fuse) (hr : 0<r) :
    Tendsto (finite J r K) l (𝓝 (reading F J K r)) :=
  ((Complex.continuous_re.tendsto _).comp (signed F J r K hG hl hr)).div_const _

end YM.Integration.WilsonPositionThermometerFinite
