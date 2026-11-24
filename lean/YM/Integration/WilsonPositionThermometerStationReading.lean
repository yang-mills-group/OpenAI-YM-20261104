import YM.Integration.WilsonPositionThermometerOrientedStation
import YM.Integration.WilsonMovingCalibratedFields

/-! The seven faces of the original oriented thermometer from the moving
cutoff fields at their separate sites to the signed continuum test. -/
noncomputable section
namespace YM.Integration.WilsonPositionThermometerStationReading
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerOrientedStation
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (r : ℝ)

def along {I : Type} {d : ℕ} {C : Family G} (A : Filing C d I) (T : Lifts C A.horizon) (i : I) : C.book.Ref d :=
  A.grade ▸ T A.level (A.grade.symm ▸ A.vector i)

private theorem along_continuous {I : Type} {d : ℕ} {C : Family G} (A : Filing C d I) (i : I) :
    Continuous (fun T => along A T i) := by
  obtain ⟨k,j,eq,V,L,u⟩ := A
  subst d
  exact (continuous_apply j).clm_apply continuous_const

variable (A : Filing R.family 6 (Badge × Fin 3))

def moment (z : UVIndex) (x : Points 3) (s : Badge) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3 => 6)
    (wrap _ ∘ address (R.family.S.a z.1) (r • x)) (fun i => along A (A.station.wheel.atCut z) (s,i))

def full (z : UVIndex) (x : Points 3) : ℂ :=
  WilsonPositionThermometerConnected.value (moment r A z x)

variable {H : (Bel R.family.book).Hierarchy} {Y : Ultrafilter UVIndex} {m : ℕ}
variable (hG : G.Simple) (hl : (Y : Filter _) ≤ f.fuse)
variable (filed : Filed (f:=f) (Y:=Y) H (fun i : Badge × Fin 3 => leg R.family i.1 i.2) r (J r) m A)
include hG hl filed

theorem cut (hr : 0 < r) {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ z : UVIndex in (Y : Filter _), ∀ s : Badge, ∀ x ∈ K, ‖moment r A z x s - sample F J r x s‖ < ε := by
  let C := R.family
  let d : Caps 3 := fun _=>6
  let T := (fun x : Points 3 => r • x) '' K
  have compact : IsCompact T := hk.image (continuous_const_smul r)
  have apart : T ⊆ conf 3 := by rintro _ ⟨x,hx,rfl⟩;exact Work.A05.smul_conf hr (sep hx)
  obtain ⟨t,ht,inside⟩ := compact.exists_cthickening_subset_open (conf_open _) apart
  let U := cthickening t T
  have cu : IsCompact U := compact.cthickening
  apply Filter.eventually_all.mpr
  intro s
  let a (i : Fin 3) := along A A.lift (s,i)
  let vals (z : UVIndex) (i : Fin 3) := along A (A.station.wheel.atCut z) (s,i)
  have measured (i : Fin 3) : Tendsto (fun z => vals z i) (Y : Filter _) (𝓝 (a i)) :=
    (along_continuous A (s,i)).continuousAt.tendsto.comp filed.2.2.2.1
  have pay (i : Fin 3) : S.project 6 (a i) = J r 6 (leg R.family s i) :=
    (filed.2.2.2.2 (s,i)).1.symm
  have equal (X : Points 3) (legal : X∈conf 3) :
      S.classMoment S d X (fun i=>J r 6 (leg R.family s i))=S.value d X a := by
    simp_rw [←pay]
    exact S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) legal (fun i=>⟨d i,a i⟩)
  let result (y : Points 3) := S.value d y a
  have cont : ContinuousOn result U := ((F.room.kernel.smooth.on_conf d a).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (cu.uniformContinuousOn_of_continuous cont) (ε/2) (half_pos he)
  have atTop' : Tendsto (fun z : UVIndex => z.1) (Y : Filter _) atTop :=
    tendsto_atTop.mpr fun j => (large_mesh f j).filter_mono hl
  have fine : Tendsto (fun z : UVIndex => (4*3:ℝ)*C.S.a z.1) (Y : Filter _) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*3:ℝ))).mul (C.S.shrinks.comp atTop')
  have bank := WilsonMovingCalibratedFields.paid R hG F hl d vals a
    measured U cu inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z charged mesh x hx
  let X := r • x
  let c := address (C.S.a z.1) X
  let Y := tag (C.S.a z.1) c
  have inT : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (C.S.a_pos z.1) X).trans_lt mesh
  have inU : Y ∈ U := mem_cthickening_of_dist_le Y X t T inT (near.le.trans (min_le_left _ _))
  have first : dist (moment r A z x s) (result Y) < ε/2 := charged c inU
  have second := move Y inU X (self_subset_cthickening T inT) (near.trans_le (min_le_right _ _))
  change ‖moment r A z x s-S.classMoment S d X (fun i=>J r 6 (leg R.family s i))‖ < ε
  rw [equal X (apart inT)]
  rw [←dist_eq_norm]
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add first second).trans_eq (add_halves ε))

theorem cells (hr : 0 < r) {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ z : UVIndex in (Y : Filter _), ∀ x ∈ K, ‖full r A z x - WilsonPositionThermometerConnected.value (sample F J r x)‖ < ε := by
  let target := WilsonPositionThermometerReading.sample F J r
  let B (z : UVIndex) (x : Points 3) (s : Badge) := moment r A z x s
  have cont : ContinuousOn target K := by
    apply continuousOn_pi.mpr
    intro s
    let v (i : Fin 3) : S.Tag := ⟨6,J r 6 (leg R.family s i)⟩
    exact ((S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn).comp
      (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr (sep hx))
  let V := target '' K
  have vc : IsCompact V := hk.image_of_continuousOn cont
  let W := cthickening (1:ℝ) V
  have wc : IsCompact W := vc.cthickening
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp
    (wc.uniformContinuousOn_of_continuous WilsonPositionThermometerConnected.continuous_value.continuousOn) ε he
  have dpos : 0 < min 1 δ := lt_min one_pos hδ
  have bank := cut F J r A hG hl filed hr hk sep dpos
  filter_upwards [bank] with z ready x hx
  have near : dist (B z x) (target x) < min 1 δ := (dist_pi_lt_iff dpos).mpr (fun s => by
    simpa only [dist_eq_norm,target,B] using ready s x hx)
  have av : target x ∈ V := ⟨x,hx,rfl⟩
  have bw : B z x ∈ W := mem_cthickening_of_dist_le (B z x) (target x) 1 V av (near.le.trans (min_le_left _ _))
  change ‖WilsonPositionThermometerConnected.value (B z x) - WilsonPositionThermometerConnected.value (target x)‖ < ε
  simpa only [dist_eq_norm] using
    move (B z x) bw (target x) (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))

omit hG hl filed in
theorem measurable (z : UVIndex) : Measurable (full r A z) := by
  let I (x : Fin 3 → Cover) := WilsonPositionThermometerConnected.value (fun s =>
    R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6) (wrap _ ∘ x)
      (fun i => along A (A.station.wheel.atCut z) (s,i)))
  have grid : Measurable (address (R.family.S.a z.1) : Points 3 → (Fin 3 → Cover)) := by
    apply measurable_to_countable
    intro x
    exact measurable_segment (R.family.S.a_pos z.1) (address (R.family.S.a z.1) x)
  exact (measurable_of_countable I).comp (grid.comp (continuous_const_smul r).measurable)

omit hG hl filed in
private theorem continuous_target {r : ℝ} (hr : 0 < r) : ContinuousOn
    (fun x => WilsonPositionThermometerConnected.value (sample F J r x)) (conf 3) := by
  apply WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  let v (i : Fin 3) : S.Tag := ⟨6,J r 6 (leg R.family s i)⟩
  exact ((S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn).comp
    (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr hx)

variable {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)
theorem signed (hr : 0 < r) : Tendsto (fun z => (Rose.test K).applyTo (full r A z))
    (Y : Filter _) (𝓝 (tested F J K r)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε he
  let Φ := Rose.test K
  let u := (fun x => WilsonPositionThermometerConnected.value (sample F J r x))
  let M := (∫ x : Points 3, ‖Rose.test K x‖)
  have hm : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
  let t := (ε/2)/(M+1)
  have ht : 0<t := div_pos (half_pos he) (by linarith)
  have price : M*t < ε := by
    calc M*t ≤ (M+1)*t := mul_le_mul_of_nonneg_right (by linarith) ht.le
         _ = ε/2 := by dsimp only [t];field_simp [show M+1≠0 by linarith]
         _ < ε := half_lt_self he
  have gi : Integrable (fun x : Points 3 => Φ x) := Φ.continuous.integrable_of_hasCompactSupport Φ.hasCompactSupport
  have target := Φ.smearing (continuous_target F J hr)
  filter_upwards [cells F J r A hG hl filed hr Φ.hasCompactSupport Φ.tsupport_subset ht] with z bound
  let v := full r A z
  have am : AEStronglyMeasurable (fun x : Points 3 => Φ x*v x) volume :=
    (Φ.continuous.measurable.mul (measurable r A z)).aestronglyMeasurable
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

end YM.Integration.WilsonPositionThermometerStationReading
end
