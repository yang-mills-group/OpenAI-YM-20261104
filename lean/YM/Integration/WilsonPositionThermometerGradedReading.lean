import YM.Integration.WilsonPositionThermometerGradedSource
import YM.Integration.WilsonPositionThermometerCapStation
import YM.Integration.WilsonMovingCalibratedFields
import YM.Integration.WilsonSeparatedOriginalThermometerCells

/-! The measured Wilson coupling on the three actual (6,4,4) cutoff lifts.
The regulator limits use one oriented station and all of its original fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerGradedReading
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators

open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource Trace.Pilot MergeProof.East
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
variable (F : Final R.family f S) (J : ℝ → PhysMS.tower S) (r : ℝ)
variable (A : Group R.family 6)

def vector (s : Badge) (i : Fin 3) : (Bel R.family.book).Field (grade i) :=
  A.change (grade i) (source R.family s i)

def row (z : UVIndex) (x : Fin 3 → Site (R.family.side z.1 z.2)) (s : Badge) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun i => (grade i).val) x
    (fun i => A.station.wheel.atCut z (index A (grade i)) (vector A s i))

def moment (z : UVIndex) (x : Points 3) := row A z (WilsonSeparatedOriginalThermometerCells.positions (R:=R) r z x)

def full (z : UVIndex) (x : Points 3) := WilsonPositionThermometerConnected.value (moment r A z x)

variable {Y : Ultrafilter UVIndex} (hG : G.Simple) (hl : (Y : Filter _) ≤ f.fuse)
variable (moves : Tendsto A.station.wheel.atCut (Y : Filter _) (𝓝 A.lift))
variable (lands : ∀ s i, S.project (grade i) (A.lift (index A (grade i)) (vector A s i)) =
    J r (grade i) (source R.family s i))
variable (nested : ∀ x ∈ conf 3, ∀ s : Badge, sample F J r x s =
    PhysMS.measured F none (J r) (d:=fun i => (grade i).val) (source R.family s) r x)

include F hG hl in
private theorem rounded {n : ℕ} (d : Caps n)
    (vals : UVIndex → R.family.book.Vector d) (a : R.family.book.Vector d)
    (measured : ∀ i, Tendsto (fun z => vals z i) (Y : Filter _) (𝓝 (a i)))
    (hr : 0<r) {K : Set (Points n)} (hk : IsCompact K) (sep : K ⊆ conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in (Y : Filter _), ∀ x∈K,
    dist (R.family.ensemble (N:=z.1) (p:=z.2) d (wrap _ ∘ address (R.family.S.a z.1) (r • x)) (vals z))
      (S.value d (r • x) a) < ε := by
  let T := (fun x : Points n => r • x) '' K
  have compact : IsCompact T := hk.image (continuous_const_smul r)
  have apart : T ⊆ conf n := by rintro _ ⟨x,hx,rfl⟩;exact Work.A05.smul_conf hr (sep hx)
  obtain ⟨t,ht,inside⟩ := compact.exists_cthickening_subset_open (conf_open _) apart
  let U := cthickening t T
  have cu : IsCompact U := compact.cthickening
  let result (y : Points n) := S.value d y a
  have cont : ContinuousOn result U := ((F.room.kernel.smooth.on_conf d a).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (cu.uniformContinuousOn_of_continuous cont) (ε/2) (half_pos he)
  have atTop' : Tendsto (fun z : UVIndex => z.1) (Y : Filter _) atTop :=
    tendsto_atTop.mpr fun j => (large_mesh f j).filter_mono hl
  have fine : Tendsto (fun z : UVIndex => (4*n:ℝ)*R.family.S.a z.1) (Y : Filter _) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*n:ℝ))).mul (R.family.S.shrinks.comp atTop')
  have bank := WilsonMovingCalibratedFields.paid R hG F hl d vals a
    measured U cu inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z charged mesh x hx
  let X := r • x
  let c := address (R.family.S.a z.1) X
  let Y := tag (R.family.S.a z.1) c
  have inT : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (R.family.S.a_pos z.1) X).trans_lt mesh
  have inU : Y ∈ U := mem_cthickening_of_dist_le Y X t T inT (near.le.trans (min_le_left _ _))
  exact (dist_triangle _ (result Y) _).trans_lt
    (add_lt_add (charged c inU)
      (move Y inU X (self_subset_cthickening T inT) (near.trans_le (min_le_right _ _))) |>.trans_eq (add_halves ε))

private theorem lift_entry {D : ℕ} (j : Fin (D+1)) (u : (Bel R.family.book).Field j)
    {V : Vane R.family D} {T : Lifts R.family D}
    (h : Tendsto V.wheel.atCut (Y : Filter _) (𝓝 T)) :
    Tendsto (fun z => V.wheel.atCut z j u) (Y : Filter _) (𝓝 (T j u)) := by
  have look : Continuous (fun l : Lifts R.family D => l j) := continuous_apply j
  have act : Continuous (fun c : (Bel R.family.book).Field j →L[ℂ] R.family.book.Ref j => c u) :=
    (ContinuousLinearMap.apply ℂ (R.family.book.Ref j) u).continuous
  exact (act.comp look).continuousAt.tendsto.comp h

include F in
private theorem projected {n : ℕ} (d : Caps n) (a : R.family.book.Vector d) (w : Ribbon S d)
    (eq : ∀ i, S.project (d i) (a i)=w i) {x : Points n} (legal : x∈conf n) :
    S.classMoment S d x w = S.value d x a := by
  have eqs : w=fun i => S.project (d i) (a i) := funext fun i => (eq i).symm
  rw [eqs]
  exact S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) legal (fun i=>⟨d i,a i⟩)

include F hG hl moves in
private theorem rounded_row (s : Badge) (hr : 0<r) {K : Set (Points 3)} (hk : IsCompact K)
    (sep : K ⊆ conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in (Y : Filter _), ∀ x∈K,
    dist (moment r A z x s) (S.value (fun i => (grade i).val) (r • x)
      (fun i => A.lift (index A (grade i)) (vector A s i))) < ε := by
  exact rounded F r hG hl (fun i => (grade i).val)
    (fun z i => A.station.wheel.atCut z (index A (grade i)) (vector A s i))
    (fun i => A.lift (index A (grade i)) (vector A s i))
    (fun i => lift_entry (index A (grade i)) (vector A s i) moves) hr hk sep he

include F lands nested in
private theorem row_projection (s : Badge) {x : Points 3} (hx : x ∈ conf 3) (hr : 0<r) :
    sample F J r x s = S.value (fun i => (grade i).val) (r • x)
      (fun i => A.lift (index A (grade i)) (vector A s i)) := by
  exact (nested x hx s).trans (projected F (fun i => (grade i).val) _
    (fun i => J r (grade i) (source R.family s i)) (lands s) (Work.A05.smul_conf hr hx))

include hG hl moves lands nested in
theorem cut (hr : 0 < r) {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ z : UVIndex in (Y : Filter _), ∀ s : Badge, ∀ x ∈ K, ‖moment r A z x s - sample F J r x s‖ < ε := by
  apply Filter.eventually_all.mpr
  intro s
  filter_upwards [rounded_row F r A hG hl moves s hr hk sep he] with z good x hx
  rw [row_projection F J r A lands nested s (sep hx) hr, ←dist_eq_norm]
  exact good x hx

include hG hl moves lands nested in
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
  have bank := cut F J r A hG hl moves lands nested hr hk sep dpos
  filter_upwards [bank] with z ready x hx
  have near : dist (B z x) (target x) < min 1 δ := (dist_pi_lt_iff dpos).mpr (fun s => by
    simpa only [dist_eq_norm,target,B] using ready s x hx)
  have av : target x ∈ V := ⟨x,hx,rfl⟩
  have bw : B z x ∈ W := mem_cthickening_of_dist_le (B z x) (target x) 1 V av (near.le.trans (min_le_left _ _))
  change ‖WilsonPositionThermometerConnected.value (B z x) - WilsonPositionThermometerConnected.value (target x)‖ < ε
  simpa only [dist_eq_norm] using
    move (B z x) bw (target x) (self_subset_cthickening V av) (near.trans_le (min_le_right _ _))

theorem measurable (z : UVIndex) : Measurable (full r A z) :=
  (measurable_of_finite (fun x => WilsonPositionThermometerConnected.value (row A z x))).comp
    (WilsonSeparatedOriginalThermometerCells.placed (R:=R) r z)

private theorem continuous_target {r : ℝ} (hr : 0 < r) : ContinuousOn
    (fun x => WilsonPositionThermometerConnected.value (sample F J r x)) (conf 3) := by
  apply WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
  apply continuousOn_pi.mpr
  intro s
  let v (i : Fin 3) : S.Tag := ⟨6,J r 6 (leg R.family s i)⟩
  exact ((S.class_smooth (spectator F none) (spectate F none).smooth v).continuousOn).comp
    (continuous_const_smul r).continuousOn (fun _ hx => Work.A05.smul_conf hr hx)

variable {V : XSpace.Normalize.Store G} (K : XSpace.Rose.Pick V)
include hG hl moves lands nested in
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
  filter_upwards [cells F J r A hG hl moves lands nested hr Φ.hasCompactSupport Φ.tsupport_subset ht] with z bound
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

/-- At every sufficiently small real radius, take the original regulated
arrays at their genuine ranks and retain the prescribed connected test. -/
theorem original (B : ℝ → Group R.family 6) (lead : PhysMS.Leading F J)
    (hG : G.Simple) (hl : (Y : Filter _) ≤ f.fuse) {I : Type} [Fintype I]
    {d : I → Fin 7} {u : ∀ i, (Bel R.family.book).Field (d i)} {m : ℕ}
    {H : (Bel R.family.book).Hierarchy}
    (book : ∀ᶠ r in Trace.Pilot.trail, projects (f:=f) (Y:=Y) H d u (B r) (J r) m r) :
    ∀ᶠ r in Trace.Pilot.trail, Tendsto (fun z => (Rose.test K).applyTo (full r (B r) z))
      (Y : Filter _) (𝓝 (tested F J K r)) := by
  filter_upwards [book, WilsonPositionThermometerGradedSource.measured F J lead, RG17.positiveLength]
    with r ready nest hr
  exact signed F J r (B r) hG hl ready.2.2.2.1
    (fun s i => ((ready.2.2.2.2.1 (grade i)).2.2 _).symm) nest K hr

end YM.Integration.WilsonPositionThermometerGradedReading
end
