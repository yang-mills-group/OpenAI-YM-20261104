import YM.Integration.WilsonPositionThermometerDefect
import YM.Integration.WilsonOrdinaryPositionReceiver
import YM.Integration.WilsonMacroscopicMatchedSection
import YM.Integration.WilsonMovingCalibratedFields

/-! Genuine filed reporting-mesh representatives for all seven subsets of the
measured physical three-point coupling, selected together before any regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerAtRef
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) (r : ℝ)


variable (L : Layout F) (E : RG17.Free R.family 6 →L[ℂ] R.family.label 6)

/-- The actual Wilson moment using the filed raw labels at the reporting
date and their original transport, including the engineering factors. -/
def moment (s : Badge) (z : UVIndex) (x : Points 3) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6)
    (wrap _ ∘ address (R.family.S.a z.1) (r • x))
    (fun i=>RG17.atRef L 6 r z (E (leg R.family s i)))

def full (z : UVIndex) (x : Points 3) : ℂ :=
  WilsonPositionThermometerConnected.value (fun s=>moment F r L E s z x)

theorem measured (s : Badge) (z : UVIndex) (x : Points 3) :
    moment F r L E s z x =
      R.family.omega z.1 z.2 (fun U=>∏ i : Fin 3,R.family.O z.1 z.2
        (RG17.atRef L 6 r z (E (leg R.family s i)))
        (wrap _ (address (R.family.S.a z.1) (r • x) i)) U) := rfl
theorem cut (hG : G.Simple) {l : Filter UVIndex} [l.NeBot] (hl : l ≤ L.lens)
    (admit : R.family.ref 6 ≤ L.level r)
    (lifted : ∀ v,RG17.master L 6 r (E v)=J r 6 v) (hr : 0<r)
    {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in l,∀ s : Badge,∀ x∈K,
      ‖moment F r L E s z x - WilsonPositionThermometerReading.sample F J r x s‖ < ε := by
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
  let raw (i : Fin 3) := E (leg R.family s i)
  let a (i : Fin 3) := RG17.locatedRef L 6 r (raw i)
  let vals (z : UVIndex) (i : Fin 3) := RG17.atRef L 6 r z (raw i)
  have measured (i : Fin 3) : Tendsto (fun z=>vals z i) l (𝓝 (a i)) :=
    RG17.tendsRef L hl (v:=fun _=>raw i) tendsto_const_nhds admit
  have pay (i : Fin 3) : S.project 6 (a i)=J r 6 (leg R.family s i) :=
    (RG17.payRef L (raw i)).trans (lifted _)
  have equal (X : Points 3) (legal : X∈conf 3) :
      S.classMoment S d X (fun i=>J r 6 (leg R.family s i))=S.value d X a := by
    simp_rw [←pay]
    exact S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) legal (fun i=>⟨d i,a i⟩)
  let A (y : Points 3) := S.value d y a
  have cont : ContinuousOn A U := ((F.room.kernel.smooth.on_conf d a).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (cu.uniformContinuousOn_of_continuous cont) (ε/2) (half_pos he)
  have atTop' : Tendsto (fun z : UVIndex => z.1) l atTop :=
    tendsto_atTop.mpr fun j => (large_mesh f j).filter_mono (hl.trans L.certified)
  have fine : Tendsto (fun z : UVIndex => (4*3:ℝ)*C.S.a z.1) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*3:ℝ))).mul (C.S.shrinks.comp atTop')
  have bank := WilsonMovingCalibratedFields.paid R hG F (hl.trans L.certified) d vals a
    measured U cu inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z charged mesh x hx
  let X := r • x
  let c := address (C.S.a z.1) X
  let Y := tag (C.S.a z.1) c
  have inT : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (C.S.a_pos z.1) X).trans_lt mesh
  have inU : Y ∈ U := mem_cthickening_of_dist_le Y X t T inT (near.le.trans (min_le_left _ _))
  have first : dist (moment F r L E s z x) (A Y) < ε/2 := charged c inU
  have second := move Y inU X (self_subset_cthickening T inT) (near.trans_le (min_le_right _ _))
  change ‖moment F r L E s z x-S.classMoment S d X (fun i=>J r 6 (leg R.family s i))‖ < ε
  rw [equal X (apart inT)]
  rw [←dist_eq_norm]
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add first second).trans_eq (add_halves ε))


theorem purchased (scene : Pier.Scene.ScenePlan R F L)
    (funds : Pier.Lair.Paying F (Pier.Lair.tender F L J) 6) :
    ∃ (p : ℕ) (c : ℝ) (B : ℝ→RG17.Free R.family 6 →L[ℂ] R.family.label 6),0≤c ∧
      ∀ᶠ r in Trace.Pilot.trail,
        (∀ v,RG17.master L 6 r (B r v)=J r 6 v) ∧
        ‖B r‖≤c*R.family.path.levels.clock.hatBeta (L.level r)^p :=
  WilsonMacroscopicMatchedSection.purchased F L J scene.shift 6 funds

end YM.Integration.WilsonPositionThermometerAtRef
