import YM.Integration.WilsonPositionThermometerPhases
import YM.Integration.WilsonMovingCalibratedFields

/-! The seven subset moments of the ORIGINAL physical thermometer itself
on the actual regulated Wilson law, before every continuum integration.
No thermal field is assumed to coincide with a measured position field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerRegulator
open Function Filter Set Finset Metric MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open OPE OPE.Orbits Climb Trace.Pilot Next.UVStress RG12 RG17 PhysMS PhysicalNext.Repeat.Legato
open XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox
open WilsonPositionThermometerReading
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
variable (J : ℝ → PhysMS.tower S) (r : ℝ)

def written (s : Badge) (j : Fin 3) : R.family.label 6 :=
  S.representative 6 (J r 6 (leg R.family s j))

def original (s : Badge) (z : UVIndex) (x : Points 3) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun _ : Fin 3=>6)
    (wrap _ ∘ address (R.family.S.a z.1) (r • x)) (written J r s)

def full (z : UVIndex) (x : Points 3) : ℂ :=
  WilsonPositionThermometerConnected.value (fun s => original J r s z x)

/-- All factors in a subset belong to the one originally normalized
Wilson measure at this regulator and period. -/
theorem measured (s : Badge) (z : UVIndex) (x : Points 3) :
    original J r s z x =
      R.family.omega z.1 z.2 (fun U => ∏ i : Fin 3,R.family.O z.1 z.2
        (written J r s i) (wrap _ (address (R.family.S.a z.1) (r • x) i)) U) := rfl

theorem cut (hG : G.Simple) {l : Filter UVIndex} (hl : l ≤ f.fuse) (hr : 0<r)
    {K : Set (Points 3)} (hk : IsCompact K) (sep : K ⊆ conf 3) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ z : UVIndex in l,∀ s : Badge,∀ x∈K,
      ‖original J r s z x - WilsonPositionThermometerReading.sample F J r x s‖ < ε := by
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
  let a := written J r s
  let A (y : Points 3) := S.value d y a
  have cont : ContinuousOn A U := ((F.room.kernel.smooth.on_conf d a).continuousOn).mono inside
  obtain ⟨δ,hδ,move⟩ := Metric.uniformContinuousOn_iff.mp (cu.uniformContinuousOn_of_continuous cont) (ε/2) (half_pos he)
  have atTop' : Tendsto (fun z : UVIndex => z.1) l atTop :=
    tendsto_atTop.mpr fun j => (large_mesh f j).filter_mono hl
  have fine : Tendsto (fun z : UVIndex => (4*3:ℝ)*C.S.a z.1) l (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=(4*3:ℝ))).mul (C.S.shrinks.comp atTop')
  have bank := WilsonMovingCalibratedFields.paid R hG F hl d (fun _ => a) a
    (fun _ => tendsto_const_nhds) U cu inside (ε/2) (half_pos he)
  filter_upwards [bank,fine.eventually (gt_mem_nhds (lt_min ht hδ))] with z charged mesh x hx
  let X := r • x
  let c := address (C.S.a z.1) X
  let Y := tag (C.S.a z.1) c
  have inT : X ∈ T := ⟨x,hx,rfl⟩
  have near : dist Y X < min t δ := (Extraction.approximate (C.S.a_pos z.1) X).trans_lt mesh
  have inU : Y ∈ U := mem_cthickening_of_dist_le Y X t T inT (near.le.trans (min_le_left _ _))
  have first : dist (original J r s z x) (A Y) < ε/2 := charged c inU
  have second := move Y inU X (self_subset_cthickening T inT) (near.trans_le (min_le_right _ _))
  change ‖original J r s z x - A X‖ < ε
  rw [←dist_eq_norm]
  exact (dist_triangle _ _ _).trans_lt ((add_lt_add first second).trans_eq (add_halves ε))

end YM.Integration.WilsonPositionThermometerRegulator
