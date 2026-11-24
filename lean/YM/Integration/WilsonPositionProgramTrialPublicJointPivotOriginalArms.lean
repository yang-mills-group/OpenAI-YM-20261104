import YM.Integration.WilsonPositionProgramTrialPublicJointPivotMeshClock
import YM.Integration.WilsonMaxwellThermometerNominatedProperFaces
import YM.Integration.WilsonThermometerUnitFilingFourSquare

/-! The actual finite torus fields supplied by one previously issued common cap book. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalArms
open Function Filter Set MeasureTheory Spec Table Extraction Lattice Climb PhysMS RG17 RG
open PhysicalNext.Repeat.Legato Wilson Trace Metric Cells Push.GridApprox
open Maxwell XSpace XSpace.Normalize Trace.Pilot Next.UVStress
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonThermometerUnitFilingFourSquare (Arm)
open private rounded projected lift_entry from YM.Integration.WilsonPositionThermometerGradedReading
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {o:Extraction.Order} {S:Table R.family.book}
variable (F:Final R.family o S) (J:ℝ→tower S) {l:Ultrafilter (ℕ×ℕ)} {D:ℕ}
variable {H:(Bel R.family.book).Hierarchy} {n:ℕ}

abbrev Ready (A:Group R.family D) (P:tower S) (r:ℝ) :=
  projects (f:=o) (Y:=l) H (fun i:Address R.family D=>i.1) entry A P 0 r

def source (A:Group R.family D) (j:Fin (D+1)) (p:Sec G j) (z:ℕ×ℕ) : R.family.label j :=
  A.station.wheel.atCut z (index A j) (A.change j ((Maxwell.Free.fields R.family.labels j).symm p))

def issued {r:ℝ} (A:Group R.family D) (ready:Ready (o:=o) (l:=l) (H:=H) A (J r) r)
    (j:Fin (D+1)) (p:Sec G j) :
    Arm R.family S (l:Filter _) j (J r j ((Maxwell.Free.fields R.family.labels j).symm p)) where
  source := source A j p
  label := A.lift (index A j) (A.change j ((Maxwell.Free.fields R.family.labels j).symm p))
  approaches := lift_entry (index A j) _ ready.2.2.2.1
  represents := ((ready.2.2.2.2.1 j).2.2 _).symm

def raw (A:Group R.family D) (j:Fin n→Fin (D+1)) (p:(i:Fin n)→Sec G (j i))
    (r:ℝ) (z:ℕ×ℕ) (x:Points n) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun i=>(j i).val)
    (wrap _ ∘ address (R.family.S.a z.1) (r • x)) (fun i=>source A (j i) (p i) z)

theorem cutoff (simple:G.Simple) (prior:(l:Filter _)≤o.fuse) {r:ℝ} (rp:0<r)
    (A:Group R.family D) (ready:Ready (o:=o) (l:=l) (H:=H) A (J r) r)
    (j:Fin n→Fin (D+1)) (p:(i:Fin n)→Sec G (j i))
    {K:Set (Points n)} (hk:IsCompact K) (apart:K⊆conf n) {e:ℝ} (ep:0<e) :
    ∀ᶠ z:ℕ×ℕ in (l:Filter _),∀x∈K,‖raw A j p r z x-
      PhysMS.measured F none (J r) (d:=fun i=>(j i).val)
        (fun i=>(Maxwell.Free.fields R.family.labels _).symm (p i)) r x‖<e := by
  let a (i:Fin n) := issued J A ready (j i) (p i)
  have close := rounded F r simple prior (fun i=>(j i).val)
    (fun z i=>(a i).source z) (fun i=>(a i).label) (fun i=>(a i).approaches) rp hk apart ep
  filter_upwards [close] with z paid x hx
  have same := projected F (fun i=>(j i).val) (fun i=>(a i).label)
    (fun i=>J r (j i) ((Maxwell.Free.fields R.family.labels _).symm (p i)))
    (fun i=>(a i).represents) (Work.A05.smul_conf rp (apart hx))
  change ‖R.family.ensemble (N:=z.1) (p:=z.2) _ _ _-S.classMoment S _ (r • x) _‖<_
  rw [same,←dist_eq_norm]
  exact paid x hx

def ordinary (A:Group R.family D) (j:Fin n→Fin (D+1)) (p:(i:Fin n)→Sec G (j i))
    {r:ℝ} (rp:0<r) (φ:Test n) (z:ℕ×ℕ) : ℂ :=
  Order.smears R.family z.1 z.2 (fun i=>⟨(j i).val,source A (j i) (p i) z⟩) (dilate rp φ)

theorem measured (prior:(l:Filter _)≤o.fuse) {r:ℝ} (rp:0<r)
    (A:Group R.family D) (ready:Ready (o:=o) (l:=l) (H:=H) A (J r) r)
    (j:Fin n→Fin (D+1)) (p:(i:Fin n)→Sec G (j i)) (φ:Test n) :
    Tendsto (ordinary A j p rp φ) (l:Filter _) (𝓝 (φ.applyTo (fun x=>
      PhysMS.measured F none (J r) (fun i=>(Maxwell.Free.fields R.family.labels _).symm (p i)) r x))) := by
  have move := WilsonThermometerUnitFilingFourSquare.measured F prior
    (fun i (_:Bool)=>issued J A ready (j i) (p i)) (fun _=>false) (dilate rp φ)
  rw [zoom_integral] at move
  exact move

theorem original (prior:(l:Filter _)≤o.fuse) {r:ℝ} (rp:0<r)
    (A:Group R.family D) (ready:Ready (o:=o) (l:=l) (H:=H) A (J r) r)
    (d:Fin (D+1)) (p:Fin n→Sec G d) (φ:Test n) :
    Tendsto (ordinary A (fun _:Fin n=>d) p rp φ) (l:Filter _)
      (𝓝 (WilsonPositionPrescribedScreen.hierarchy F J d r n φ p)) := by
  rw [WilsonPositionPrescribedScreen.actual F J d n φ p rp]
  exact measured F J prior rp A ready _ p φ

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalArms
