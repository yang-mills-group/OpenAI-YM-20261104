import YM.Integration.WilsonPositionCorrectedCap
import YM.Integration.WilsonPositionThermometerGradedReading
import YM.PhysMS.Frame.Tensor

/-! On the original corrected thermometer, all proper moments converge to the
actual grade-(6,4,4) Maxwell table, uniformly on the separated test support.
Each cutoff moment carries the original inverse at its own centered site. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedProperFaces
open Filter Function Set Metric MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato
open RG17 XSpace XSpace.Normalize OPE OPE.Orbits Climb Table Spec Extraction Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open XSpace.Rose WilsonPositionCapTransport Maxwell Maxwell.Free WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open private rounded projected lift_entry from YM.Integration.WilsonPositionThermometerGradedReading
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {S:Table R.family.book}
  (F:Final R.family f S) (J:ℝ→tower S) (V:Store G) (A:ℝ→Group R.family 6)
local notation "D" => ((fun i:Fin 3=>(grade i).val):Caps 3)

def ground (x:Points 3) (s:Badge):ℂ:=WickGoal (C:=R.family) (d:=D) (source R.family s) x
def upper (r:ℝ) (s:Badge):MaxwellSlots R.family D:=
  fun i=>WilsonPositionPrescribedLift.field F J V (grade i) r (source R.family s i)
def read (r:ℝ) (x:Points 3) (s:Badge):ℂ:=PhysMS.measured F none (J r) (upper R F J V r s) r x

theorem leading (lead:Leading F J) {E:Set (Points 3)} (compact:IsCompact E) (legal:E⊆conf 3)
    (δ:ℝ) (pos:0<δ):
    ∀ᶠr in trail,∀s:Badge,∀x∈E,‖read R F J V r x s-ground R x s‖<δ:=by
  apply Filter.eventually_all.mpr
  intro s
  have limit (i:Fin 3):Tendsto (fun r=>upper R F J V r s i) trail (𝓝 (source R.family s i)):=
    WilsonPositionPrescribedLeading.applied F J V lead _ _
  have T:=measured_tensor F (r:=id) (v:=fun _=>none) (l:=trail) (P:=J) (w:=fun r=>upper R F J V r s)
    (u:=source R.family s) RG17.positiveLength D 0 (fun i=>whole R.family (grade i)) compact legal
    (fun _=>lead.lead 3 D _ 0 E compact legal) limit
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp T δ pos] with r paid x hx
  have h:=paid x hx
  rw [dist_comm,dist_eq_norm] at h
  let a:=PhysMS.measured F none (J r) (upper R F J V r s) r
  let b:= WickGoal (C:=R.family) (d:=D) (source R.family s)
  change ‖iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x‖<δ at h
  have jets:iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x=iteratedFDeriv ℝ 0 (a-b) x:=by ext;simp
  rw [jets,norm_iteratedFDeriv_zero] at h
  exact h

variable {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel R.family.book).Hierarchy}
  (simple:G.Simple) (hl:(Y:Filter _)≤f.fuse)
  (book:Book (f:=f) (l:=Y) (H:=H) A J)

include simple hl in
theorem cutoff (r:ℝ) (rp:0<r) {E:Set (Points 3)} (compact:IsCompact E) (legal:E⊆conf 3)
    (ε:ℝ) (hp:0<ε)
    (ready:projects (f:=f) (Y:=Y) H (fun i:Address R.family 6=>i.1) entry (A r) (J r) 0 r):
    ∀ᶠz:ℕ×ℕ in (Y:Filter _),∀s:Badge,∀x∈E,‖WilsonPositionThermometerGradedReading.moment r
      (WilsonPositionCorrectedCap.adjusted F J V A r) z x s-read R F J V r x s‖<ε:=by
  apply Filter.eventually_all.mpr
  intro s
  let Z:=A r
  let U:=upper R F J V r s
  let m:R.family.book.Vector D:=fun i=>Z.lift (index Z (grade i)) (Z.change (grade i) (U i))
  let M (z:ℕ×ℕ):R.family.book.Vector D:=fun i=>Z.station.wheel.atCut z (index Z (grade i)) (Z.change (grade i) (U i))
  have move:=ready.2.2.2.1
  have moves (i:Fin 3):Tendsto (fun z=>M z i) (Y:Filter _) (𝓝 (m i)):=
    lift_entry (index Z (grade i)) (Z.change (grade i) (U i)) move
  have project (i:Fin 3):S.project (grade i) (m i)=J r (grade i) (U i):=
    ((ready.2.2.2.2.1 (grade i)).2.2 (U i)).symm
  have bank:=rounded F r simple hl D M m moves rp compact legal hp
  filter_upwards [bank] with z cell x hx
  have proj:=projected F D m (fun i=>J r (grade i) (U i)) project (Work.A05.smul_conf rp (legal hx))
  change ‖R.family.ensemble (N:=z.1) (p:=z.2) D _ (M z)-S.classMoment S D (r • x) _‖<_
  rw [proj,←dist_eq_norm]
  exact cell x hx

include simple hl book in
theorem original (lead:Leading F J) {E:Set (Points 3)} (compact:IsCompact E) (legal:E⊆conf 3)
    (ε:ℝ) (pos:0<ε):
    ∀ᶠw:ℝ×(ℕ×ℕ) in trail.curry (Y:Filter _),∀s:Badge,∀x∈E,
      ‖WilsonPositionThermometerGradedReading.moment w.1 (WilsonPositionCorrectedCap.adjusted F J V A w.1)
        w.2 x s-ground R x s‖<ε:=by
  apply eventually_curry_iff.mpr
  filter_upwards [book 0,RG17.positiveLength,leading R F J V lead compact legal (ε/2) (half_pos pos)]
    with r ready rp close
  filter_upwards [cutoff R F J V A simple hl r rp compact legal (ε/2) (half_pos pos) ready] with z paid s x hx
  exact (norm_sub_le_norm_sub_add_norm_sub _ (read R F J V r x s) _).trans_lt
    ((add_lt_add (paid s x hx) (close s x hx)).trans_eq (add_halves ε))

end YM.Integration.WilsonMaxwellThermometerNominatedProperFaces
