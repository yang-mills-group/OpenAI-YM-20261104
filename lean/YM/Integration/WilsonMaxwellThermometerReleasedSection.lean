import YM.Integration.WilsonMaxwellThermometerReleasedSlope
import YM.Integration.WilsonThermometerPositionTunedGalop
/-! Put the normalized finite original Wilson section and the genuine
public reannouncements on one three-site test before taking the signed error. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReleasedSection
open Function Filter Set Finset Spec Extraction Table RG Wilson Lattice OPE OPE.Orbits Climb Trace Trace.Pilot Next.UVStress
open PhysicalNext.Repeat.Legato RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose
open XSpace.Cirrus XSpace.Photo WilsonMaxwellThermometerInteracting WilsonMaxwellThermometerShiftedPanel
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonMaxwellThermometerPublicStation
open WilsonMaxwellThermometerSignedWallet WilsonSeparatedOriginalThermometerCells WilsonSeparatedOriginalThermometerDetectorMesh
open WilsonOriginalNullReleasedMaximalLimit
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G)(W:Initialize G){V:Normalize.Store G}(K:Rose.Pick V)(s:ℝ→ℕ)

/-- The signed test mass is still evaluated on each full original cutoff cell. -/
def cells (r:ℝ)(z:ℕ×ℕ)(f:Sample 3→ℂ):ℂ:=
  if h:s r≤z.1 then
    let board:=WilsonMaxwellThermometerSignedWallet.board R (s r) r z.2
    ∑o,weight (Rose.test K) (positions (R:=R) r z) o •
      f (translated board (Mesh.back board ((R.family.S.toDepth h z.2).parent ∘ o)))
  else 0

def originalSection (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):ℂ:=
  cells R K s r z fun x=>
    let X:=WilsonThermometerPositionTunedGalop.originalRead R W (V:=V) x p
    first (X 0) (X 1)

def sectionLoss (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):ℂ:=
  cells R K s r z fun x=>
    let X:=WilsonThermometerPositionTunedGalop.originalRead R W (V:=V) x p
    let Q:=WilsonMaxwellThermometerPublicGalop.quotient W (V:=V) x p
    let J:=WilsonThermometerPositionTunedGalop.loss R W (V:=V) x p
    first (X 0) (J 1)+(first (X 0) (Q 1)-first (Q 0) (Q 1))

theorem exact (r:ℝ)(z:ℕ×ℕ)(p:Tags G 6 3):
    originalSection R W K s r z p - report R W K s r z p=sectionLoss R W K s r z p:=by
  by_cases h:s r≤z.1
  · simp only [originalSection,sectionLoss,cells,report,dif_pos h,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro o _
    let m:=WilsonMaxwellThermometerSignedWallet.board R (s r) r z.2
    let x:=translated m (Mesh.back m ((R.family.S.toDepth h z.2).parent ∘ o))
    rw [←smul_sub]
    exact congrArg (fun t:ℂ=>weight (Rose.test K) (positions (R:=R) r z) o • t)
      (WilsonThermometerPositionTunedGalop.first_order R W (V:=V) x p)
  · simp only [originalSection,sectionLoss,cells,report,dif_neg h,sub_zero]

variable {f:Extraction.Order}{Y:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{S:Table R.family.book}
variable (F:Final R.family f S)(J:ℝ→tower S)(A:ℝ→Group R.family 6)
local notation "Z" => WilsonPositionCorrectedCap.adjusted F J V A
local notation "k" => fun r=>(Z r).station.k
local notation "cut"=>trail.curry (Y:Filter (ℕ×ℕ))
local notation "moved" => fun (v:ℝ×(ℕ×ℕ)→∀i,Axes R i) (w:ℝ×(ℕ×ℕ))=>
  deposited R (k w.1) w.1 w.2.2 (v w)

theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)
    (book:Book (f:=f) (l:=Y) (H:=H) A J)(lead:Leading F J)(q:ℕ)(prior:(Y:Filter _)≤f.fuse)
    (v:ℝ×(ℕ×ℕ)→∀i,Axes R i)
    (paid:∀ᶠ w in cut,∀i,Solved R (Z w.1) q w.2.1 w.2.2 univ i (v w i))
    (heard:Tendsto (fun w:ℝ×(ℕ×ℕ)=>sectionLoss R W K k w.1 w.2 (moved v w)) cut (𝓝 0)):
    Tendsto (fun w:ℝ×(ℕ×ℕ)=>originalSection R W K k w.1 w.2 (moved v w)) cut
      (𝓝 ((Rose.c_T K:ℝ):ℂ)):=by
  have pub:=WilsonMaxwellThermometerReleasedSlope.original R W K F J A simple shop book lead q prior v paid
  have combined:=heard.add pub
  simp only [zero_add] at combined
  apply combined.congr'
  apply Filter.Eventually.of_forall
  intro w
  change sectionLoss R W K k w.1 w.2 (moved v w)+report R W K k w.1 w.2 (moved v w)=_
  rw [←exact,sub_add_cancel]

end YM.Integration.WilsonMaxwellThermometerReleasedSection
end
