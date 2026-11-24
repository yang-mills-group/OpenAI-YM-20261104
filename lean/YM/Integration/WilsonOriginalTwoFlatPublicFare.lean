import YM.Integration.WilsonOriginalTwoFlatGridScaling
import YM.Integration.WilsonReflectedPublicCensusFare

/-! At every cutoff, hear one ordinary product of the pooled and weak
public fields with each original named dose and its own reporting date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicFare
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {D k:ℕ}{r s B:ℝ}{stock:Bank F l D s B}{W:Vane R.family k}{fits:D≤k}
  {I:Type}[Fintype I]{d:I→ℕ}{cap:∀i,d i≤D}{V:∀i,Spin.change S (d i)}
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

def charge {d:ℕ}{cap:d≤D}{U:Spin.change S d}(A:Pair F stock cap W fits U r)
    (j:ℕ)(weak:Bool)(v:S.Field d):ℝ:=
  max 1 (2*(a (station F A weak)/a j)^(d+1)*fee F A weak v)

theorem issued {d:ℕ}{cap:d≤D}{U:Spin.change S d}(A:Pair F stock cap W fits U r)
    (checked:W.checked order H k)(weak:Bool)(v:S.Field d){j N p:ℕ}
    (arrived:station F A weak≤j)(deep:j<N):
    Spindle.paid C d j N p ((A.arm weak v).source (N,p))≤charge F A j weak v:=by
  let Y:=(A.arm weak v).source (N,p)
  have right:=WilsonReflectedPublicCensusFare.original F A checked weak v (p:=p) arrived deep
  have ident:2*(a j^d)⁻¹*quota C d j N p Y=2*Spindle.paid C d j N p Y:=by
    rw [←WilsonMatrixTicketLanesQuota.quota];have h:=((C).S.a_pos j).ne';field_simp
  change max 1 (2*(a j^d)⁻¹*quota C d j N p Y)≤charge F A j weak v at right
  rw [ident] at right
  have en:=le_max_right (1:ℝ) (2*Spindle.paid C d j N p Y)
  have ep:=le_max_left (1:ℝ) (2*Spindle.paid C d j N p Y)
  change Spindle.paid C d j N p Y≤_
  linarith

variable [DecidableEq I][Nonempty I]{lo wid teach}(L:Package R.family wid lo teach)
include L in
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}
    (stop:Stop C 0 J u)(Bgeo q:ℕ):
    ∀ᶠ j:ℕ in atTop,∀{t:ℝ},0<t → t≤a (u+3) → a j<t → t≤(β j)^Bgeo*a j →
    ∀N p:ℕ,∀hN:j<N,∀o:I → Cover,(∀i,8*‖(C).S.gridPoint j (o i)‖≤t) →
    (Pairwise fun i i'=>2*a j*(((P).budget j).B:ℝ)^2 ≤
      ‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
    ∀A:∀i,Pair F stock (cap i) W fits (V i) r,W.checked order H k →
    ∀weak:I→Bool,∀v:∀i,S.Field (d i),(∀i,station F (A i) (weak i)≤j) →∀uj:u≤j,
    let F₀:=word R d j N p hN.le o (fun i=>((A i).arm (weak i) (v i)).source (N,p))
    ‖gap R N p u (uj.trans hN.le) F₀‖≤(∏i,charge F (A i) j (weak i) (v i))*((β j)^q)⁻¹:=by
  filter_upwards [WilsonOriginalTwoFlatGridScaling.original R d L simple slow stop Bgeo q] with j paid
  intro t tp small fine span N p hN o inside apart A checked weak v past uj
  exact paid tp small fine span N p hN o inside apart _ _ (fun i=>lt_of_lt_of_le zero_lt_one (le_max_left ..))
    (fun i=>issued F (A i) checked (weak i) (v i) (past i) hN) uj

end YM.Integration.WilsonOriginalTwoFlatPublicFare
end
