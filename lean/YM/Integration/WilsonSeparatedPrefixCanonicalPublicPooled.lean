import YM.Integration.WilsonSeparatedPrefixCanonicalPublicHearing
import YM.Integration.WilsonAddressedPublicGridRoster

/-! The actual heterogeneous physical roster on the selected reporting grid. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalPublicPooled
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ
open WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale WilsonThermometerReflectedTrajectory
open WilsonThermometerOwnOffsetNectar WilsonReflectedPublicOrientedFaces
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open WilsonAddressedAlignedColumn
open WilsonThermometerUnitFilingCoarse WilsonReflectedPublicOrientedFaces
open Extraction Table Spec Trace.Pilot WilsonAddressedPublicPool WilsonAddressedPublicCrown
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S)
    {l : Ultrafilter (ℕ×ℕ)} {D : ℕ} {g : ℝ → ℝ} {U : ℝ}
variable {I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)

theorem original (d:I → Fin (D+1))(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (Γ:Pool R (l:=l) F D g U)(pace:WilsonWindowReportingPace.Slow R.kit)(cater:Cater (C) R.doors)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (A))(wage:WilsonReportLampForecast.Ready (A))
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(window room target:ℕ):
    ∃t≥D+3,∃j₀:ℕ,∀ᶠ r in trail,∀p N (live:Γ.j r<N),
    ∃(V:∀a:Fin (D+1),Sight (C) a.val p)(u:∀a:Fin (D+1),Emblems (C) a.val)
      (view:∀a:Fin (D+1),Opened (C) a.val (Γ.j r) p),
    (∀a,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) (Γ.j r) N p a.val
      (digits R N p 0) (V a) (u a)) ∧
    ∀(v:∀i,S.Field (d i).val)(o:I → Site ((C).side (Γ.j r) p))
      (j:ℕ)(_late:j₀≤j)(_height:j+2≤Γ.j r)(l₀:ℕ)(route:∀t,X → Site ((C).side t p))(anchor:X),
    let k:=Γ.j r
    let P:=(C).path.rep N p k
    let x:=fun i=>Γ.field (d i) r (v i) (N,p)
    let y:=fun i=>offer R (x i) (view (d i)) live.le
    let b:=fun i=>anchorAt R (o i) N
    let W:=fun i=>marked R (N:=N) 0 (1,false) (o i) (V (d i)) (u (d i)) (reduce (y i)) k
    l₀≤room → (C).S.a j/(C).S.a k≤(H k)^window → ((A).params k).supportExponent=100 →
    5≤ P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route k=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j+1≤t → t<k → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l₀) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    (∀i,charge (y i)≤ max 1 (2*(Γ.B r*GapsContact.Ascent.cost F (d i).val (Γ.ρ r) (v i)))) ∧
    ∀e:ℕ,(C).ref 0≤e → ∀ej:e≤j,Opened (C) 0 e p → Opened (C) 0 j p → ∀s:(J₀).Mode,
      ‖reading R (N:=N) (fun T=>P.eval T • actualTransport (C) (N:=N)
          (fun Z=>∏i∈s.val,((charge (y i):ℝ):ℂ)⁻¹*(C).O N p (x i) (b i) Z) live.le T) e (ej.trans (by omega))-
       reading R (N:=N) (fun T=>(P.eval T:ℂ)*∏i∈s.val,(W i).2.1 T) e (ej.trans (by omega))‖≤((H k)^target)⁻¹:=by
  obtain ⟨t,above,plans⟩:=WilsonAddressedPublicGridRoster.original R F simple shop Γ
  obtain ⟨j₀,buyer⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalPublicHearing.original R
    (fun i=>(d i).val) simple shop pace cater bank wage nested window room target t)
  refine ⟨t,above,j₀,?_⟩
  filter_upwards [plans] with r bought p N live
  obtain ⟨V,u,view,entered,plans⟩:=bought p N live
  refine ⟨V,u,view,entered,?_⟩
  intro v o j late age l₀ route anchor k P x y b W housed span fixed size apart course parent housing zero
  have budget:P.p=(A).budget k:=(R.makes.wilson.represents N p k live.le).vac
  have sep(i h:I)(ne:i≠h):((A).budget k).B^2<separation (point R (N:=N) 0 (1,false) (o i) k)
      (point R (N:=N) 0 (1,false) (o h) k):=by
    rw [WilsonReflectedPublicOpticalJoint.location R live.le,WilsonReflectedPublicOpticalJoint.location R live.le,←budget]
    exact Nat.lt_of_succ_le (apart i h ne)
  obtain ⟨chargeBound,filed,source⟩:=plans I d v o J₀ sep
  refine ⟨chargeBound,?_⟩
  intro e he ej oe oj s
  have ink:=buyer j late N p k age live l₀ (fun i=>V (d i)) (fun i=>u (d i)) (fun i=>view (d i))
    (fun i=>entered (d i)) x (fun _=>(1,false)) o route anchor filed housed span fixed size apart course parent housing zero
    e he ej oe oj s
  have refs(i:I)(h:ℕ)(hd:h≤(d i).val):(C).ref h≤N:=
    (view ⟨h,hd.trans_lt (d i).isLt⟩).post.trans live.le
  have oriented:=WilsonReflectedPublicOrientedFaces.original R (fun i=>(d i).val) x (fun i=>V (d i))
    (fun i=>u (d i)) (fun i=>view (d i)) live.le (fun i=>entered (d i)) refs (fun _=>(1,false)) o J₀ t filed k live.le s
  have same:=funext (fun a=>(oriented a).symm.trans (source k live.le s a))
  exact (congrArg (fun a=>‖reading R (N:=N) a e (ej.trans (by omega:j≤k))-
      reading R (N:=N) (fun z=>(P.eval z:ℂ)*∏i∈s.val,(W i).2.1 z) e (ej.trans (by omega:j≤k))‖≤((H k)^target)⁻¹) same).mp ink

end YM.Integration.WilsonSeparatedPrefixCanonicalPublicPooled
