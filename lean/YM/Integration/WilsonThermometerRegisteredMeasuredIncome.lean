import YM.Integration.WilsonThermometerRegisteredHistoryMass
import YM.Integration.WilsonThermometerFiniteConnectedCells
import YM.Integration.WilsonPositionThermometerJointFaces

/-! Each proper or full face of the measured ordinary ratio is the integral of
the same face on the original received Wilson table. The unit comes from the
elected station, at every child residue before any physical limit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredMeasuredIncome
open Filter Finset MeasureTheory Table Spec Lattice Wilson RG Source Marker Extraction Climb Trace.Pilot
open Next.UVStress Next.Rank RG12 RG17 PhysMS PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent MergeProof.East
open FVA1 OriginalForcedAddresses XSpace XSpace.Normalize XSpace.Rose Cells Push.GridApprox OPE.Therm
open WilsonPositionThermometerGradedReading WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonThermometerCenteredAlgebra WilsonThermometerFiniteConnectedCells
open Primitives.GCC.Anchor
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6) (simple:G.Simple)
local notation "J" => Stock.census (Fin 3)
local notation "places" z:max => Fin 3→Site (R.family.side (z:UVIndex).1 z.2)
local notation "ν" z:max i:max => OPE.Therm.scene R.family.path (z:UVIndex).1 z.2 i
local notation "source₀" z:max o:max s:max => WilsonThermometerCourseHot.bare R A (placement R z o) s
local notation "F₀" age:max z:max o:max => WilsonThermometerCourseResidual.table R A simple age (placement R z o)

theorem original {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀ j,A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j):
    ∀ᶠ z:UVIndex in f.fuse, ∀ i(age:i≤z.1)(o:places z)(Q:Poly J)(s:(J).Mode),
    let F:=F₀ age z o
    Integrable (fun U=>(total (F U) Q).part s) (ν z i) ∧
    (total (measured R A z o) Q).part s = ∫U,(total (F U) Q).part s ∂ν z i:=by
  have date:=eventually_all.mpr (fun v:Fin 3=>large_mesh f (R.family.ref (index A (grade v))))
  filter_upwards [date,WilsonPositionThermometerJointFaces.same A checked unit] with z refs placed
  intro i age o Q s F
  have weighted (a:(J).Mode):Integrable (fun U=>(R.family.path.rep z.1 z.2 z.1).eval U • (source₀ z o a) U) (prior G _):=by
    have smooth:=WilsonThermometerLiteralCredit.continuous_face R A (placement R z o) a
    simpa only [Complex.real_smul] using (RG05Readout.Harvest.dye_grow («C»:=R.family) (N:=z.1) (p:=z.2) R.makes smooth)
  have value (a:(J).Mode): (fun U=>(F U).part a)=actualTransport R.family (N:=z.1) (source₀ z o a) age:=
    funext (fun U=>WilsonThermometerCourseResidual.observed R A simple age (placement R z o) refs U a)
  have cost (a:(J).Mode):Integrable (fun U=>(F U).part a) (ν z i):=by
    rw [value]
    exact actualScene_integrable_of_weighted R.family R.makes age
      (actualTransport_weighted_integrable_of_integrable R.family R.makes le_rfl (weighted a) age)
  have lawEq:ν z z.1=law G (R.family.side z.1 z.2) (R.family.beta z.1 z.2):=by
    have authentic:R.family.Makes:=R.makes
    unfold OPE.Therm.scene law dose Wilson.weight
    rw [(authentic.wilson.starts z.1 z.2).2]
  have average (a:(J).Mode): (measured R A z o).part a=∫U,(F U).part a ∂ν z i:=by
    change row A z o a.val=∫ U,(fun V=>(F V).part a) U ∂ν z i
    rw [value,actualScene_transport R.family R.makes le_rfl (weighted a) age,lawEq,
      WilsonPositionThermometerJointFaces.ensemble]
    exact congrArg (R.family.omega z.1 z.2) (placed (placement R z o) a.val)
  let term (a b:(J).Mode)(U:Config G (R.family.side i z.2)):ℂ:=if Poly.merges a b s then (F U).part a*(inverseMass Q).part b else 0
  have ok (a b:(J).Mode):Integrable (term a b) (ν z i):=by
    by_cases linked:Poly.merges a b s
    · simpa only [term,if_pos linked] using (cost a).mul_const ((inverseMass Q).part b)
    · simp only [term,if_neg linked]
      haveI:IsProbabilityMeasure (ν z i):=OPE.Therm.probability (H:=R.family.path) (p:=z.2) R.makes.wilson age
      exact integrable_const (0:ℂ)
  have face (U): (total (F U) Q).part s= ∑a:(J).Mode,∑b:(J).Mode,term a b U:=Poly.part_mul ..
  simp_rw [face]
  refine ⟨integrable_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>ok a b)),?_⟩
  rw [integral_finsetSum _ (fun a _=>integrable_finsetSum _ (fun b _=>ok a b)),total,Poly.part_mul]
  apply sum_congr rfl;intro a _
  rw [integral_finsetSum _ (fun b _=>ok a b)]
  apply sum_congr rfl;intro b _
  by_cases joined:Poly.merges a b s
  · simp only [term,if_pos joined,integral_mul_const,average a]
  · simp only [term,if_neg joined,integral_zero]

end YM.Integration.WilsonThermometerRegisteredMeasuredIncome
