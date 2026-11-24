import YM.Integration.WilsonPhysicalStationPureReceipt
import YM.Integration.WilsonPhysicalStationBasisOwners

/-! The corrected vote meets one Maxwell test at the actual rear ruler and the measured thermal transit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationPureBorn
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open Further.CorrectedLift Next.Rank Next.Rank.Station
open WilsonPhysicalStationFullVote (Head Below)
open WilsonPhysicalStationPureReceipt (ballot coefficients signed left)
open WilsonPhysicalStationBasisOwners (Earned)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationKineticLimit (transit)
open scoped Topology Classical BigOperators Matrix

variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}{H:(Bel R.family.book).Hierarchy}
    {ℓ:Ultrafilter (ℕ×ℕ)}(J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
    {m k h:ℕ}(hm:h ≤ m)(hk:h ≤ k)(ca:(V m).checked f H m)(cb:(V k).checked f H k)(q:ℕ)
set_option quotPrecheck false
local notation "axes" => (R.family.labels.level h).Index
local notation "C₀" => standard R.family
local notation "A₀" => V m
local notation "B₀" => V k
local notation "rails" => R.family.path.levels

theorem assembled (u:(C₀).Field h):
    (∑i:Head R.family h,coefficients R J₀ J V (k:=k) q u i • WilsonPhysicalVaneBasis.field R.family h i.val)=
      ballot R J₀ J V (k:=k) q u:=by
  let y:=ballot R J₀ J V (k:=k) q u
  let atoms:=(fun i:axes=>ladder R.family h y i • WilsonPhysicalVaneBasis.field R.family h i)
  have whole:=WilsonPhysicalVaneBasis.resolve R.family h y
  have partition:=Fintype.sum_subtype_add_sum_subtype (fun i:axes=>((R.family.labels.level h).grades i).1=h) atoms
  have earlier:(∑i:Below R.family h,atoms i.val)=0:=by
    apply Finset.sum_eq_zero
    intro i _
    have off:¬(R.family.labels.level h).grades i.val=(h,q):=fun eq=>i.property (congrArg Prod.fst eq)
    have absent:ladder R.family h y i.val=0:=WilsonPhysicalStationGradedVoter.outside R.family h _ _ i.val off
    simp only [atoms,absent,zero_smul]
  have all:=partition.trans whole
  rw [earlier,add_zero] at all
  exact all

theorem matrix (u z:(C₀).Field h)(ξ:Points 2):
    (∑i:Head R.family h,coefficients R J₀ J V (k:=k) q u i*born R h ξ z i.val)=
      (C₀).classMoment (C₀) (fun _:Fin 2=>h) ξ ![ballot R J₀ J V (k:=k) q u,z]:=by
  let M:=(C₀).classMoment (C₀) (fun _:Fin 2=>h) ξ
  let L:(C₀).Field h→ₗ[ℂ]ℂ:=M.toLinearMap ![0,z] 0
  have applied (y:(C₀).Field h):L y=M ![y,z]:=by
    change M (Function.update ![0,z] 0 y)=M ![y,z]
    exact congrArg _ (funext fun i=>by fin_cases i <;>simp [Function.update])
  change _=M ![_,z]
  rw [←applied,←assembled R J₀ J V (k:=k) q u,map_sum]
  simp only [map_smul,smul_eq_mul]
  simp only [applied]
  rfl

theorem thermal {g:ℝ}(receipt:Tendsto (transit R (A₀).k (B₀).k) (ℓ:Filter _) (𝓝 g)):
    Tendsto (fun p:ℕ×ℕ=>signal R p.1 p.2 (A₀).k (B₀).k h q
      (mag (rails) (A₀).b (A₀).k) (mag (rails) (B₀).b (B₀).k)) (ℓ:Filter _)
      (𝓝 (((B₀).wheel.r/(A₀).wheel.r)^h*g^q)):=by
  exact tendsto_const_nhds.mul (receipt.pow q)

end YM.Integration.WilsonPhysicalStationPureBorn
end
