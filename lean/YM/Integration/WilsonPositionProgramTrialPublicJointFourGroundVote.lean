import YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundRows
import YM.Integration.WilsonPositionProgramTrialPublicJointFourClock

/-! The full coefficient-zero input on each nonunit row of the earned upper field. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundVote
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

open scoped BigOperators Matrix
variable {G:Gauge}{H:Hol G}{E U:Credit}{e:ℕ}
theorem written (Q:SealR G)(L:Theatre H Q.ans Q.path e E U)(simple:G.Simple)(cap:Q.h=4)
    {m K N:ℕ}(start:L.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
    (c:Verse Q.F)(i:Alma Q.F)(active:sheet Q.F i≠0):
    coeff 0 (street L.V.draws L.V.paid Q.ans Q.path N m (K-m) c i)=coeff 0 (c i):=by
  classical
  obtain ⟨h,F,D,T,p⟩:=Q
  change h=4 at cap
  subst h
  rw [WilsonPositionProgramTrialPublicJointFourClock.filed]
  let Z:=lineS (CurNames L.V.draws L.V.paid T p N m (K-m) false) 0
  have row:Z i=(1:Wall F) i:=funext fun j=>
    WilsonPositionProgramTrialPublicJointFourGroundRows.original L simple start before live i j active
  change dotProduct (Z i) (fun j=>coeff 0 (c j))=_
  rw [row]
  exact congrFun (Matrix.one_mulVec (fun j=>coeff 0 (c j))) i

theorem measured (Q:SealR G)(L:Theatre H Q.ans Q.path e E U)(simple:G.Simple)(cap:Q.h≤6)
    {m N:ℕ}(start:L.V.anchor ≤ m)(live:m ≤ N)(b:Verse Q.F)
    (i:Alma Q.F)(active:sheet Q.F i≠0):
    coeff 0 (PermuteLens L.V.draws L.V.paid Q N m b i)=coeff 0 (b i):=by
  classical
  rw [WilsonPositionProgramTrialPublicJointFourClock.measured]
  let Z:=Wray L.V.draws L.V.paid Q.ans Q.path N m
  let x:Alma Q.F→ℝ:=fun j=>coeff 0 (b j)
  have unit:IsUnit Z.det:=wick_unit _ (production L live start).1 _ _
  have eq:Z*ᵥ(Z⁻¹*ᵥx)=x:=by rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ unit,Matrix.one_mulVec]
  exact (WilsonPhysicalSixWickRows.nonunit L cap simple live start i active (Z⁻¹*ᵥx)).symm.trans (congrFun eq i)
end YM.Integration.WilsonPositionProgramTrialPublicJointFourGroundVote
