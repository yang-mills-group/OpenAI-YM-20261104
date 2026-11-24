import YM.Integration.WilsonPositionProgramTrialPublicJointCapGroundFare

/-! The measured zeroth coefficient on any retained positive angular row uses only
its own angular rank. At maximal curvature rank every contributing address has full
engineering weight, giving a fixed ground row on both registered clocks. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundRank
open WilsonCoeffUV WilsonCoeffUV.RootLaw
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Supply Ticket Polestar Shard Plan Mer
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

open scoped BigOperators Matrix
variable {G:Gauge}{H:Hol G}{E U:Credit}{e:ℕ}
theorem same (Q:SealR G)(T:Theatre H Q.ans Q.path e E U)(cap:Q.h ≤ 6)
    {m K N:ℕ}(start:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
    (i j:Alma Q.F)(lit:2 ≤ valence Q.F i):
    let A:=T.V.draws
    let O:=T.V.paid
    lineS (CurNames A O Q.ans Q.path N m (K-m) false) 0 i j=
      identum (forwardW A O Q.ans Q.path N m (K-m)) i j:=by
  classical
  intro A O
  let B:=lineS (CurNames A O Q.ans Q.path N m (K-m) false) 0
  let F:=identum (forwardW A O Q.ans Q.path N m (K-m))
  let W t:=Wray A O Q.ans Q.path N t
  have mat:W m*B=F*W K:=WilsonPositionProgramTrialFittedTable.ground H Q T start before live
  have rank (x:Alma Q.F→ℝ):(F*ᵥ(W K*ᵥx)) i=(F*ᵥx) i:=by
    refine Finset.sum_congr rfl ?_
    intro l _
    change F i l*(W K*ᵥx) l=F i l*x l
    by_cases equal:valence Q.F i=valence Q.F l
    · rw [show (W K*ᵥx) l=x l from WilsonPhysicalSixWickRows.original T cap live (start.trans before) l (by omega) x]
    · have z:F i l=0:=by simp [F,identum,equal]
      rw [z,zero_mul,zero_mul]
  let x:Alma Q.F→ℝ:=Pi.single j 1
  have keep: (B*ᵥx) i=(F*ᵥx) i:=calc
    _=(W m*ᵥ(B*ᵥx)) i:=(WilsonPhysicalSixWickRows.original T cap (before.trans live) start i lit _).symm
    _=(F*ᵥ(W K*ᵥx)) i:=by simp only [Matrix.mulVec_mulVec,mat]
    _=_:=rank x
  simpa [x,Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite] using keep

theorem atTop (Q:SealR G)(T:Theatre H Q.ans Q.path e E U)(cap:Q.h ≤ 6)
    {m K N:ℕ}(start:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
    (i j:Alma Q.F)(lit:2 ≤ valence Q.F i)(full:Q.h ≤ 2*valence Q.F i):
    lineS (CurNames T.V.draws T.V.paid Q.ans Q.path N m (K-m) false) 0 i j=(1:Wall Q.F) i j:=by
  rw [same Q T cap start before live i j lit]
  by_cases equal:valence Q.F i=valence Q.F j
  · have ar:=WilsonPhysicalSixWickRows.arity Q.F j
    have cut:=weigh_cap Q.F j
    have included:weave Q.F j ≤ weight Q.F j:=Nat.le_add_right .. 
    have top:Q.h=weight Q.F j:=by omega
    exact (wallways T start (show m+(K-m) ≤ N by omega)).2.2.2 i j top
  · have diff:i≠j:=fun e=>equal (e▸rfl)
    simp [identum,equal,Matrix.one_apply_ne diff]

theorem written (Q:SealR G)(T:Theatre H Q.ans Q.path e E U)(cap:Q.h ≤ 6)
    {m K N:ℕ}(start:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
    (c:Verse Q.F)(i:Alma Q.F)(lit:2 ≤ valence Q.F i)(full:Q.h ≤ 2*valence Q.F i):
    coeff 0 (street T.V.draws T.V.paid Q.ans Q.path N m (K-m) c i)=coeff 0 (c i):=by
  rw [WilsonPositionProgramTrialPublicJointFourClock.filed]
  let Z:=lineS (CurNames T.V.draws T.V.paid Q.ans Q.path N m (K-m) false) 0
  have row:Z i=(1:Wall Q.F) i:=funext fun j=>atTop Q T cap start before live i j lit full
  change dotProduct (Z i) (fun j=>coeff 0 (c j))=_
  rw [row]
  exact congrFun (Matrix.one_mulVec (fun j=>coeff 0 (c j))) i

open WilsonPositionProgramTrialFittedLens (ticket matrix)
theorem ticketed (Q:SealR G)(T:Theatre H Q.ans Q.path e E U)(cap:Q.h ≤ 6)
    {m K N:ℕ}(start:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
    (c:Verse Q.F)(i:Alma Q.F)(lit:2 ≤ valence Q.F i)(full:Q.h ≤ 2*valence Q.F i):
    coeff 0 (ticket T.V.draws T.V.paid Q N m K c i)=coeff 0 (c i):=by
  let a:=street T.V.draws T.V.paid Q.ans Q.path N m (K-m) c
  have head (M:Wall Q.F):coeff 0 (matrix M a i)=(M*ᵥfun j=>coeff 0 (a j)) i:=by
    simp [matrix,Matrix.mulVec,dotProduct]
  change coeff 0 (matrix _ a i)=_
  rw [head,WilsonPhysicalSixWickRows.original T cap (before.trans live) start i lit]
  exact written Q T cap start before live c i lit full

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundRank
