import YM.Integration.WilsonPositionProgramTrialPublicJointGroundRank

/-! The leading three-curvature field is measured on the original dated field,
including its whole accumulated stable and scalar return. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointGroundField
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialFittedLens (ticket)
theorem reported {H:Hol G}(S:SealR G){rails:Rails S.h k u e}{E U V B:Credit}
    (X:CutsP H S.ans S.path rails E U B V)(size:S.h ≤ 6)(i:Alma S.F)
    (lit:2 ≤ valence S.F i)(full:S.h ≤ 2*valence S.F i):
    coeff 0 (home S X i)=coeff 0 (X.tileP i):=by
  rw [WilsonPositionProgramTrialAccrued.tally]
  exact WilsonPositionProgramTrialPublicJointGroundRank.ticketed S X.L.L size X.ha (Nat.le_add_right ..) (X.hc.trans X.hn) X.tileP i lit full

theorem received {H:Hol G}(S:SealR G){rails:Rails S.h k u e}{E U V B:Credit}
    (T:Theatre H S.ans S.path e E U)(simple:G.Simple)(size:S.h ≤ 6)
    (X:CutsP H S.ans S.path rails E U B V)(m K N:ℕ)(late:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)
    (i:Alma S.F)(lit:2 ≤ valence S.F i)(full:S.h ≤ 2*valence S.F i):
    coeff 0 (WilsonPositionProgramTrialReverseLens.received T.V.draws T.V.paid S m K N (home S X) i)=
      coeff 0 (X.tileP i):=by
  rw [←reported S X size i lit full]
  let b:=home S X
  let c:=WilsonPositionProgramTrialReverseLens.received T.V.draws T.V.paid S m K N b
  have same:street T.V.draws T.V.paid S.ans S.path N m (K-m) c=PermuteLens T.V.draws T.V.paid S N m b:=
    Street_up T _ late (by omega)
  have field:=WilsonPositionProgramTrialPublicJointGroundRank.written S T size late before live c i lit full
  rw [same] at field
  have active:sheet S.F i≠0:=by
    intro eq
    have zero:valence S.F i=0:=by rw [valence,eq,S.F.zero_degree]
    omega
  exact field.symm.trans (WilsonPositionProgramTrialPublicJointFourGroundVote.measured S T simple size late
    (before.trans live) b i active)

theorem purchase {H:Hol G}(S:SealR G)(rails:Rails S.h k u e)(E U V B cash:Credit)(size:S.h ≤ 6):
    ∃C:Credit,∀(X:CutsP H S.ans S.path rails E U B V),Weston X.L.L cash →
      ∀(I:Island S.F S.D)(c:Verse S.F),Shimmer I → X.pt=Shrine I c →
      ∀i:Alma S.F,2 ≤ valence S.F i → S.h ≤ 2*valence S.F i →
        ‖coeff 0 (home S X i)-coeff 0 (c i)‖ ≤ C.buy X.Age*X.ρ*X.fuel:=by
  obtain ⟨C,paid⟩:=fan_jet H S.ans S.path rails E U V B cash
  refine ⟨C,?_⟩
  intro X west I c sh source i lit full
  have actual:=paid X west i
  have fixed:=WilsonPhysicalSixWickRows.original X.L.L size (X.hc.trans X.hn)
    (X.ha.trans (Nat.le_add_right X.m X.i)) i lit (fun a=>coeff 0 (X.tileP a))
  change (Wray X.ax X.tx S.ans S.path X.N X.ceilC*ᵥ fun a=>coeff 0 (X.tileP a)) i=coeff 0 (X.tileP i) at fixed
  have read:wickT X.ax X.ceilC X.N k S.F (Shrine I c).2 i=coeff 0 (c i):=by
    rw [WickBase X.ax I sh c rails.hk]
    change ∑j:Alma S.F,wickM X.ax X.ceilC X.N S.F I.2 i j * coeff 0 (c j)=_
    simp_rw [WilsonPhysicalSixWickRows.retained size I sh X.ax X.ceilC X.N i lit]
    simp [Matrix.one_apply,ite_mul]
  rw [fixed,source,read] at actual
  rwa [reported S X size i lit full]

end YM.Integration.WilsonPositionProgramTrialPublicJointGroundField
