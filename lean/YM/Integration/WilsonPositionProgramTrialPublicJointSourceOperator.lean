import YM.Integration.WilsonPositionProgramTrialPublicJointSourceCampus
/-! Both directions of the actual off-shell change have a uniform bound on the
unscaled top compact coefficients, before the two regulators and all peers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
namespace YM.Integration.WilsonPositionProgramTrialPublicJointSourceOperator
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonPositionProgramTrialPublicJointSourceVote (port)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonPositionProgramTrialPublicJointSourceExchange (change carried undo)
open WilsonIndependentMatchedFreshInverseIncome (age)
open scoped Topology BigOperators Classical
variable {G:Gauge}{n k u e:ℕ}(R:Run G)(W:Initialize G)(d D:Fin (n+1)→ℕ)(fit:∀i,d i<D i)
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC
local notation "port_" s:arg i:arg => port R W d D fit s i

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (pub:prices W R.kit)(i:Fin (n+1))(stock:Rails (d i) k u e)(cap:capP (deck (G:=G) d D fit) ≤ k):
    ∃A:Bool→Alma (R.family.labels.level (d i))→ℝ,(∀s a,0 ≤ A s a) ∧ ∃C:Bool→Credit,
    ∀ᶠ j:ℕ in atTop,∀m K,j ≤ m → m ≤ K → ∀target source (c:Verse (R.family.labels.level (d i))) q,
      q ≤ e → ∀a,‖PowerSeries.coeff q
        (change (port_ target i).ans (port_ source i).ans (fit i) L O m K c a)‖ ≤
        (C target).buy (age L (zz L) m K)*charge e c (A source):=by
  choose A nonneg inputs using fun s:Bool=>
    WilsonIndependentMatchedFiledIncome.named R W s (d i) (fit i) stock.hk e u
  choose C paid using fun s:Bool=>CutsP.stature (hol G) (port_ s i).ans (fit i) stock CC CC CC CC
  refine ⟨A,nonneg,C,?_⟩
  filter_upwards [WilsonPositionProgramTrialPublicJointSourceCampus.original R W d D fit simple v funded pub i stock cap] with j school
  intro m K late before target source c q qq a
  obtain ⟨T,B,ta,to',tz,tj,tb⟩:=school target
  obtain ⟨S,_,sa,so,_,sj,_⟩:=school source
  let P:=Shrine (plate (port_ source i).ans (fit i)) c
  obtain ⟨fits,positive,post⟩:=inputs source c
  have gap:m+(K-m)=K:=Nat.add_sub_of_le before
  have start:T.L.V.anchor ≤ m:=tj ▸ late
  have seed:S.L.V.anchor ≤ m:=sj ▸ late
  let Y:=WilsonIndependentMatchedKernelResidual.diagonal T B tb m (K-m) K start gap.le P fits
    (charge e c (A source)) positive post
  have chart:street L O (port_ target i).ans (fit i) K m (K-m) Y.tileP=
      street L O (port_ source i).ans (fit i) K m (K-m) c:=by
    have selected:=TallOracle T start gap.le P fits
    have other:=carried (port_ source i).ans (fit i) S.L m K seed before stock.hk c
    have named:opal (port_ target i).F (spools L O K k (d i) m (K-m) P)=
        street L O (port_ target i).ans (fit i) K m (K-m) Y.tileP:=by
      change _=street L O _ _ K m (K-m) (tallyV T.L.V.draws T.L.V.paid _ _ K k (m+(K-m)) m P)
      simpa only [ta,to'] using selected
    exact named.symm.trans (by simpa only [sa,so] using other)
  have replay:Y.tileP=change (port_ target i).ans (port_ source i).ans (fit i) L O m K c:=by
    have self:=undo (port_ target i).ans (fit i) T.L m K start before Y.tileP
    unfold change
    rw [← chart]
    simpa only [ta,to'] using self.symm
  have cost:=(paid target Y q qq a).main
  have life:Y.Age=age L (zz L) m K:=by
    change T.L.V.y m+(T.L.V.draws.S.scale (m+(K-m))-T.L.V.draws.S.scale m)+(K-m:ℕ)=_
    rw [tz,ta,gap];rfl
  rw [←replay,←life]
  exact cost

end YM.Integration.WilsonPositionProgramTrialPublicJointSourceOperator
