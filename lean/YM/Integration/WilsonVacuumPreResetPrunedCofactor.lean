import YM.Integration.WilsonVacuumPreResetPrunedIntake
import YM.Integration.WilsonRootedPhysicalCashCover

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetPrunedCofactor
open Function Filter Finset Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open scoped Topology BigOperators Classical

variable {G:Gauge}(R:Run G){m N per:ℕ}
set_option quotPrecheck false
local notation "a" => R.alloy.B.a
local notation "B" => (a).budget m
local notation "jj" => (a).clock.J
local notation "γ" => R.alloy.B.kin.alpha N m
local notation "β" => (R.family.path.rep N per (m+1)).beta

theorem original (hm:m<N)(U:RG.Rep G (R.family.side (m+1) per))
    (allowed:Routed.EquivalentParameters (A:=R.alloy) N m per U)
    (exactβ:U.beta=β)(same:U.eval=(R.family.path.rep N per (m+1)).eval):
    ∃H:Opera.Guide R.alloy.B R.kit.shape N m per U,Opera.Price R.alloy.B R.kit.shape N m per U H ∧
      let M:=Match.staple (H:=H) (J:=H) rfl rfl rfl
      (∀O W,(R.family.path.rep N per m).eval W=earlyValue (ledger R.kit H) (R.alloy.B.kin.path N m)
        ((a).params m).clip B (vacuum R.kit H H M) β (Song.weighty H Chi.canonical O) γ W) ∧
      ∃pay:H.fragrances→ℝ,∀(E:Set ℕ)(r:ℕ),
        (∀z:H.fragrances,Pruned.chosen H M E r (.inl z)→
          let g:=Pruned.regLow H Chi.canonical M E r γ (.inl z)
          let b:=Song.locate H z
          (∀V,masked (B).threshold b.support g V = -H.trainedPool Chi.canonical V (M.furrow z)) ∧
          (∀V,Healthy (B).threshold b.support V → g V = -H.trainedPool Chi.canonical V (M.furrow z)) ∧
          (B).Regular b.support g ∧ (B).supBounds b.site b.support g (pay z)) ∧
        (∀u:Songbook (R.family.side m per),Pruned.chosen H M E r (.inr u)→
          Pruned.regLow H Chi.canonical M E r γ (.inr u)=
            sounding (R.alloy.B.kin.path N m) ((a).params m).clip β γ u):=by
  obtain ⟨H,price,read⟩:=WilsonVacuumPreResetPrunedIntake.physical R hm U allowed exactβ same
  let M:=Match.staple (H:=H) (J:=H) rfl rfl rfl
  let j:=jj (m+1)
  let c:=jj m
  let K:=R.metals.p.profile c
  have actual:=step_paid R.alloy.B.a m
  have heights:=R.kit.pledging.jewels j ((a).clock.hatBeta m) (R.alloy.B.valid.pays m) c actual
  let T:=ships R.alloy.B N m per
  obtain ⟨Y',d',v,t',Av,b',r',B',q',i',z',⟨cap,_⟩,_,_⟩:=
    heights.2 _ _ _ T H.laws.data.funds (protocol R.alloy.B hm R.kit.pledging.conducts.full) _ H
  have hr:(a).params m=K:=params_eq R.alloy.B.valid m
  have hp:(B).power=K.power:=congrArg RG.Stage.power hr
  have hj:(B).order=K.order:=congrArg RG.Stage.order hr
  refine ⟨H,price,read,fun z=>cap.markΦ (M.furrow z) K.power,?_⟩
  intro E r
  constructor
  · intro z chosen
    have identity:=Song.valueDue B H M Chi.canonical cap rfl hj.le z
    have pocket:=Song.pocketScore B H M Chi.canonical cap rfl hj.le K.power hp.le z
    simp only [Pruned.regLow,chosen,↓reduceIte,Song.opus,Sum.elim_inl]
    refine ⟨identity,?_,pocket⟩
    intro V live
    simpa only [masked_eq _ _ _ V live] using identity V
  · intro u chosen
    simp only [Pruned.regLow,chosen,↓reduceIte,Song.opus,Sum.elim_inr]
    rw [exactβ]
    rfl

end YM.Integration.WilsonVacuumPreResetPrunedCofactor
