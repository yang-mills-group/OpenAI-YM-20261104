import YM.Integration.WilsonIndependentConditionedPivotTailSchool
import YM.Integration.WilsonIndependentMovingRosterLaneEdge

/-! The two true single-field inputs purchased at this edge. The source
tariff sees j+1, while every finite conditional retains its original N. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailWing
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (printed)
open WilsonIndependentMatchedCoverProfile (Income charge)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMovingRosterLaneEdge (OnEdge)
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e:ℕ}{E W V:Credit}

def price (H:Hol G)(Q:SealR G)(e b:ℕ)(E W V:Credit):Credit:=
  ((polarBill H Q.ans Q.path e b E W V).choose).prodC (polarBill H Q.ans Q.path e 0 E W V).choose

lemma flat {Y:Era G ℝ}{k:ℕ}{p:ProfileW}{A:ℝ}(cash:Income Y k e 0 p A)(x:ℝ)(nonneg:0 ≤ A):
    Flush e 0 x Y A:=by
  refine ⟨nonneg,fun i hi r _=>?_⟩
  have f:Rent p 0 (Y.2 i r) A:=(cash.2 0 le_rfl i r hi).paid
  have weight:(quoteT p 0 : (Fin r→YForest G)→ℝ)=hedge 0 x 0:=by
    funext a
    simp only [quoteT,hedge,autumn,pow_zero]
  change Award _ (hedge 0 x 0) A
  rw [←weight]
  exact f

theorem original {H:Hol G}(Q:SealR G)(R:Realm G (e+1) E)(sold:PassportC H R Q W V)
    (host home j N b:ℕ)(live:R.anchor ≤ host)(early:host ≤ home)(date:home ≤ j)(fine:j<N)
    (φ:Rarity Q.D)(X:Q.Rider)(B y z:ℝ)(o:CellR)(test:Amplitude φ B)(cap:radiusH φ 1 y ≤ z):
    let Z:=epoch R host (j+1)
    let A:=(price H Q e b E W V).buy Z*fee Q e X
    let δ:=paceT R.draws.S home N
    let x:=paceT R.draws.S home (j+1)
    OnEdge R Q.h 0 b home N j φ y o (printed R Q φ X home N y o) (offer 0 b Q.h 0 z δ x A B):=by
  intro Z A δ x
  let r:=paceT R.draws.S home j
  let C₁:Credit:=(polarBill H Q.ans Q.path e b E W V).choose
  let C₀:Credit:=(polarBill H Q.ans Q.path e 0 E W V).choose
  let P:=printed R Q φ X home N y o
  have here:=live.trans early
  have child:=date.trans (Nat.le_succ _)
  have top:=window R host home (j+1) live early child
  have coarse:=window R host home j live early date
  have grows:epoch R host j ≤ Z:=by
    unfold Z WilsonSeparatedPrefixMovingCalendar.epoch
    linarith only [scales R.draws.S (Nat.le_succ j)]
  have coarseRoom:Compar R.draws.S R.y home j ≤ Z:=coarse.2.2.1.trans grows
  have up:=WilsonSeparatedPrefixMovingOwnDate.column sold home (j+1) N b here child fine Z top.2.2.1 X φ y o (ll R.draws j) B test
  have down:=WilsonSeparatedPrefixMovingOwnDate.column sold home j N 0 here date fine.le Z coarseRoom X φ y o (ll R.draws j) B test
  have x0:0 < x:=pace_pos ..
  have r0:0 < r:=pace_pos ..
  have δ0:0 < δ:=pace_pos ..
  have coeff0:0 ≤ fee Q e X:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have c₁:=C₁.purchase top.1
  have c₀:=C₀.purchase top.1
  have u₁:C₁.buy Z*fee Q e X ≤ A:=by
    dsimp only [A,price];rw [Credit.products]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (zero_le_one.trans c₁) c₀) coeff0
  have u₀:C₀.buy Z*fee Q e X ≤ A:=by
    dsimp only [A,price];rw [Credit.products]
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (zero_le_one.trans c₀) c₁) coeff0
  have A0:0 ≤ A:=(mul_nonneg (zero_le_one.trans c₀) coeff0).trans u₀
  have xcap:=WilsonIndependentMatchedRosterDate.radius φ x0 (pace_le _ child) cap
  have rcap:=WilsonIndependentMatchedRosterDate.radius φ r0 (pace_le _ date) cap
  have xr:x ≤ r:=div_le_div_of_nonneg_right (R.draws.S.strictAnti.antitone (Nat.le_succ _)) (R.draws.S.a_pos home).le
  have upPay:=WilsonIndependentMatchedRosterTariff.incoming φ 0 b Q.h 0 δ x y z A B x0 δ0 A0 test.1 xcap
  have downPay:=WilsonIndependentMatchedRosterTariff.outgoing φ 0 b Q.h 0 δ x r y z A B x0 xr δ0 A0 test.1 rcap
  simp only [Nat.zero_add,Nat.cast_zero,zero_div,Real.rpow_zero,mul_one] at upPay downPay
  have monotone (u:ℕ)(η:ℝ)(hp:0 < η){a:ℝ}(bound:a ≤ A):
      charge φ u Q.h η y a B ≤ charge φ u Q.h η y A B:=by
    unfold WilsonIndependentMatchedCoverProfile.charge BasePrice
    have hr:0 ≤ radiusH φ η y:=zero_le_one.trans (fieldCap ..)
    gcongr
    exact test.1
  have priceUp:charge φ b Q.h x y (C₁.buy Z*fee Q e X) B ≤ offer 0 b Q.h 0 z δ x A B:=
    (monotone b x x0 u₁).trans upPay
  have priceDown:charge φ 0 Q.h r y (C₀.buy Z*fee Q e X) B ≤ offer 0 b Q.h 0 z δ x A B:=by
    apply (monotone 0 r r0 u₀).trans
    simpa only [WilsonIndependentMatchedCoverProfile.charge,WilsonIndependentMatchedRosterLane.chargeBelow,pow_zero,one_mul] using downPay
  have restored:verseI R.draws R.paid j N Q.h (P (j+1-home))=P (j-home):=by
    dsimp only [P,printed]
    rw [Nat.add_sub_of_le child,Nat.add_sub_of_le date]
    exact passportCarry sold φ X o here date fine
  have upForm:P (j+1-home)=locale o (Q.spins R.draws R.paid φ home (j+1) N y X):=by
    dsimp only [P,printed];rw [Nat.add_sub_of_le child]
  have oldForm:P (j-home)=locale o (Q.spins R.draws R.paid φ home j N y X):=by
    dsimp only [P,printed];rw [Nat.add_sub_of_le date]
  have pos:0 ≤ offer 0 b Q.h 0 z δ x A B:=WilsonIndependentMatchedRosterTariff.positive _ _ _ _
    ((zero_le_one.trans (fieldCap ..)).trans cap) δ0.le x0.le A0 test.1
  change OnEdge R Q.h 0 b home N j φ y o P _
  refine ⟨upForm ▸ up.1,?_,restored,?_,?_⟩
  · rw [upForm]
    simp only [Nat.zero_add]
    exact ⟨up.1,fun a ha i r hi=>(up.2 a ha i r hi).stepX priceUp ha⟩
  · rw [restored,oldForm]
    have saved:Income _ Q.h e 0 (OrbP (ll R.draws j) φ r y o) (offer 0 b Q.h 0 z δ x A B):=
      ⟨down.1,fun a ha i r hi=>(down.2 a ha i r hi).stepX priceDown ha⟩
    exact flat saved r pos
  · intro absent
    rw [upForm]
    exact WilsonIndependentMatchedVacant.absent _ φ x y o Q.h x0 absent

end YM.Integration.WilsonIndependentConditionedPivotTailWing

