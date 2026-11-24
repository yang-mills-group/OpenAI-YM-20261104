import YM.Integration.WilsonIndependentConditionedPivotTailWing
import YM.Integration.WilsonIndependentMovingRosterMarginLedger
import YM.Integration.WilsonIndependentMatchedRosterPowers
import YM.Integration.WilsonSeparatedPrefixMovingUnformedCash

/-! The complete held first-join wage is charged at j+1. Every native child
length and every one-column price is absorbed there before the UV sum. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedPivotTailTwoFees
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingUnformedCash (columns bought)
open WilsonIndependentMatchedRosterPowers (profiles)
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMovingRosterMarginLedger (market local_cost)
open WilsonIndependentMatchedCoverDate (age)
open scoped BigOperators Topology Classical
variable {G:Gauge}{e n:ℕ}{E:Credit}
local notation "I" => Fin ((n+1)+1)

def total (D:Credit)(S:Credit)(E:Credit)(k:ℕ)(c:I→Credit):Credit:=
  (market D S E k).prodC (columns _ c)

theorem original (R:Realm G (e+1) E)(D S:Credit)(C:I→Credit)(h gain k:ℕ)(host m j:ℕ)
    (live:R.anchor ≤ host)(old:host ≤ m)(date:m ≤ j)(f B:I→ℝ)(z gap T:ℝ)(far:ℕ)
    (f0:∀s,0 ≤ f s)(b0:∀s,0 ≤ B s)(z0:0 ≤ z)(g0:0 < gap)(t0:0 ≤ T):
    let Z:=epoch R host (j+1)
    let L:ℝ:=(ll R.draws j).L.val
    let x:=paceT R.draws.S m (j+1)
    let r:=paceT R.draws.S m j
    let A:=fun s=>(C s).buy Z*f s
    let b:=h+gain
    let shape:=fun a:I→ℝ=>profiles (n+1) k e 0 b gap z (∏s,factor 0 b z*(B s*a s))
    (T^far*((D.buy (age R m j)*R.cash S j*L^h)*shape A))*r^gain ≤
      (total D S E b C).buy Z*x^gain*(T^far*shape f):=by
  intro Z L x r A b shape
  have zable:1 ≤ Z:=(window R host j (j+1) live (old.trans date) (Nat.le_succ _)).1
  let term:=fun s=>factor 0 b z*(B s*A s)
  let amt:=fun s=>factor 0 b z*(B s*f s)
  have factor0:0 ≤ factor 0 b z:=by unfold WilsonIndependentMatchedRosterTariff.factor;positivity
  have bundle:=bought (Z:=Z) ((n+1)+1) C term amt (fun s=>by
    refine ⟨mul_nonneg factor0 (mul_nonneg (b0 s) (mul_nonneg (zero_le_one.trans ((C s).purchase zable)) (f0 s))),?_⟩
    change factor 0 b z*(B s*((C s).buy Z*f s)) ≤ (C s).buy Z*(factor 0 b z*(B s*f s)); exact le_of_eq (by ring))
  let plus:=columns ((n+1)+1) C
  have priced:shape A ≤ plus.buy Z*shape f:=by
    let c:ℝ:=(n+1:ℕ)*(coinMat k e+1)^(n+1)*(gap^b)⁻¹*(16*z)^0
    have co:0 ≤ coinMat k e+1:=by linarith only [coinMat_nn k e]
    have cp:0 ≤ c:=by dsimp only [c];positivity
    change c*(∏s,term s) ≤ plus.buy Z*(c*(∏s,amt s))
    exact (mul_le_mul_of_nonneg_left bundle.grant cp).trans_eq (by ring)
  have posf:0 ≤ shape f:=by
    unfold shape profiles
    have co:0 ≤ coinMat k e+1:=by linarith only [coinMat_nn k e]
    have numbers:0 ≤ ∏s,factor 0 b z*(B s*f s):=Finset.prod_nonneg fun s _=>mul_nonneg factor0 (mul_nonneg (b0 s) (f0 s))
    positivity
  let desk:=D.buy (age R m j)*R.cash S j
  have now:R.anchor ≤ m:=live.trans old
  have eligible:1 ≤ WilsonIndependentMatchedCoverDate.age R m j:=by
    unfold WilsonIndependentMatchedCoverDate.age
    linarith only [R.depth m now,scales R.draws.S date,Nat.cast_nonneg (α:=ℝ) (j-m)]
  have dp:0 ≤ desk:=mul_nonneg (zero_le_one.trans (D.purchase eligible))
    (zero_le_one.trans (S.purchase (R.depth j (now.trans date))))
  have lp:0 ≤ L:=by dsimp only [L];exact_mod_cast (ll R.draws j).L.pos.le
  have xp:0 ≤ x:= (pace_pos ..).le
  have raised:desk*L^b ≤ (market D S E b).buy Z:=
    local_cost R D S b host m j (j+1) live old date (Nat.le_succ _)
  have clock:r=x*L:=(pace_step R.draws.S m j).symm
  calc
    _=T^far*x^gain*((desk*L^b)*shape A):=by
      rw [clock,mul_pow];dsimp only [desk,b];rw [pow_add];ring
    _≤T^far*x^gain*((market D S E b).buy Z*(plus.buy Z*shape f)):=mul_le_mul_of_nonneg_left
      (mul_le_mul raised priced (by
        unfold shape profiles
        have co:0 ≤ coinMat k e+1:=by linarith only [coinMat_nn k e]
        have nums:0 ≤ ∏s,factor 0 b z*(B s*A s):=Finset.prod_nonneg fun s _=>mul_nonneg factor0
          (mul_nonneg (b0 s) (mul_nonneg (zero_le_one.trans ((C s).purchase zable)) (f0 s)))
        positivity) (zero_le_one.trans ((market D S E b).purchase zable))) (mul_nonneg (pow_nonneg t0 _) (pow_nonneg xp _))
    _=_:=by dsimp only [total,plus];rw [Credit.products];ring

end YM.Integration.WilsonIndependentConditionedPivotTailTwoFees

