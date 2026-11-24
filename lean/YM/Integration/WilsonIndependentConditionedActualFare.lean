import YM.Integration.WilsonIndependentConditionedActualWages
import YM.Integration.WilsonIndependentConditionedBankAward

/-! The award's complete finite tariff, with the two external charges and the actual inverse kept explicit. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedActualFare
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open RG.Supply Next.Foundations WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Bank.Mosaic PhysicalNext.Repeat.Legato XSpace.Rose XSpace.Cirrus XSpace
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentConditionedPairProbeSemester (Home)
open WilsonIndependentConditionedPairProbes (Prices)
open WilsonIndependentConditionedPairFiledSemester (Tested)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonIndependentMatchedNamedPair (sectionAt)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D e k u u₀:ℕ}
local notation "J" => Fin 2
local notation "C" => Credit.leanC


open WilsonIndependentConditionedActualBudget (Pay ages)
open WilsonIndependentConditionedActualCredit (badge gramAge)
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedBankShellPrice (wage)
open WilsonIndependentConditionedPairTrialCost (roof)
open WilsonIndependentConditionedBankApplied (field gram)
open WilsonIndependentConditionedGramPrices (profile)
open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedProxyIncome (tariff)
open WilsonIndependentMatchedRosterMasks (Bits choose)
open WilsonIndependentMatchedRosterSlots (degree)
open WilsonInvariantActionPosition (berth)
open Real

open WilsonIndependentConditionedBankAward (fare)
open WilsonIndependentConditionedBankStableCost (gross)
open WilsonIndependentConditionedActualWages (unitWage stripped quote gramWage)

def external (I x y:ℝ):ℝ:=(1+I)*((1+x)*(1+y))*(1+x+y)

private theorem grow (q:ℕ)(U I E F V G x y:ℝ)(u:0 ≤ U)(i:0 ≤ I)(e:0 ≤ E)
    (f:0 ≤ F)(v:0 ≤ V)(vg:V ≤ G)(xx:0 ≤ x)(yy:0 ≤ y):
    gross q (U*(1+x)*(1+y)) I (E*x) (F*y) V ≤ gross q U 1 E F G*external I x y:=by
  let a:=(1+x)*(1+y)
  let b:=1+x+y
  let w:=external I x y
  let n:=((q+1:ℕ):ℝ)
  have n0:0 ≤ n:=Nat.cast_nonneg _
  have a0:0 ≤ a:=mul_nonneg (by linarith) (by linarith)
  have b1:1 ≤ b:=by dsimp [b];linarith only [xx,yy]
  have w0:0 ≤ w:=by dsimp [w,external];positivity
  have ab:a*b ≤ w:=by
    calc
      _ ≤ (1+I)*(a*b):=le_mul_of_one_le_left (mul_nonneg a0 (zero_le_one.trans b1)) (by linarith)
      _ = w:=by dsimp [w,external,a,b];ring
  have aw:a ≤ w:=(le_mul_of_one_le_right a0 b1).trans ab
  have xi:a*I ≤ w:=by
    calc
      _ ≤ a*(1+I):=mul_le_mul_of_nonneg_left (by linarith) a0
      _ ≤ (a*(1+I))*b:=le_mul_of_one_le_right (mul_nonneg a0 (by linarith)) b1
      _ = w:=by dsimp [w,external,a,b];ring
  have ex:a*x ≤ w:=(mul_le_mul_of_nonneg_left (show x≤b by dsimp [b];linarith) a0).trans ab
  have ey:a*y ≤ w:=(mul_le_mul_of_nonneg_left (show y≤b by dsimp [b];linarith) a0).trans ab
  have xy:x*y ≤ w:=(mul_le_mul (show x ≤ 1+x by linarith) (show y ≤ 1+y by linarith)
    yy (by linarith)).trans aw
  have lead:n*(U*(1+x)*(1+y))*I ≤ (n*U*1)*w:=by
    calc
      _ = n*U*(a*I):=by dsimp [a];ring
      _ ≤ n*U*w:=mul_le_mul_of_nonneg_left xi (mul_nonneg n0 u)
      _ = _:=by ring
  have first:2*n*(U*(1+x)*(1+y))*(E*x+F*y) ≤ (2*n*U*(E+F))*w:=by
    calc
      _ = (2*n*U*E)*(a*x)+(2*n*U*F)*(a*y):=by dsimp [a];ring
      _ ≤ (2*n*U*E)*w+(2*n*U*F)*w:=add_le_add
        (mul_le_mul_of_nonneg_left ex (by positivity)) (mul_le_mul_of_nonneg_left ey (by positivity))
      _ = _:=by ring
  have both:3*V*(E*x)*(F*y) ≤ (3*G*E*F)*w:=by
    calc
      _ = (3*V*E*F)*(x*y):=by ring
      _ ≤ (3*G*E*F)*w:=mul_le_mul (by gcongr) xy (mul_nonneg xx yy)
        (by have gg:=v.trans vg;positivity)
  change max _ _ ≤ max (n*U*1) (2*n*U*(E+F)+3*G*E*F)*w
  refine max_le (lead.trans (mul_le_mul_of_nonneg_right (le_max_left ..) w0)) ?_
  have low:2*n*(U*(1+x)*(1+y))*(E*x+F*y)+3*V*(E*x)*(F*y) ≤
      (2*n*U*(E+F)+3*G*E*F)*w:=by simpa only [add_mul] using add_le_add first both
  exact low.trans (mul_le_mul_of_nonneg_right (le_max_right ..) w0)

def material (R:Run G)(Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)(coins:Prices)
    (u b f K q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ):ℝ:=
  let U:=roof (wage (k:=k) (e:=e) R Q coins u b f f K ζ (fun _=>1) (fun _=>1) B t z)
  let F:=fun s=>|field R (Q s) (C₁ s) (C₂ s) f f K q 1 1|
  gross q U 1 (F 0) (F 1) |quote (e:=e) R Q rate f K q B z|

theorem budget (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)(coins:Prices)(u b T q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ):
    Pay R (fun f=>material (k:=k) (e:=e) R Q C₁ C₂ rate coins u b f (berth R T f) q ζ B t z):=by
  let n:=((q+1:ℕ):ℝ)
  have U:=unitWage (k:=k) (e:=e) R simple slow Q coins u b T ζ B t z
  have F (s:J):= (stripped R simple slow (Q s) (C₁ s) (C₂ s) T q).abs
  have V:=(gramWage (e:=e) R simple slow Q rate T q B z).abs
  exact (((Pay.fixed R n).mul U).mul (Pay.fixed R 1)).max
    ((((Pay.fixed R (2*n)).mul U).mul ((F 0).add (F 1))).add
      ((((Pay.fixed R 3).mul V).mul (F 0)).mul (F 1)))

theorem original (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)(coins:Prices)(u b T q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ):
    ∃P:Credit,∀ᶠ f:ℕ in atTop,∀(I:ℝ)(H:J→ℝ),0 ≤ I → (∀s,0 ≤ H s) →
      ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y ≤ z) →
       fare (k:=k) (e:=e) R Q C₁ C₂ rate coins u b f f (berth R T f) q I ζ H B t z φ y ≤
         P.buy (badge R f)*external I (H 0) (H 1):=by
  obtain ⟨P,p⟩:=budget (k:=k) (e:=e) R simple slow Q C₁ C₂ rate coins u b T q ζ B t z
  refine ⟨P,?_⟩
  have hot:=(tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1
  filter_upwards [p,hot] with f bound one I H i hh φ y room
  let K:=berth R T f
  let U:=roof (wage (k:=k) (e:=e) R Q coins u b f f K ζ (fun _=>1) (fun _=>1) B t z)
  let E:=fun s=>|field R (Q s) (C₁ s) (C₂ s) f f K q 1 1|
  let V:=|gram (e:=e) R Q rate f K q φ B y|
  let cap:=|quote (e:=e) R Q rate f K q B z|
  have g0:V ≤ cap:=(WilsonIndependentConditionedActualWages.profiles (e:=e) R Q rate f K q B z φ y room).trans (le_abs_self _)
  have fee:=grow q U I (E 0) (E 1) V cap (H 0) (H 1) (le_max_left ..) i
    (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) g0 (hh 0) (hh 1)
  exact fee.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (bound one))
    (by dsimp [external];have a:=hh 0;have b:=hh 1;positivity))

theorem thermal (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    (Q:J→SealR G)(C₁ C₂:J→Credit)(rate:Credit)(coins:Prices)(u b T q:ℕ)(ζ:ℝ)(B:J→ℝ)(t z:ℝ)
    {ε:ℝ}(ep:0<ε):
    ∀ᶠ f:ℕ in atTop,∀(I:ℝ)(H:J→ℝ),0 ≤ I → (∀s,0 ≤ H s) →
      ∀(φ:(s:J)→Rarity (Q s).D)(y:ℝ),(∀s,radiusH (φ s) 1 y ≤ z) →
       fare (k:=k) (e:=e) R Q C₁ C₂ rate coins u b f f (berth R T f) q I ζ H B t z φ y ≤
         (WilsonOriginalPublicRelativeGramKineticMesh.thermal R f)^(-ε)*external I (H 0) (H 1):=by
  obtain ⟨P,p⟩:=original (k:=k) (e:=e) R simple slow Q C₁ C₂ rate coins u b T q ζ B t z
  filter_upwards [p,WilsonIndependentConditionedActualCredit.subpower R simple P ep] with f bound pay I H i hh φ y room
  exact (bound I H i hh φ y room).trans (mul_le_mul_of_nonneg_right pay
    (by dsimp [external];have a:=hh 0;have b:=hh 1;positivity))

end YM.Integration.WilsonIndependentConditionedActualFare
