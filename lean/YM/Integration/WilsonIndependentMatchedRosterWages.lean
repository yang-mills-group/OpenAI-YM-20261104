import YM.Integration.WilsonIndependentMatchedRosterPool

/-! The physical comparable-geometry roster loses only arbitrarily small
mesh powers on the actual independent basis and through its final read. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedRosterWages
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoverProfile
open scoped BigOperators Topology Classical

open WilsonIndependentMatchedCoverProfile
open WilsonIndependentMatchedRosterLane (Lane)
open WilsonIndependentMatchedRosterChronology (mass born)
open WilsonIndependentMatchedRosterTariff (offer)
open WilsonIndependentMatchedRosterPowers (profiles)
variable {G:Gauge}{h D k e u₀ n:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u₀ e}{E W K U:Credit}{dim:Fin (n+1)→ℕ}

open WilsonIndependentEvenPassport (old count)
open WilsonIndependentMatchedRosterReception (bill)

open WilsonIndependentMatchedRosterStop (Hearing)
open WilsonIndependentMatchedRosterSlots (degree entry wallet)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentMatchedCutBudget (restored)
open WilsonIndependentEvenPassport (young)

open WilsonIndependentMatchedRosterReception (perSite)
open WilsonIndependentMatchedRosterTariff (factor)
open WilsonIndependentMatchedRosterPowers (profiles)

def geo (n e u b:ℕ)(l:Fin (n+1)→ℕ)(t z:ℝ):ℝ:=
  (coinMat (∑s,l s) e)^n+2*profiles n b e u b t z 1

/-- The rooted salaries of positive basis directions and residuals cost
at most the same arbitrarily small mesh power per position. The stop and
first-join sums cost two additional copies, regardless of angular rank. -/
theorem combined (l:Fin (n+1)→ℕ)(e u b m:ℕ)(δ η t z:ℝ)(A M B:Fin (n+1)→ℝ)
    (positive:0<δ)(unit:δ ≤ 1)(exp:0 ≤ η)(ht:0<t)(hz:0 ≤ z)
    (money:∀s,0 ≤ M s)(wages:∀s,0 ≤ A s)(weights:∀s,0 ≤ B s)(pay:∀s,A s ≤ δ^(-η)*M s):
    δ^(-η)*(bill b e u b l δ η t z A B*δ^((m:ℝ)/4)) ≤ 
      geo n e u b l t z*perSite u b z M B*δ^((m:ℝ)/4-((n+3:ℕ):ℝ)*η):=by
  let x:=δ^(-η)
  let W:=perSite u b z M B
  let Z:=perSite u b z A B
  let C:=profiles n b e u b t z 1
  let K:=(coinMat (∑ s,l s) e)^n
  have x₁:1 ≤ x:=Real.one_le_rpow_of_pos_of_le_one_of_nonpos positive unit (neg_nonpos.mpr exp)
  have x₀:0 ≤ x:=zero_le_one.trans x₁
  have f₀:0 ≤ factor u b z:=by unfold WilsonIndependentMatchedRosterTariff.factor;positivity
  have w₀:0 ≤ W:=Finset.prod_nonneg (fun s _=>mul_nonneg f₀ (mul_nonneg (weights s) (money s)))
  have kc:0 ≤ K:=pow_nonneg (coinMat_nn _ _) n
  have cc:0 ≤ C:=by have :=coinMat_nn b e;unfold C profiles;positivity
  have first:Z ≤ x^(n+1)*W:=by
    calc
      Z ≤ ∏s:Fin (n+1),x*(factor u b z*(B s*M s)):=by
        apply Finset.prod_le_prod
        · intro s _;exact mul_nonneg f₀ (mul_nonneg (weights s) (wages s))
        · intro s _
          calc _ ≤  factor u b z*(B s*(x*M s)):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pay s) (weights s)) f₀
               _ = _ :=by ring
      _=x^(n+1)*W:=by rw [Finset.prod_mul_distrib];simp [W,perSite]
  have pref:K+2*x*C ≤ x*(K+2*C):=by nlinarith [mul_nonneg (sub_nonneg.mpr x₁) kc]
  have fee: x*(K+2*x*C)*Z ≤ x^(n+3)*(K+2*C)*W:=by
    calc
      _ ≤  x*(K+2*x*C)*(x^(n+1)*W):=mul_le_mul_of_nonneg_left first (by positivity)
      _ ≤  x*(x*(K+2*C))*(x^(n+1)*W):=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left pref x₀) (by positivity)
      _=x^(n+3)*(K+2*C)*W:=by rw [show n+3=n+1+2 by omega,pow_add];ring
  have powers:x^(n+3)*δ^((m:ℝ)/4)=δ^((m:ℝ)/4-((n+3:ℕ):ℝ)*η):=by
    have turn: x^(n+3)=δ^((-η)*((n+3:ℕ):ℝ)):=by rw [Real.rpow_mul positive.le,Real.rpow_natCast]
    rw [turn,←Real.rpow_add positive];congr 1;ring
  have cp:profiles n b e u b t z Z=C*Z:=by simp only [C,profiles,mul_one]
  change x*((K*Z+2*(x*profiles n b e u b t z Z))*δ^((m:ℝ)/4)) ≤ (K+2*C)*W*_
  rw [cp,←powers]
  calc
    _=(x*(K+2*x*C)*Z)*δ^((m:ℝ)/4):=by ring
    _ ≤ _ :=le_trans (mul_le_mul_of_nonneg_right fee (Real.rpow_nonneg positive.le _)) (by apply le_of_eq;ring)

end YM.Integration.WilsonIndependentMatchedRosterWages
