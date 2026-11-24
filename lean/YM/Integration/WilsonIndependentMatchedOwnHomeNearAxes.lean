import YM.Integration.WilsonIndependentMatchedOwnHomeAxisWage
import YM.Integration.WilsonIndependentCutJoinNativeFrames
import YM.Integration.WilsonMovingForkSharpExteriorIncome
import YM.Integration.WilsonIndependentSpoutMasterArms

/-! Each unit arm on its true near measurement date carries only its genuine
inverse finite field frame. Its finite angular filtration costs the same
for every allowed truncation of this constant thermal input. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentMatchedOwnHomeNearAxes
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonCoeffUV.Cosmos.Polestar
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonIndependentSpoutMasterCoordinates (axis)
open WilsonIndependentMovingRosterAllFineSeats (Named)
open WilsonIndependentCutJoinNativeFrames (Funded)
open WilsonMarkedIndependentNormalizedElection (normalized)
open XSpace PertExtension WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open scoped BigOperators Classical
local notation "𝒞" => Credit.leanC
variable {G:Gauge}{H:Hol G}{e n height seats:ℕ}
theorem singleton (A:Levels G)(O:ChartRatio G)(Q:SealR G)(m N:ℕ)(a:Alma Q.F)(e:ℕ):
    fee Q e (PermuteLens A O Q N m (axis Q a))=
      ∑j:Alma Q.F,‖(Wray A O Q.ans Q.path N m)⁻¹ j a‖:=by
  let w:Matrix (Alma Q.F) (Alma Q.F) ℝ:=(Wray A O Q.ans Q.path N m)⁻¹
  have one (j:Alma Q.F):PermuteLens A O Q N m (axis Q a) j=w j a • (1:Cost):=by
    simp [PermuteLens,axis,w,Finset.sum_ite_eq',apply_ite]
  unfold fee
  apply Finset.sum_congr rfl
  intro j _
  simp only [one,map_smul,smul_eq_mul,w,PowerSeries.coeff_one]
  simp [Fin.sum_univ_succ]

theorem earned (H:Hol G)(Q:SealR G)(e:ℕ):
    ∃B:Credit,∀(R:Realm G (e+1) 𝒞)(_teacher:AheadT H R 𝒞 𝒞 Q 𝒞)(m N:ℕ),R.anchor ≤ m → m ≤ N →
    ∀(a:Alma Q.F)(j:ℕ),fee Q j (PermuteLens R.draws R.paid Q N m (axis Q a)) ≤
      Fintype.card (Alma Q.F)*B.buy (R.y m):=by
  obtain ⟨B,wick⟩:=belt (H:=H) (C:=𝒞) (T:=Q.ans) (p:=Q.path) (e:=e) (E:=𝒞) (W:=𝒞)
  refine ⟨B,?_⟩
  intro R P m N awake top a j
  rw [singleton]
  calc
    _ ≤ ∑_i:Alma Q.F,B.buy (R.y m):=by
      apply Finset.sum_le_sum;intro i _
      have rule:=(wick P.p.f.arch P.stamps m m N N (P.p.tap.trans_le awake) le_rfl top top i a).main
      simpa only [Realm.cash,P.p.lands,P.p.modes,P.p.depths] using rule
    _=_:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem original (M:Master H)(Q:Fin (n+1)→SealR G)(e:ℕ)(named:∀s,Named M height seats (Q s)):
    ∃pay:Fin (n+1)→Credit,∀(R:Realm G (e+1) 𝒞)(_income:Funded M R height seats)(m N:ℕ),
      R.anchor ≤ m → m ≤ N →∀(a:∀i,Alma (Q i).F)(B:Fin (n+1)→ℝ), (∀i,0 ≤ B i) → ∀q:ℕ,
      let X:=normalized R.draws R.paid Q (WilsonIndependentSpoutMasterArms.basis Q a) m N
      ∏i,B i*fee (Q i) q (X i) ≤
        ∏i,B i*(Fintype.card (Alma (Q i).F)*(pay i).buy (R.y m)):=by
  choose pay granted using (fun i=>earned H (Q i) e)
  refine ⟨pay,?_⟩
  intro R income m N awake top a B positive q X
  apply Finset.prod_le_prod
  · intro i _;exact mul_nonneg (positive i) (WilsonMovingForkSharpExteriorIncome.nonnegative ..)
  · intro i _
    exact mul_le_mul_of_nonneg_left (granted i R (income _ (named i)).some m N awake top (a i) q) (positive i)
end YM.Integration.WilsonIndependentMatchedOwnHomeNearAxes
end
