import YM.Integration.WilsonIndependentMatchedFreshCompact
import YM.Integration.WilsonIndependentMatchedPhysicalTail

/-! Coefficientwise prices for the actual finite-chart inverse.  The normalized
input uses the measured Wray inverse.  Forward motion of this submitted
normalized vector uses the native chronological inverse on exactly that
shelf and contains all earlier lower-row feeds. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshInverseIncome
open Function Filter Finset Matrix Lattice RG Wilson Precision Source Labels
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Wheel.Mark PowerSeries
open WilsonPositionProgramTrialReverseLens (received)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonIndependentMatchedFreshGroupFilm (named)
open scoped BigOperators Classical
variable {G:Gauge}{n h D H k u e:ℕ}
local notation "CC" => Credit.leanC

def age (L:Levels G)(z:ℕ → ℝ)(m K:ℕ):ℝ :=
  z m+(L.S.scale K-L.S.scale m)+(K-m:ℕ)

theorem slope (H:Hol G)(Q:SealR G)(e:ℕ):
    ∃A:Credit,∀(f:ChorusLine H Q.ans Q.path e CC CC CC)(m K:ℕ),
    f.arch.V.anchor ≤ m → m ≤ K → ∀(b:Q.Rider)(F:ℝ),0 ≤ F →
    (∀i ≤ e,∀j,‖coeff i (b j)‖ ≤ F) → ∀i ≤ e,∀j,
    ‖coeff i (steep f.arch.V.draws f.arch.V.paid Q.ans Q.path K m (K-m) b j)‖ ≤
      A.buy (age f.arch.V.draws f.arch.V.y m K)*F:=by
  obtain ⟨A,earned⟩:=agesQuote H Q.ans Q.path e CC CC CC
  refine ⟨A,?_⟩
  intro f m K active before b F nn paid i depth j
  let S:CourseS H Q.ans Q.path e CC CC CC:=
    ⟨f,⟨f.arch.V,m,K-m,K,K,K,active,by omega,le_rfl,le_rfl⟩,rfl⟩
  let δ:=max 0 S.cab
  have same:=earned S b b F δ nn (le_max_right ..)
    (fun r hr z=>twain.one _ _ (le_max_left ..) (paid r hr z)) i depth j
  have hs:S.Age=age f.arch.V.draws f.arch.V.y m K:=by
    change _+(f.arch.V.draws.S.scale (m+(K-m))-_) + _=_
    rw [Nat.add_sub_of_le before]
    rfl
  rw [←hs]
  exact same.main

theorem measured (L:Levels G)(O:ChartRatio G)(Q:SealR G)(K m:ℕ)(b:Q.Rider)(q:ℕ)(A B:ℝ)
    (bb:0 ≤ B)(input:∀j,‖coeff q (b j)‖ ≤ A)
    (inv:∀i j,‖(Wray L O Q.ans Q.path K m)⁻¹ i j‖ ≤ B)(i:Alma Q.F):
    ‖coeff q (PermuteLens L O Q K m b i)‖ ≤ (Fintype.card (Alma Q.F):ℝ)*B*A:=by
  classical
  unfold PermuteLens
  simp only [map_sum,map_smul,smul_eq_mul]
  refine (norm_sum_le ..).trans ?_
  calc
    _ ≤ ∑ _j:Alma Q.F,B*A:=by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (inv i j) (input j) (norm_nonneg _) bb
    _ = _:=by simp [mul_assoc]

end YM.Integration.WilsonIndependentMatchedFreshInverseIncome
