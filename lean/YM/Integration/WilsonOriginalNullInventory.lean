import YM.Integration.WilsonOriginalNullFamily
import YM.Integration.WilsonMeasuredNullAccounts
import YM.Integration.WilsonMeasuredCoefficientTransport

/-! Split a stored field on one actual vacuum into its original masked
regulars, its full co-owned hard numerator and its measured primary.
The three pieces sum on every group configuration before the original push. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalNullInventory
open Function Filter Lattice Wilson RG Source Labels MeasureTheory Extra.Histories Next.Foundations
open WilsonMeasuredCoefficientTransport
open scoped Classical Topology BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}

def cold (o : Site n) (P : Coefficient F n) : Coefficient F n :=
  { primary (F:=F) o 0 with forced := P.forced }

theorem format (R : Rep G n) (A : Hol G) (o : Site n) (P : Coefficient F n) (live : P.Format o A R) :
    (cold o P).Format o A R := by
  have zero := primary_format (R:=R) (o:=o) (H:=A) (0:F.Coeff)
  exact ⟨zero.smooth,zero.origin,zero.identity_null,zero.projects,
    live.forcing,live.carried,live.invariant,live.supported,live.borel⟩

theorem split (R : Rep G n) (B : SectionData F) (o : Site n) (P : Coefficient F n) (U : Config G n) :
      P.density o B R U = (R.eval U:ℂ)*(∑' j,P.maskedTerm R j U) +
        (primary o P.x).density o B R U + account (cold o P) R U := by
  rw [primary_density]
  change (R.eval U:ℂ)*(part B o R U P.x + ∑' j,P.maskedTerm R j U)+account P R U=_
  have hard : account (cold o P) R U = account P R U := rfl
  rw [hard]
  ring

theorem original (R : Rep G n) (A : Hol G) (o : Site n) (P : Coefficient F n)
    (live : P.Format o A R) (κ b : ℝ) (wallet : P.remBound o R κ b) :
    ∃ (a c : ℝ) (fees : ℕ → ℝ), 0≤a ∧ 0≤c ∧ a+c≤b ∧
      SumBudget (fun j => R.p.mass (P.support j) (fees j)) a ∧
      (∀ j, RegFit R o d A (P.support j) (P.regular j) ∧ R.p.supBounds o (P.support j) (P.regular j) (fees j)) ∧
      (cold o P).Format o A R ∧ (cold o P).remBound o R κ c ∧
      (∀ B U, P.density o B R U = (R.eval U:ℂ)*(∑' j,P.maskedTerm R j U) +
        (primary o P.x).density o B R U + account (cold o P) R U) := by
  obtain ⟨a,c,s,h,ha,hc,le,charge,regular,fit,hard,values⟩ := WilsonMeasuredNullAccounts.atoms F A o R P live wallet
  refine ⟨a,c,s,ha,hc,le,regular,fit,format R A o P live,?_,fun B U => split R B o P U⟩
  exact ⟨0,c,le_rfl,hc,by simp,charge,
    ⟨fun _ => 0,budget0 _ _,fun _ => (regular0 R.p _ o).2⟩,⟨h,hard,values⟩⟩

end YM.Integration.WilsonOriginalNullInventory
