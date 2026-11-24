import YM.Integration.WilsonOriginalProjectedCurvatureBudget
import YM.QuadraticLocal.Sunrise.Loan

/-! Register every original Wilson token at its measured signed coupling power.
The positive source advances are chosen from the full finite roster before the torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureLoan
open Lattice Wilson RG Source Labels Marker QuadraticLocal.Sunrise
open PhysicalNext.Repeat.Legato LocalComparison ActualOriginalQPackets
open WilsonOriginalProjectedCurvatureBudget
open scoped Classical
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G} {V : Type} [Fintype V]
  (u : V → MS.Rake.Label B) (s : Row (R:=R) u)

def toll := ActualOriginalQLayout.rankCap R u + 1

def filed : Loan where
  e := grade u s
  r := ActualRunKernelPackets.tokenRank R (degree u) s
  toll := toll (R:=R) u
  higher := Nat.succ_pos _
  crest := by
    have h := limit u s
    change _ ≤ _ + (ActualOriginalQLayout.rankCap R u + 1) + 1
    omega

theorem receipt : (filed u s).lag = -(ActualRunKernelPackets.fieldRank R (degree u) s : ℤ) ∧
    (filed u s).r ≤ ActualOriginalQLayout.rankCap R u ∧
    (filed u s).e ≤ ActualOriginalQLayout.rankCap R u ∧
    (filed u s).toll = ActualOriginalQLayout.rankCap R u + 1 :=
  ⟨phase u s, limit u s, (Nat.sub_le _ _).trans (limit u s), rfl⟩

end YM.Integration.WilsonOriginalProjectedCurvatureLoan
