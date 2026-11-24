import YM.Integration.WilsonCapturedFactoryReturn
import YM.Integration.WholeProductCapture

/-! The original retained product chooses a label with vanishing
stored head at the lower stop. Its measured periodic germ may differ.
Carry the actual priced discrepancy through the funded chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRetainedReturnPrice
open Filter Real Lattice RG Source Labels PhysicalNext.Repeat.Legato
open Trace.Pilot Trace.Physical Trace.Physical.GermGraph Work.G08 RG16.Literal Bid
open scoped Classical Topology
variable {G : Gauge} (R : Run G) (d : ℕ)

theorem prices (hG : G.Simple) :
    ∃ U : ℕ, (∀ u≥U, ∀ p, Opened R.family d u p) ∧
    ∀ γ>0, ∃ M : ℝ, 1≤M ∧ ∀ u≥U, ∀ b N p
      (ho : Opened R.family d u p) (ub : u≤b) (bN : b<N)
      (Y : Cut R.family N p) (B : R.family.label d) (a : ℝ),
      WholeProductCapture.Retained R.family N b p d u R.makes ho ub bN Y B a →
      ∀ i≥u, i≤N →
      mCost R.family d N p i (topReport R.family N p d R.makes u ho (ub.trans bN.le) Y -
        (R.family.factory d N p).terminal.symm B) ≤
        M*(invoice (C:=R.family) d u p*a)*
        exp (γ*(R.family.S.scale i-R.family.S.scale u)-(1/8:ℝ)*(R.family.S.scale b-R.family.S.scale u)) := by
  obtain ⟨U,openU,carry⟩ := WilsonCapturedFactoryReturn.coordinates R hG d
  refine ⟨U,openU,?_⟩
  intro γ pos
  obtain ⟨M,hM,step⟩ := carry γ pos
  refine ⟨M,hM,?_⟩
  intro u late b N p ho ub bN Y B a purchased i ui iN
  obtain ⟨P,g,_,_,_,lower⟩ := purchased
  let x := topReport R.family N p d R.makes u ho (ub.trans bN.le) Y -
    (R.family.factory d N p).terminal.symm B
  have scale := step u late N p i ui iN x
  calc
    _ ≤ M*(exp (γ*(R.family.S.scale i-R.family.S.scale u)) *
        (invoice (C:=R.family) d u p*(a/gainChart R.family.path b u))) :=
      scale.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left lower (exp_pos _).le) (by linarith))
    _ = _ := by rw [exp_sub]; unfold gainChart; ring

end YM.Integration.WilsonRetainedReturnPrice
