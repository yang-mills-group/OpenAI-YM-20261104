import YM.Integration.WilsonCubicSummedLocalPolynomial
import YM.Contacts.Model.Voyage

/-! Omitted true paths at one original root. The physical and prescribed
jets use their own finite-period link coordinates and the same path cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonRootedCubicPathCut
open Function Filter Lattice RG Wilson Precision Exterior Contacts Contacts.Model
open Push Push.Uniform Push.AbsoluteSums Gauge Stationary Tree Pressure Pressure.Tube ConnectedActivityE6
open WilsonVacuumPreResetJointField
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side} {t : ℕ} {σ C : ℝ} {S : StepData c f}
  {T : Tube G S} {F : Forest S.ratio}

def long (A : ℕ → Atom G t) (b : ℕ) : Set ℕ := {i | b ≤ (A i).length}
def residue (A : ℕ → Atom G t) (b : ℕ) (l : Signed) (p : Site f) (U : Config G f) :=
  (∑' i,(A i).unmasked (pull l 0 U) p) - Model.title (long A b)ᶜ p A (pull l 0 U)

theorem exact_tail (A : ℕ → Atom G t) (hs : 0<σ) (cash : SumBudget (fun i => (A i).budget σ) C)
    (b : ℕ) (l : Signed) (p : Site f) (U : Config G f) :
    residue A b l p U = Model.title (long A b) p A (pull l 0 U) := by
  let v (i : ℕ) := (A i).unmasked (pull l 0 U) p
  have h : Summable v := .of_norm_bounded (cash.2.1.mul_right ((2:ℝ)^t))
    (fun i => ((A i).unmasked_bound _ _).trans (mul_le_mul_of_nonneg_right ((A i).lower_budget σ hs) (by positivity)))
  have eq := h.tsum_subtype_add_tsum_subtype_compl (long A b)
  change (∑' i,v i)-(∑' i:↥((long A b)ᶜ),v i.val)=∑' i:↥(long A b),v i.val
  rw [← eq,add_sub_cancel_right]

private theorem ticket {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℕ → Atom G t) (hs : 0<σ) (cash : SumBudget (fun i => (A i).budget σ) C)
    (b k : ℕ) (l : Signed) (p : Site f) (U : E → Config G f) {K : Set E} (hO : IsOpen K)
    (hc : IsPreconnected K) {y : E} (hy : y∈K) {Z : ℝ}
    (links : ∀ e z, z∈K → Allows k (fun w => G.mat (U w e)) z Z) :
    Allows k (residue A b l p ∘ U) y ((Model.pole σ b*C)*Model.atomSize G σ Z k t) := by
  let V := fun w => pull l 0 (U w)
  have rotated (e : Bond f) (z : E) (hz : z∈K) : Allows k (fun w => G.mat (V w e)) z Z := by
    let d := (posDir e.2).rotate l
    let x := affine l (0:Site f) e.1
    have h := links (d.used x) z hz
    unfold V pull Lattice.Step.read
    split
    · exact h.inverse (f:=fun a => U a _)
    exact h
  have h := Model.yore (long A b) p (U:=V) hO hc hy rotated A hs cash b (fun _ h => h)
  exact h.germ (Filter.Eventually.of_forall fun z => (exact_tail A hs cash b l p (U z)).symm)

/-- This is the same rate for every finite period, measured coat and root.
The held field, orientation and the full unmasked long part remain genuine. -/
theorem physical (A : ℕ → Atom G t) (hs : 0<σ) (cash : SumBudget (fun i => (A i).budget σ) C)
    (b k : ℕ) (l : Signed) (p : Site f) (P : Finset (Bond c)) (X : Coat T F) (z : Arguments G c f) :
    Allows k (residue A b l p ∘ field P X) z ((Model.pole σ b*C)*Model.atomSize G σ (linkFee G k) k t) :=
  ticket A hs cash b k l p _ isOpen_univ isPreconnected_univ (Set.mem_univ z)
    (fun e y _ => WilsonVacuumPreResetJointField.links P X k y e)

theorem prescribed (A : ℕ → Atom G t) (hs : 0<σ) (cash : SumBudget (fun i => (A i).budget σ) C)
    (b k : ℕ) (l : Signed) (p : Site f) {Z : ℝ} (ink : PaintSupply G k Z) :
    Allows k (residue A b l p ∘ Stationary.input G f) 0
      ((Model.pole σ b*C)*Model.atomSize G σ (outerCost G k Z) k t) :=
  ticket A hs cash b k l p _ Metric.isOpen_ball (convex_ball (0:Link G f) 1).isPreconnected
    (Metric.mem_ball_self zero_lt_one) (fun e y hy => Model.imprints ink (le_of_lt (by simpa using hy)) e)

end YM.Integration.WilsonRootedCubicPathCut
