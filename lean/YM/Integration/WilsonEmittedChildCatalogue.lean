import YM.Integration.WilsonEmittedRecordedField
import YM.Integration.WilsonEmittedHealthyField

/-! The earned derivatives of a complete signed family of genuine rooted
catalogues, with their different widths, Laurent ranks and moving orders. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedChildCatalogue
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open AnalyticBridge.SectorAffine.Offset Comparison.Density Push.AbsoluteSums
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedLocatedCensus
open scoped BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A X V : Type} [Fintype A] [DecidableEq V]
variable {Γ : Census V} {P : A → Passport n V} {I : A → Type}
variable (M : (a:A)→I a→Row (P a) Γ G X) (w : A→V→ℝ) (grades : V→ℕ) (B : BudgetPoint)
variable {σ b α K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀ a, Armada (M a) (w a) grades (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀ a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s : Γ.Mode) (v : V) (hv : v∈s.val) (x : X) (c : A→ℝ)

def mass (j m : ℕ) := ∑a:A, |c a| *(Poly.toll (w a) s)⁻¹ *
  receipt G B j (p a+depth a+1) (pieces a) m (b a) (α a) (θ a)
def sum (μ : (a:A)→I a→Prop) (t : ℝ) (U : Config G n) :=
  ∑ a:A, c a • Air.sums (M a) (fun i=>(M a i).paint x) (μ a) t U

private theorem survey {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (F : A→Y→ℂ) {m : ℕ} {z : Y} (D : A→ℝ) (fund : ∀a,Through m (F a) z (D a)) :
    Through m (fun t:Y=>∑ a:A,c a • F a t) z (∑a:A,|c a| *D a) := by
  let f (a:A) (t:Y) := c a • F a t
  have h (a:A) : Through m (f a) z (|c a| *D a) := (fund a).scale (c a)
  refine ⟨ContDiffAt.sum (fun a _=>(h a).smooth),?_⟩
  intro i hi
  rw [iteratedFDeriv_fun_sum_apply (fun a _=>(h a).smooth.of_le (by exact_mod_cast hi))]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum fun a _=>(h a).pay i hi)

include old scope hv in
theorem original (j m : ℕ) (μ : (a:A)→I a→Prop)
    (kept : ∀ a i,μ a i→s=(M a i).mode ∧ m≤(M a i).length)
    (z : Chart G n) (unit : ‖z‖≤1) :
    Through j (fun h : Chart G n=>sum M x c μ h.1 (increment 1 h.2)) z
      (mass (G:=G) w B (p:=p) (pieces:=pieces) (depth:=depth) (b:=b) (α:=α) (θ:=θ) s c j m) := by
  have h (a:A) := WilsonEmittedLocatedCensus.original (M a) (w a) grades (old a) B (scope a) j m s v hv x (μ a) (kept a) z unit
  simpa only [sum,mass,mul_assoc,WilsonEmittedRootCensus.field] using survey c _ _ h

end YM.Integration.WilsonEmittedChildCatalogue
end
