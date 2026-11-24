import YM.Integration.WilsonEmittedFiledCatalogue

/-! Every finite transition coefficient stays with its own original
receipt on the joint coarse link direction. Scalar output is included. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedFiledGerm
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ℓ : A→ℕ)
variable (B : BudgetPoint) {σ b α K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s : Multi.Hot Γ) (L : A→Layout G) (tape : A→Finset Age)
local notation "chart₀" => Chart G n
local notation "q" a:max => (fun i:I a=>(M a i).paint (x a))
local notation "d" a:max => (Launch.index Γ (grades a) s.val+1)
local notation "row" a:max => WilsonEmittedRootCensus.field (M a) (q a) (picked (M a) s.val)
local notation "book" a:max => Air.craft (M a) (q a) (grades a) (L a) (tape a)
local notation "paid" a:max => staff M w grades x B old scope a
local notation "full" => (fun z:chart₀=>words M x c ℓ (fun a=>picked (M a) s.val) z.1 (increment 1 z.2))
def price (j : ℕ) (u : Directions G n) (a:A) : ℂ :=
  if ℓ a+d a≤j then
    (Air.discharge (book a) (j-ℓ a-d a)
      (Stationary.arm G n 1 (WilsonCubicOriginalTorus.coordinates G n u))).part s.val
  else 0

include old scope L tape in
theorem smooth : ContDiffAt ℝ ω full 0 := by
  apply ContDiffAt.sum
  intro a _
  exact ((contDiffAt_fst.pow _).smul (WilsonEmittedRecordedJet.analytic (M a) (x a)
    (grades a) (paid a) (L a) (tape a) s)).const_smul (c a)

private theorem join (F : A→chart₀→ℂ) (h : ∀a,ContDiffAt ℝ ω (F a) 0) (j:ℕ) (u:Directions G n) :
    Assembly.jet (fun z:chart₀=>∑a,c a • F a z) j (1,u)=∑a,c a • Assembly.jet (F a) j (1,u) := by
  let f (a:A) := fun z:chart₀=> c a • F a z
  have smooth (a:A) : ContDiffAt ℝ ω (f a) 0 := (h a).const_smul (c a)
  unfold Assembly.jet
  rw [iteratedFDeriv_fun_sum_apply (fun a _=>(smooth a).of_le le_top)]
  simp only [_root_.sum_apply,Finset.smul_sum]
  apply sum_congr rfl
  intro a _
  rw [show f a=c a • F a from rfl,
    iteratedFDeriv_const_smul_apply ((h a).of_le le_top), _root_.smul_apply]
  exact smul_comm ..

include old scope in
theorem heard (j : ℕ) (u : Directions G n) :
    Assembly.jet full j (1,u)=∑a,c a • price M grades x ℓ s L tape j u a := by
  let F (a:A) (z:chart₀) := z.1^ℓ a • (row a) z
  have smooth (a:A) := WilsonEmittedRecordedJet.analytic (M a) (x a) (grades a)
    (paid a) (L a) (tape a) s
  have analytic (a:A) : ContDiffAt ℝ ω (F a) 0 := (contDiffAt_fst.pow _).smul (smooth a)
  apply (join c F analytic j u).trans
  apply sum_congr rfl
  intro a _
  congr 1
  rw [show Assembly.jet (F a) j (1,u)=_ from
    WilsonEmittedTransitionJet.original (ℓ a) j (row a) (smooth a) u]
  unfold price
  by_cases first : ℓ a≤j
  · rw [if_pos first]
    by_cases second : ℓ a+d a≤j
    · rw [if_pos second]
      have eqn : j-ℓ a=d a+(j-ℓ a-d a) := by omega
      conv_lhs => rw [eqn]
      exact WilsonEmittedRecordedJet.original (M a) (x a) (grades a) (paid a) (L a) (tape a) s _ u
    · rw [if_neg second]
      exact WilsonEmittedRecordedJet.below (M a) (x a) (grades a) (paid a) (L a) (tape a) s _ (by omega) u
  · simp [first,show ¬ℓ a+d a≤j by omega]

end YM.Integration.WilsonEmittedFiledGerm
end
