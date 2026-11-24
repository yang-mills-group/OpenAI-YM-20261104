import YM.Integration.WilsonEmittedCompactBalance
import YM.Integration.WilsonEmittedRootedJetWage

/-! Recover the signed sum on the physical parent patch from its original
rooted angular and thermal coordinate tariffs. Long words keep their salary. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedWindingBalance
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset
open WilsonEmittedWordJointFare WilsonEmittedCutGrouping WilsonEmittedFiledCatalogue
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A→Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ℓ : A→ℕ)
variable (B : BudgetPoint) {σ b α K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s : Multi.Hot Γ) (v : V) (hv : v∈s.val.val)
variable (tube : LinkTube G) {k m j l D a₀ J : ℕ} {y o : Site n} {W ε : ℝ}
local notation "q" a:max => (fun i:I a=>(M a i).paint (x a))
local notation "sum" => words M x c ℓ
local notation "near" => (fun a=>early (M a) s.val m)
local notation "far" => (fun a=>late (M a) s.val m)
local notation "total" => (fun a=>picked (M a) s.val)
local notation "full" => (fun z:Chart G n=>sum total z.1 (increment 1 z.2))
local notation "fee" u:max => rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth)
  (b:=b) (α:=α) (θ:=θ) s.val J u
local notation "paid" a:max => staff M w grades x B old scope a

include scope old hv in
theorem original (hε : 0 ≤ ε) (read : ∀ i < j,
      ∑ u : Fin i → WilsonEmittedRootedJetWage.Slot G n,
        ‖iteratedFDeriv ℝ i full 0 (WilsonEmittedRootedJetWage.peg G n ∘ u)‖ ≤ ε)
    (same : ∀a,(P a).origin v=o) (positive : 0<g) (small : g≤1)
    (hj : j≤J) (hl : l≤j) (date : B.order≤J) (home : separation o y≤a₀)
    (inside : 2*m≤k) (apart : k<D) (room : Room B n tube D W) :
    B.Regular (neighborhood D o) (sum near g) ∧
      B.supBounds y (neighborhood D o) (sum near g)
        (Anchor.focus k a₀ B^B.order *
          (groupPrice tube B.order*(l*((j:ℝ)*ε+(fee 0)*g^(j-l)+(fee m))+(fee 0)*W^l))) := by
  have jets (i:ℕ) (hi:i<j) : ‖iteratedFDeriv ℝ i (full-(fun _:Chart G n=>(0:ℂ))) 0‖ ≤ ε := by
    simpa only [show (fun _:Chart G n=>(0:ℂ))=0 from rfl, sub_zero] using
      WilsonEmittedRootedJetWage.original (iteratedFDeriv ℝ i full 0) (read i hi)
  have partition (u:Directions G n) : full (g,u)-0=sum near g (increment 1 u)+sum far g (increment 1 u) := by
    simp only [sub_zero,words,←Finset.sum_add_distrib]
    apply sum_congr rfl
    intro a _
    rw [divided (M a) (q a) (grades a) (paid a) s.val m g (increment 1 u)]
    simp only [smul_add]
  have whole := funded M w grades x c ℓ B old scope s.val v hv J 0 total (fun _ _ h=>⟨h,Nat.zero_le _⟩)
  have short := funded M w grades x c ℓ B old scope s.val v hv J 0 near (fun _ _ h=>⟨h.1,Nat.zero_le _⟩)
  have long := funded M w grades x c ℓ B old scope s.val v hv J m far (fun _ _ h=>h) (g,0)
    (by simp [Prod.norm_def,abs_of_pos positive,small])
  have support (a:A) := WilsonEmittedWordFootprint.kept (M a) s.val m v hv (q a) B g inside
  have physical (a:A) := local_field (M a) (q a) (grades a) (paid a) s.val B m v hv g
  apply WilsonEmittedWindingField.original B tube full (fun _=>0) (sum near) (sum far) hε jets
    partition (by simpa only [show (fun _:Chart G n=>(0:ℂ))=0 from rfl,sub_zero] using whole) short long positive small hl hj
    ?_ ?_ ?_ home apart room date
  · intro U Z agrees
    apply sum_congr rfl
    intro a _
    rw [support a U Z (by simpa only [same a] using agrees)]
  · intro t U
    apply sum_congr rfl
    intro a _
    rw [(physical a).2.1 t U]
  · apply Finset.measurable_sum
    intro a _
    exact (((physical a).2.2).const_smul (g^ℓ a)).const_smul (c a)

end YM.Integration.WilsonEmittedWindingBalance
end
