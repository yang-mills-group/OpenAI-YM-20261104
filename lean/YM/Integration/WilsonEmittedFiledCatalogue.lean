import YM.Integration.WilsonEmittedTransitionJet

/-! The actual finite field transition on the incoming catalogue salary.
Different rooted books can use their own physical grades and test space. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonEmittedFiledCatalogue
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density
open AnalyticBridge.SectorAffine.Offset WilsonEmittedWordJointFare WilsonEmittedCutGrouping
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius
open private survey from YM.Integration.WilsonEmittedChildCatalogue
variable {G : Gauge} {n : Side} {A V : Type} [Fintype A] [DecidableEq V]
variable {I X : A→Type} {Γ : Census V} {P : A → Passport n V}
variable (M : (a:A)→I a→Row (P a) Γ G (X a)) (w : A→V→ℝ) (grades : A→V→ℕ)
variable (x : (a:A)→X a) (c : A→ℝ) (ℓ : A→ℕ)
variable (B : BudgetPoint) {σ b α K θ : A→ℝ} {p pieces depth : A→ℕ} {g : ℝ}
variable (old : ∀a,Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (pieces a) (depth a))
variable (scope : ∀a,Invoice.Supports B (K a) (α a) g (σ a) (θ a))
variable (s : Γ.Mode) (v : V) (hv : v∈s.val)

def words (μ : (a:A)→I a→Prop) (t : ℝ) (U : Config G n) :=
  ∑ a:A, c a • (t^(ℓ a) • Air.sums (M a) (fun i=>(M a i).paint (x a)) (μ a) t U)

def rent (j m : ℕ) :=
  ∑ a : A, |c a| * WilsonEmittedTransitionJet.fee j (ℓ a)
    ((Poly.toll (w a) s)⁻¹ * WilsonEmittedLocatedCensus.receipt G B j
      (p a+depth a+1) (pieces a) m (b a) (α a) (θ a))

omit [Fintype A] in
include scope in
theorem width (a:A) : 0<σ a := by
  have h := (scope a).2.2.2.2.2
  exact (add_pos_of_nonneg_of_pos (mul_nonneg h.1 (inv_nonneg.mpr (Nat.cast_nonneg _)))
    (mul_pos (by norm_num) h.2.1)).trans_le h.2.2

omit [Fintype A] in
include old scope in
theorem staff (a:A) : Air.Staff (M a) (fun i=>(M a i).paint (x a)) (grades a) (σ a) (p a+depth a+1) :=
  Air.license (M a) _ (grades a) (w a) (old a) (width B scope a) (fun i=>(old a).honor i (x a))

include scope old hv in
theorem funded (j m : ℕ) (μ : (a:A)→I a→Prop)
    (stay : ∀a i,μ a i→s=(M a i).mode ∧ m≤(M a i).length)
    (z : Chart G n) (unit : ‖z‖≤1) :
    Through j (fun t:Chart G n=>words M x c ℓ μ t.1 (increment 1 t.2)) z
      (rent (G:=G) w c ℓ B (p:=p) (pieces:=pieces) (depth:=depth) (b:=b) (α:=α) (θ:=θ) s j m) := by
  have h (a:A) := WilsonEmittedLocatedCensus.original (M a) (w a) (grades a) (old a)
    B (scope a) j m s v hv (x a) (μ a) (stay a) z unit
  have all (a:A) := WilsonEmittedTransitionJet.marked (ℓ a) j z unit (h a)
  simpa only [words,rent,WilsonEmittedRootCensus.field] using
    survey c _ _ all

include old scope in
theorem numerical {q : ℕ} {ν : A→ℕ} (closed : ∀a,q+ν a=ℓ a+(Launch.index Γ (grades a) s+1))
    (hg : 0<g) (U : Config G n)
    (posted : ∀a,Summable (fun i=>Spill.raw (M a) g (x a) i U)) :
    (g^q)⁻¹ • words M x c ℓ (fun a=>picked (M a) s) g U =
      ∑a:A,c a • (g^(ν a) • (Spill.Foundry.uncut (M a) g (x a) U).part s) := by
  rw [words,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [WilsonEmittedRecordedField.uncut (M a) (x a) (grades a) (staff M w grades x B old scope a)
    s hg.ne' U (posted a)]
  rw [←Complex.ofReal_inv,←Complex.real_smul]
  simp only [smul_smul]
  congr 1
  have he := congrArg (fun i:ℕ=>g^i) (closed a)
  simp only [pow_add] at he
  field_simp [hg.ne']
  convert congrArg (fun z:ℝ=>c a*z) he.symm using 1 <;> ring

end YM.Integration.WilsonEmittedFiledCatalogue
end
