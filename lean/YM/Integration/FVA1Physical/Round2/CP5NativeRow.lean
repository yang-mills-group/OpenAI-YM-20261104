import YM.QuadraticLocal.Earn.Blend

/-! Pay both occurrences of the analytic support price in a physical
single-marker input. The helper keeps the entire passport, including
windings, and leaves the field amplitude as an independent bounded test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.CP5
open Finset Lattice YM.Wilson RG Marker QuadraticLocal.Earn Push.AbsoluteSums
open scoped Classical BigOperators
variable {G:Gauge} {I:Type} [DecidableEq I] {n:Side} {r:ℕ}

def scaledAtom (c:ℝ) (A:RG.Atom G r) : RG.Atom G r :=
  {A with coeff := fun j => c*A.coeff j}

theorem scaled_poly (c:ℝ) (A:RG.Atom G r) (X:Fin r→G.Color) :
    (scaledAtom c A).poly X = c*A.poly X := by
  unfold RG.Atom.poly scaledAtom
  rw [Finset.mul_sum]
  exact sum_congr rfl (fun _ _=>mul_assoc ..)

private theorem scaled_budget (c σ:ℝ) (A:RG.Atom G r) :
    (scaledAtom c A).budget σ = |c| * A.budget σ := by
  unfold RG.Atom.budget RG.Atom.magnitude
  simp only [scaledAtom,abs_mul,←Finset.mul_sum,mul_assoc]
  rfl

theorem scaled_unmasked (c:ℝ) (A:RG.Atom G r) (U:Config G n) (o:Site n) :
    (scaledAtom c A).unmasked U o = c * A.unmasked U o := scaled_poly c A _

def reserve (A:RG.Atom G r) (σ:ℝ) : ℝ := 1+A.budget σ
theorem reserve_pos (A:RG.Atom G r) (σ:ℝ) : 0 < reserve A σ := by
  have h : 0≤A.budget σ := mul_nonneg (sum_nonneg fun _ _=>abs_nonneg _) (Real.exp_pos _).le
  unfold reserve
  linarith

def singletonBinder (P:Passport n I) (R:Census I) (i:I) : Binder P R where
  mode := R.fire i
  front := i
  east := mem_singleton_self i
  path _ := []
  span j h := by obtain rfl : j=i := mem_singleton.mp h; rfl
  extra := 0

def unitRow {α:Type} (P:Passport n I) (R:Census I) (i:I) (A:RG.Atom G r) (legal:A.Invariant)
    (σ:ℝ) (c:ℂ) (amp:α→ℂ) : Row P R G α where
  binder := singletonBinder P R i
  lamp := ⟨r,r,1,by decide,by omega⟩
  atom := scaledAtom (reserve A σ)⁻¹ A
  lawful := fun u x=> by rw [scaled_poly,scaled_poly,legal u x]
  clear := r=0
  salary := 1+‖c‖*reserve A σ
  sound := by have := mul_nonneg (norm_nonneg c) (reserve_pos A σ).le; linarith
  paint y := (c*(reserve A σ:ℂ))*amp y
  rank h := h

theorem unitRow_read {α:Type} (P:Passport n I) (R:Census I) (i:I) (A:RG.Atom G r)
    (legal:A.Invariant) (σ:ℝ) (c:ℂ) (amp:α→ℂ) (y:α) (g:ℝ) (U:Config G n) :
    (unitRow P R i A legal σ c amp).nominal g y U =
       c*amp y*(A.unmasked U (P.origin i):ℂ) := by
  change (c*(reserve A σ :ℂ)*amp y)*((g^((r:ℤ)-r)*(scaledAtom (reserve A σ)⁻¹ A).unmasked U (P.origin i):ℝ):ℂ) = _
  simp only [sub_self,zpow_zero,one_mul,scaled_unmasked,Complex.ofReal_mul,Complex.ofReal_inv]
  field_simp [(Complex.ofReal_ne_zero.mpr (reserve_pos A σ).ne')]

theorem unitRow_eligible {α:Type} (P:Passport n I) (R:Census I) (i:I) (A:RG.Atom G r)
    (legal:A.Invariant) (σ:ℝ) (c:ℂ) (amp:α→ℂ) (bounded:∀ y,‖amp y‖≤1) :
    let row := unitRow P R i A legal σ c amp
    row.Graceful σ ∧ row.Credentials r (fun _=>1) ∧ row.Budget ∧
    row.length=P.height i+A.length := by
  intro row
  refine ⟨?_,⟨le_rfl,?_⟩,?_,?_⟩
  · change (scaledAtom _ A).budget σ ≤ 1
    rw [scaled_budget,abs_of_pos (inv_pos.mpr (reserve_pos A σ)),mul_comm,←div_eq_mul_inv,div_le_one (reserve_pos A σ)]
    unfold reserve
    linarith
  · simp [row,unitRow,Row.mode,singletonBinder,Census.fire]
  · intro y
    change ‖c*(reserve A σ:ℂ)*amp y‖ ≤ 1+‖c‖*reserve A σ
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (reserve_pos A σ).le]
    have := mul_le_mul_of_nonneg_left (bounded y) (mul_nonneg (norm_nonneg c) (reserve_pos A σ).le)
    linarith
  · simp [row,unitRow,Row.length,singletonBinder,Binder.length,Binder.distance,Census.fire,RG.Atom.length,scaledAtom]
    rfl

end YM.Integration.FVA1Physical.Round2.CP5
