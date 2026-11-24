import YM.FVA2.Based

/-!
# Scalar torus line at the same conventions as Endμ

Green function with *one* zero mode deleted. Real even function. Prove all
identities before taking any quotient or limit. No continuum core assumption.
`fwd i`/`back i` include the sign in the discrete adjoint (`back`
is adjoint of `fwd`), native fine units (not restoring powers of a).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Green
open MS MS.Koszul MS.Tone MS.Orbit MS.Landau MS.Swirl.Near Lattice Finset
open MS.Momentum
variable {n : Side}

section diffs
variable {R : Type*} [Ring R]

/-- Discrete coordinate differences at regulator n on the cover. -/
def fwd (i : Axis) : (Site n → R) →ₗ[R] (Site n → R) where
  toFun f x := f (x+Lattice.step i) - f x
  map_add' f g := funext fun x => by simp only [Pi.add_apply]; abel
  map_smul' c f := funext fun x => Eq.symm (mul_sub c (f (x+step i)) (f x))

def back (i : Axis) : (Site n → R) →ₗ[R] (Site n → R) where
  toFun f x := f (x-Lattice.step i) - f x
  map_add' f g := funext fun x => by simp only [Pi.add_apply]; abel
  map_smul' c f := funext fun x => Eq.symm (mul_sub c (f (x-step i)) (f x))

lemma fwd_of (i : Axis) (f : Site n → R) (x : Site n) :
    fwd i f x= f (x+Lattice.step i)-f x := rfl
lemma back_of (i : Axis) (f : Site n → R) (x : Site n) :
    back i f x= f (x-Lattice.step i)-f x := rfl

lemma fwd_swap (i j : Axis) (f : Site n → R) : fwd i (fwd j f) = fwd j (fwd i f) := by
  ext x; simp_rw [fwd_of]; rw [add_right_comm x]; abel

lemma mixed_swap (i j : Axis) (f : Site n → R) : fwd i (back j f) = back j (fwd i f) := by
  ext x; simp_rw [back_of,fwd_of,back_of]; rw [add_sub_right_comm]; abel
lemma back_swap (i j : Axis) (f : Site n → R) : back i (back j f) = back j (back i f) := by
  ext x; simp_rw [back_of]; rw [sub_right_comm]; abel_nf
lemma adjoint (i : Axis) (f g : Site n → R) :
    ∑ x : Site n, f x * fwd i g x = ∑ x : Site n, back i f x * g x := by
  simp_rw [back_of,fwd_of,mul_sub,sub_mul,sum_sub_distrib]; congr 1
  rw [← Equiv.sum_comp (Equiv.addRight (Lattice.step i)) (fun x : Site n => f (x-step i) * g x)]
  exact sum_congr rfl (fun x _ => by change _= f (x+step i-step i)*g (x+step i); rw [add_sub_cancel_right])

lemma adjoint' (i : Axis) (f g : Site n → R) :
    ∑ x : Site n, f x * back i g x = ∑ x : Site n, fwd i f x * g x := by
  simp_rw [back_of,fwd_of,mul_sub,sub_mul,sum_sub_distrib]; congr 1
  rw [← Equiv.sum_comp (Equiv.addRight (Lattice.step i)) (fun x : Site n => f x * g (x-step i))];
  exact sum_congr rfl (fun x _ => by change f (x+step i)*g (x+step i-step i)=_;rw [add_sub_cancel_right])

lemma reflect_coord (i : Axis) (f : Site n → R) :
    fwd i (fun x : Site n=> f (-x)) = fun x => back i f (-x) := by
  ext x; simp_rw [fwd_of, back_of]; rw [neg_add, sub_eq_add_neg (-x)]

/-- Positive link Laplacian of the auxiliary torus (acting componentwise when used on fields). -/
def lap : (Site n → R) →ₗ[R] (Site n → R) := ∑ i : Axis, (back i).comp (fwd i)

lemma lap_of (f : Site n → R) (x : Site n) : lap f x = ∑ i : Axis, back i (fwd i f) x := by
  unfold lap; simp_rw [LinearMap.sum_apply,Finset.sum_apply]; rfl
lemma lap_fwd (i : Axis) (f : Site n → R) : lap (fwd i f) = fwd i (lap f) := by
  unfold lap; simp_rw [LinearMap.sum_apply,map_sum,LinearMap.comp_apply, mixed_swap i,fwd_swap i]
lemma lap_back (i : Axis) (f : Site n → R) : lap (back i f) = back i (lap f) := by
  unfold lap; simp_rw [LinearMap.sum_apply,map_sum,LinearMap.comp_apply]
  exact Finset.sum_congr rfl fun j _=> by rw [mixed_swap j i,back_swap j i]
end diffs

abbrev waveStep (p : Site n) (i : Axis) := MS.Momentum.wave (Coord p) i
abbrev stepPhase (p : Site n) (i : Axis) := bill (Coord p) (offset (some i,false))

def symbol (p : Site n) := MS.Momentum.sq (MS.Momentum.wave (Coord p))
def ds (p : Site n) (i : Axis) := Bloch.cell p (step i) - 1
lemma cellNeg (p x : Site n) : Bloch.cell (-p) x = Bloch.cell p (-x) := by
  rw [Bloch.cell_duality (-p),Bloch.cell_inverse, Bloch.cell_inverse,Bloch.cell_duality]

lemma halfPhase (p : Site n) (i : Axis) : stepPhase p i=(bill (-Coord p) (offset (some i,true)))⁻¹ := by
  simp only [stepPhase,opp, inv_inv]; rfl

lemma cellStep (p : Site n) (i : Axis) : Bloch.cell p (step i)= bill (Coord p) (embed (step i)) := by
  rw [Tone.rights,dual_cell p,Lattice.wrap_step]

lemma neg_step_phase (p : Site n) (i : Axis) : ds (-p) i * stepPhase p i = -(Complex.I * (waveStep p i:ℂ)) := by
  unfold ds stepPhase; rw [cellNeg,Bloch.cell_inverse,cellStep, mul_comm]
  exact (Tone.opp (Coord p) _ ▸ Tone.Frame.triangle i (Coord p))
lemma pos_step_phase (p : Site n) (i : Axis) : ds p i = Complex.I * (waveStep p i:ℂ)*stepPhase p i := by
  have ht:= Tone.Frame.triangle i (-Coord p)
  rw [neg_neg, ← cellStep,Tone.Frame.wave_neg, Pi.neg_apply, Complex.ofReal_neg, mul_neg,neg_neg] at ht
  change bill _ _ * ds p i = Complex.I * (waveStep p i:ℂ) at ht
  rw [← ht]
  change ds p i = bill _ (offset (some i,true))*_ * _
  rw [halfPhase, mul_right_comm, mul_inv_cancel₀ (Tone.nonz _ _), one_mul]
lemma neg_step_formula (p : Site n) (i : Axis) : ds (-p) i = -(Complex.I * (waveStep p i:ℂ))*(stepPhase p i)⁻¹ := by
  rw [← neg_step_phase, mul_assoc, mul_inv_cancel₀ (show stepPhase p i≠0 from Tone.nonz _ _), mul_one]

lemma product_step (p : Site n) (i : Axis) : ds (-p) i * ds p i = ((waveStep p i)^2 :ℝ) := by
  conv_lhs => arg 2; rw [pos_step_phase]
  rw [mul_comm _ (stepPhase p i), ← mul_assoc, neg_step_phase]
  push_cast; ring_nf; simp

lemma symbol_sum (p : Site n) : (symbol p:ℂ) = ∑ i : Axis, ds (-p) i * ds p i := by
  simp_rw [product_step, symbol, MS.Momentum.sq, Complex.ofReal_sum]
@[simp] lemma symbol_neg (p : Site n) : symbol (-p)=symbol p := Complex.ofReal_injective (by
  rw [symbol_sum,symbol_sum,neg_neg]; exact Finset.sum_congr rfl fun i _ => mul_comm ..)

@[simp] lemma symbol_zero : symbol (0:Site n)=0 := by
  apply Complex.ofReal_injective; rw [symbol_sum]; simp [ds,Bloch.cell]
lemma symbol_pos {p : Site n} (h : p≠0) : 0 < symbol p := by
  by_contra! hp
  have ht : MS.Momentum.wave (Coord p)=0 := NoWave _ (le_antisymm hp (sq_nonnegative _))
  obtain ⟨i,hi⟩ := Bloch.step_picks p h
  apply hi; apply sub_eq_zero.mp; rw [← ds,pos_step_phase,
              show waveStep p i=0 from congr_fun ht i, Complex.ofReal_zero,mul_zero,zero_mul]

lemma cell_fwd (p : Site n) (i : Axis) : fwd i (Bloch.cell p)= ds p i • (Bloch.cell p) := by
  ext1 x; rw [fwd_of,Bloch.cell_add]; change _= _ * (Bloch.cell _ _); unfold ds; ring
lemma cell_back (p : Site n) (i : Axis) : back i (Bloch.cell p)= ds (-p) i • (Bloch.cell p) := by
  ext1 x; rw [back_of,sub_eq_add_neg x,Bloch.cell_add]; change _= _ * (Bloch.cell _ _); unfold ds; rw [cellNeg]; ring
lemma cell_lap (p : Site n) : lap (Bloch.cell p)=(symbol p:ℂ) • (Bloch.cell p) := by
  ext1 x; simp_rw [lap_of,cell_fwd, map_smul,cell_back,Pi.smul_apply, smul_eq_mul,
       symbol_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring

def kernelC (k : ℕ) : Site n→ℂ := ∑ p : Site n, (scaleZ n * ((symbol p:ℂ)⁻¹)^k) • Bloch.cell p
def kernel (k : ℕ) (x : Site n) : ℝ := (kernelC k x).re
lemma termwise (k : ℕ) (x : Site n) : kernelC k x=∑ p : Site n, scaleZ n * ((symbol p:ℂ)⁻¹)^k* Bloch.cell p x := by rw [kernelC,Finset.sum_apply]; rfl
lemma negTerm (k : ℕ) (x : Site n) : kernelC k (-x)=kernelC k x := by
  rw [termwise,termwise,← Equiv.sum_comp (Equiv.neg (Site n)) (fun p : Site n=> scaleZ n * ((symbol p:ℂ)⁻¹)^k* Bloch.cell p x)]
  simp only [Equiv.neg_apply,symbol_neg,cellNeg]

open scoped ComplexConjugate
lemma real_kernel (k : ℕ) (x : Site n) : (kernel k x:ℂ)=kernelC k x := by
  let z:= kernelC k x
  have h : conj z=z := by unfold z; nth_rw 2 [← negTerm k x]; simp only [termwise,map_sum,map_mul,map_inv₀,map_pow, scaleZ, Complex.conj_ofReal, Bloch.cell_bar,Bloch.cell_inverse]
  exact Complex.ext rfl (by
    have hv:= congr_arg Complex.im h; change -z.im=z.im at hv
    change 0 = z.im; linarith)
lemma kernel_even (k : ℕ) (x : Site n) : kernel k (-x)=kernel k x:= by rw [kernel,kernel,negTerm]

lemma ortho_C (x : Site n) : ∑ p:Site n,Bloch.cell p x= if x=0 then brightness n else 0 := by
  by_cases h : x=0
  · subst x; simp [brightness,scaleZ,νt]
  rw [if_neg h]; simp_rw [Bloch.cell_duality (r:=x)]; exact Bloch.sum_cell h

lemma zero_kernelC (x : Site n) : kernelC 0 x= if x=0 then 1 else 0 := by
  simp_rw [termwise,pow_zero,mul_one,← Finset.mul_sum,ortho_C]; split; exact lightW n; exact mul_zero _
lemma mean_zero (k : ℕ) : ∑ x : Site n,kernel (k+1) x=0 := by
  apply Complex.ofReal_injective; simp_rw [Complex.ofReal_sum,real_kernel,termwise]; rw [Finset.sum_comm]
  rw [Complex.ofReal_zero]; apply Finset.sum_eq_zero; intro p _; by_cases h:p=0
  · subst p; simp
  rw [← Finset.mul_sum, Bloch.sum_cell h,mul_zero]

lemma lapC (k : ℕ) (x : Site n) : lap (kernelC (k+1)) x = kernelC k x - if k=0 then scaleZ n else 0 := by
  have he(p:Site n) : scaleZ n * ((symbol p:ℂ)⁻¹)^(k+1) * (symbol p:ℂ) * Bloch.cell p x = scaleZ n * ((symbol p:ℂ)⁻¹)^k * Bloch.cell p x - if p=0 ∧ k=0 then scaleZ n else 0 := by
     by_cases h:p=0
     · subst p; by_cases hz:k=0 <;> simp [*, Bloch.cell]
     have hp : (symbol p:ℂ)≠0:= by exact_mod_cast (symbol_pos h).ne'
     rw [if_neg (not_and_of_not_left _ h),sub_zero,pow_succ,mul_assoc (scaleZ n),mul_assoc (((symbol p:ℂ)⁻¹)^k)]; field_simp
  have hh : (∑ p:Site n, if p=0 ∧ k=0 then scaleZ n else 0) = if k=0 then scaleZ n else 0 := by by_cases ht:k=0 <;> simp [ht]
  rw [termwise,kernelC,map_sum,Finset.sum_apply]; simp_rw [ map_smul,cell_lap,smul_smul,Pi.smul_apply,smul_eq_mul, he]; rw [Finset.sum_sub_distrib,hh]
lemma lapR (k : ℕ) (x : Site n) : lap (kernel (k+1)) x = kernel k x - if k=0 then νt n else 0 := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sub,real_kernel,apply_ite (Complex.ofReal), Complex.ofReal_zero, show (νt n:ℂ)=_ from (rfl : (νt n:ℂ)=scaleZ n), ← lapC]
  simp_rw [lap_of,back_of,fwd_of,Complex.ofReal_sum,Complex.ofReal_sub,real_kernel]
lemma zero_kernel (x : Site n) : kernel 0 x= if x=0 then 1 else 0 := by unfold kernel; rw [zero_kernelC]; split <;> rfl

end YM.FVA2.Green
