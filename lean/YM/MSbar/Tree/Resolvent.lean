import YM.MSbar.Tree.Torus
import YM.Extra.WILSON_STARTUP.Transform

/-!
# Verify the finite Fourier calculation

The rank comparisons operate on Fourier symbols. Here we also relate to finite
real-Wick-calculus checks. Start with Fourier inversion against the Feynman-gf
auxiliary Hessian. (Can dispense with unnecessary longitudinal terms since we
will test only on curls.) Use real matrices and count on all cells of the
periodic lattice, then verify the metric factors separately on the inversion
quotient calculation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tree.Resolvent
open Function Set Filter Lattice Laurent Bloch Matrix Exterior
open Further.FreeCovariance.KP
open scoped Topology BigOperators ComplexConjugate Classical
open WilsonStartup.Polar Torus

variable {α β γ : Type} {m : Side}

section spectrum
variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable [Fintype α] [Fintype β] [Fintype γ]

def spectral (k : Site m → Matrix α β ℂ) := meter m •
   (rotations m α * fiber k * star (rotations m β))
private lemma inverseDF (m : Side) (α : Type) [DecidableEq α] [Fintype α] : star (rotations m α)*rotations m α = (meter m)⁻¹ • 1 := by
  let M:= meter m
  have he:M≠0:= inv_ne_zero (pow_ne_zero _ (side_ne m))
  apply smul_right_injective _ he
  change M • _=M • (M⁻¹ • 1)
  rw [smul_inv_smul₀ he, ← Matrix.smul_mul, mul_eq_one_comm,Matrix.mul_smul, rotations_gram]; exact inv_smul_smul₀ (pow_ne_zero _ (side_ne m)) _
lemma spectral_read (k : Site m → Matrix α β ℂ) : spectral k * rotations m β = rotations m α * fiber k := by
  unfold spectral; rw [Matrix.smul_mul, Matrix.mul_assoc (_ * _),inverseDF,Matrix.mul_smul,Matrix.mul_one]; exact smul_inv_smul₀ (inv_ne_zero (pow_ne_zero _ (side_ne m))) _
lemma spectral_adj (k : Site m → Matrix α β ℂ) : (spectral k)ᴴ = spectral (fun p=> (k p)ᴴ):= by
  unfold spectral; rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,fiber_adj,Matrix.star_eq_conjTranspose,Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]; simp [meter,Matrix.mul_assoc]
lemma spectral_mul (F : Site m → Matrix α β ℂ) (G : Site m → Matrix β γ ℂ) : spectral F * spectral G=spectral (fun p=>F p*G p) := by
  apply cancel_rotation m; rw [Matrix.mul_assoc,spectral_read,spectral_read,← Matrix.mul_assoc (spectral F),spectral_read,Matrix.mul_assoc,fiber_mul]
lemma spectral_add (F G : Site m → Matrix α β ℂ) : spectral F+spectral G=spectral (fun p=>F p+G p):= by
  have h : fiber F + fiber G=fiber (fun p=>F p+G p):= by ext ⟨p,i⟩ ⟨q,j⟩; by_cases he : p=q <;> simp [fiber,he]
  unfold spectral; rw [← h, Matrix.mul_add, Matrix.add_mul,smul_add]
lemma spectral_unit (m : Side) (α : Type) [DecidableEq α] [Fintype α] : spectral (m:=m) (fun _=>1 : Site m → Matrix α α ℂ)=1:= by apply cancel_rotation m; rw [spectral_read, fiber_one, Matrix.mul_one,Matrix.one_mul]
lemma spectral_apply (k : Site m → Matrix α β ℂ) (u v : Site m) (i : α) (j : β) : spectral k (u,i) (v,j) = meter m *
    ∑ p : Site m, cell p (u-v) * k p i j:= by
  rw [spectral, Matrix.star_eq_conjTranspose, Matrix.smul_apply, smul_eq_mul, mul_apply,Fintype.sum_prod_type]
  simp_rw [rot_fiber]; congr 1; apply Finset.sum_congr rfl; intro p _; unfold rotations; rw [sub_eq_add_neg,cell_add]; rw [Finset.sum_eq_single j]
  · simp only [conjTranspose_apply,Matrix.of_apply, ite_true,eq_self,Complex.star_def,cell_bar,cell_inverse]; ring
  · intro b _ h; simp [Ne.symm h]
  simp

def realOf (A : Matrix α β ℂ):= A.map Complex.re
omit [DecidableEq β] [DecidableEq γ] [DecidableEq α] [Fintype α] [Fintype γ] in
lemma realOf_mul (P : Matrix α β ℝ) (A : Matrix β γ ℂ) : realOf (approached P * A)= P * realOf A:= by ext; simp [realOf,approached,Complex.re_sum, Complex.mul_re,Matrix.mul_apply]
omit [DecidableEq β] [DecidableEq γ] [DecidableEq α] [Fintype α] [Fintype γ] in
lemma realOf_mul' (A : Matrix α β ℂ) (P : Matrix β γ ℝ): realOf (A * approached P) = realOf A * P:= by ext; simp [realOf,approached,Complex.re_sum, Complex.mul_re,Matrix.mul_apply]
omit [DecidableEq β] [DecidableEq α] [Fintype α] [Fintype β] in
lemma realOf_adj (A : Matrix α β ℂ) : realOf Aᴴ=(realOf A)ᵀ:= rfl
end spectrum

abbrev curl (m : Side) : Matrix (Body 2 m) (Body 1 m) ℝ := d 1 m
abbrev grad (m : Side) : Matrix (Body 1 m) (Body 0 m) ℝ := d 0 m
lemma d_spectral (m : Side) (k : ℕ) : approached (d k m) = spectral (fun p=> symbol k (mon p)):= by
  apply cancel_rotation; rw [circulant m (cobound k) (cobound_safe k), spectral_read]; simp_rw [reading]
/-- Add longitudinal Feynman term to the free Wilson calculation.
No projection out on this operation. -/
def hessian (m : Side) := (curl m)ᵀ * curl m + grad m * (grad m)ᵀ

theorem hessian_symm (m : Side) : (hessian m)ᵀ=hessian m := by unfold hessian; simp
lemma hessian_reading (m : Side) : approached (hessian m) = spectral (fun p : Site m=> (Torus.lap (mon p) : ℂ) • 1) := by
  unfold hessian; rw [show approached (_ + _ : Matrix (Body 1 m) _ ℝ)=_+_ from plus _ _]; unfold curl grad; simp_rw [prom_mul, prom_adj,d_spectral,spectral_adj,spectral_mul]; rw [spectral_add]; congr! 1; exact funext hessian_gf
where plus {α β : Type} (A B : Matrix α β ℝ) : approached (A+B)=approached A+approached B:= by ext; simp [approached]

def missing (m : Side) : Matrix (Body 1 m) (Body 1 m) ℝ := realOf (spectral (m:=m) (fun p=> if p=0 then 1 else 0))
def pre (m : Side) := realOf (spectral (m:=m) (fun p=> ((Torus.lap (mon p) : ℂ))⁻¹ • (1:Matrix (TypeFace 1) (TypeFace 1) ℂ)))

theorem pre_symm (m : Side) : (pre m)ᵀ = pre m := by unfold pre; rw [← realOf_adj, spectral_adj]; simp

theorem pre_inverts (m : Side) : hessian m * pre m=1-missing m:= by
  unfold pre; rw [← realOf_mul,hessian_reading,spectral_mul]; apply (eq_sub_iff_add_eq).2
  unfold missing; rw [show realOf _ + realOf _=_ from plus _ _,spectral_add]
  have hh (p : Site m) : (((lap (mon p) : ℂ)) • (1:Matrix (TypeFace 1) (TypeFace 1) ℂ))*((lap (mon p):ℂ)⁻¹ • 1)+(if p=0 then 1 else 0)=1:= by
    split
    · subst p; simp [lap,q]
    rename_i h; rw [add_zero, Matrix.smul_mul, Matrix.mul_smul,Matrix.one_mul,smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (positive p h).ne')]
  simp_rw [hh,spectral_unit]; ext i j; by_cases he:i=j <;> simp [realOf,one_apply,he]
where plus {α : Type} (A B : Matrix α α ℂ): realOf A+realOf B=realOf (A+B) := by ext; simp [realOf]

theorem projected (u v : Site m) (i j : TypeFace 1) : missing m (u,i) (v,j)=if i=j then ((m.val:ℝ)^4)⁻¹ else 0 := by
  simp only [missing,realOf, Matrix.map_apply,spectral_apply]; rw [Finset.sum_eq_single 0]
  · rw [if_pos rfl, Matrix.one_apply,cell_duality,cell_origin,one_mul,mul_ite,mul_one,mul_zero]; split_ifs; · rw [show meter m = ↑(((m.val:ℝ)^4)⁻¹) by simp only [meter]; push_cast; rfl]; rfl
    rfl
  · intro k _ he; rw [if_neg he]; simp
  simp

theorem reverse (m : Side) : pre m*hessian m=1-missing m:= by
  rw [← pre_symm,← hessian_symm, ← transpose_mul, pre_inverts, transpose_sub, transpose_one]; congr 1
  ext ⟨u,i⟩ ⟨v,j⟩; simp [projected,eq_comm (a:=i)]

lemma bridge (u v : Cover) (a b : PlaqAxes) (m : Side) :
    kernel m u v a b=(curl m * pre m * (curl m)ᵀ) (wrap m u, plaquette a) (wrap m v,plaquette b):= by
  unfold kernel pre curl; rw [← realOf_mul,← realOf_mul',prom_adj, d_spectral,spectral_adj,spectral_mul,spectral_mul]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, realOf, Matrix.map_apply,spectral_apply]; simp_rw [← map_sub, cell_wrap]; rfl
end YM.MSbar.Tree.Resolvent
