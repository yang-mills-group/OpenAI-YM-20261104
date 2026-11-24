import YM.XSpace.Harmonic

/-!
# Bare Feynman gauge potential on periodic torus (all sizes). Laplace proof.

Using unnormalized real Hessians in unit lattice steps. For normalization of glyphs
and subtraction, tests replacing derivatives of Fourier Green need contact
entries through arbitrary finite stencil, so prove the identity as exact finite sums.
Use before limit or movement.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Potential
open Function Filter Set Lattice Bloch Laurent Exterior Matrix Complex Top
open scoped Topology BigOperators ComplexConjugate ComplexOrder
variable {n: Side}

def q (p:Site n) (i:Axis):= cell p (step i)-1
lemma crossed (p:Site n) (i:Axis): Exterior.q (mon p) i=q p i:=by rw [q,Exterior.q,Bloch.cell_step]
lemma crossed_op (p:Site n) (i:Axis): Exterior.q (-mon p) i=cell p (-step i)-1:=by simp only [Exterior.q,Pi.neg_apply,mul_neg,Complex.exp_neg, cell_inverse,cell_step]
lemma crossed_conj (p:Site n) (i:Axis): Exterior.q (-mon p) i=conj (q p i):=by rw [crossed_op,q,map_sub,map_one,cell_inverse,cell_bar]
lemma crossed_neg (p:Site n) (i:Axis): q (-p) i = conj (q p i) := by rw [q, cell_duality,cell_inverse,cell_duality,q,map_sub,map_one,cell_bar]

def normSquare (p:Site n) := ∑ i : Axis,‖q p i‖^2
lemma delta (p:Site n) : Top.delta (mon p)= ↑(normSquare p):= by
  unfold Top.delta normSquare; rw [Complex.ofReal_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [crossed,crossed_conj,Complex.mul_conj, Complex.normSq_eq_norm_sq]
@[simp] lemma square_origin : normSquare (0:Site n)=0:=by simp [normSquare, Potential.q,Bloch.cell]
lemma square_pos {p:Site n} (h:p≠0):0<normSquare p:=by
  obtain ⟨i,hi⟩:= step_picks p h; exact Finset.sum_pos' (fun _ _=>sq_nonneg _) ⟨i,Finset.mem_univ _,pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hi)) _⟩
lemma square_even (p : Site n): normSquare (-p)=normSquare p:=by unfold normSquare; simp only [crossed_neg,norm_conj]

lemma product (p : Site n) (i:Axis):cell p (step i)*cell p (-step i)=1:=by rw [← cell_add]; simp

def scalar : (Site n → ℝ) →ₗ[ℝ] (Site n → ℝ) := LinearMap.pi fun x=> ∑ i:Axis, (((LinearMap.proj : Site n → ((Site n → ℝ) →ₗ[ℝ] ℝ))) x - ((LinearMap.proj : Site n → ((Site n → ℝ) →ₗ[ℝ] ℝ))) (x+step i) + (((LinearMap.proj : Site n → ((Site n → ℝ) →ₗ[ℝ] ℝ))) x-((LinearMap.proj : Site n → ((Site n → ℝ) →ₗ[ℝ] ℝ))) (x-step i)))
def asc (p:Site n→ℂ) (x:Site n):=∑ i:Axis, (p x-p (x+step i)+(p x-p (x-step i)))
lemma scalar_at (p:Site n→ℝ) (x:Site n): scalar p x=∑ i:Axis,(p x-p (x+step i)+(p x-p (x-step i))):=by unfold scalar; rw [LinearMap.pi_apply,LinearMap.sum_apply]; rfl
lemma asc_real (p:Site n→ℂ) (x:Site n): scalar (fun j=> (p j).re) x= (asc p x).re:=by simp [asc,scalar_at]
lemma asc_freq (p k:Site n) : asc (cell p) k=cell p k * ↑(normSquare p):=by
  rw [← delta,Top.delta,asc,Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [crossed,crossed_op,q,cell_add,sub_eq_add_neg k,cell_add]; linear_combination -cell p k * product p i

def Gc (n:Side) (x:Site n):ℂ:= ((n.val:ℂ)^4)⁻¹*∑ i:Site n, cell i x / (normSquare i:ℂ)
def G (n:Side) (x : Site n) : ℝ:= (Gc n x).re
lemma even (n:Side) (x:Site n): Gc n (-x)=Gc n x:=by
  unfold Gc; congr 1; rw [← Equiv.sum_comp (Equiv.neg (Site n)) (fun i=> cell i x / (normSquare i:ℂ))]; apply Finset.sum_congr rfl; intro i _; simp_rw [Equiv.neg_apply,square_even]; rw [cell_duality (-i),cell_inverse,cell_inverse, cell_duality]
lemma g_real (n:Side)(x:Site n): (G n x:ℂ)=Gc n x:= by
  unfold G; rw [← conj_eq_iff_re]; unfold Gc; simp only [_root_.map_mul,map_inv₀,map_pow,map_natCast,_root_.map_sum,map_div₀,conj_ofReal,cell_bar,← cell_inverse]; exact even n x
lemma poisson_scalarC (p:Site n): asc (Gc n) p=(if p=0 then 1 else 0) - ((n.val:ℂ)^4)⁻¹:=by
  let M:ℂ:= (n.val:ℂ)^4; have hm : M≠0:= pow_ne_zero _ (side_ne n)
  have hx (z:Site n) : Gc n z=∑ i:Site n,(M*(normSquare i:ℂ))⁻¹ * cell i z:=by unfold Gc; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> by dsimp only [M]; simp [div_eq_mul_inv]; ring
  unfold asc; simp_rw [hx, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← _root_.mul_sub, ← _root_.mul_add]; rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; change (∑ i: Site n,(M*(normSquare i:ℂ))⁻¹ * asc (cell i) p) = _; simp_rw [asc_freq]
  let s:= ∑ i : Site n, cell i p; have hs : s = if p=0 then M else 0:= by
    unfold s; split
    next h=> rw [h]; simp [M]
    next h=> simp_rw [cell_duality _ p]; exact sum_cell h
  calc _ = M⁻¹*(s-1) := ?_
       _ = _ := by rw [hs]; split_ifs <;> change _ = _ - M⁻¹ <;> rw [_root_.mul_sub] <;> simp [hm]
  have he : ∀ i:Site n,(M* (normSquare i:ℂ))⁻¹*(cell i p*(normSquare i:ℂ))= if i=0 then 0 else M⁻¹ * cell i p:=by
    intro i; split
    next h=> simp [h]
    next h=> have ht:(normSquare i:ℂ)≠0:= Complex.ofReal_ne_zero.mpr (square_pos h).ne'; field_simp
  simp_rw [he, show ∀ i:Site n, (if i=0 then 0 else M⁻¹*cell i p)= M⁻¹*cell i p - if i=0 then M⁻¹*cell i p else 0 by intro i; split <;> simp,Finset.sum_sub_distrib]; rw [← Finset.mul_sum]; simp [s,cell_duality (0:Site n), _root_.mul_sub]
lemma poisson (p:Site n): (scalar (G n)) p=(if p=0 then 1 else 0) - ((n.val:ℝ)^4)⁻¹:=by
  unfold G; rw [asc_real,poisson_scalarC,← Complex.ofReal_natCast,← Complex.ofReal_pow,← Complex.ofReal_inv]
  split_ifs <;> simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re, Complex.one_re]
end YM.XSpace.Potential
