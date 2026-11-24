import YM.QuadraticLocal.Poetry.Scarf
/-!
# Average but price orientation path.E.Entry.Send to Loan Φ caller
Not larger absolute/majorant. Use on Ritz.Anchor real GRAM analytic Mark only.
Haar formula exact rank of original tape. Material photons keep rank. width linear costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry.Texture
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Push Stationary MeasureTheory Gauge
open Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{k N : ℕ} {n:Side}
local notation "μ"=> G.probHaar
variable (q:Atom G k) (u:G.El)
local notation "I"=> G.ColorIndex
local notation "J"=> Tooth G k
local notation "B"=> EuclideanSpace.basisFun (I) ℝ
local notation "ψ" u:max i:max=> Texture.clip (G:=G) u i
abbrev prob (i j:Tooth G k):ℝ:= ∫ u:G.El, Texture.clip u k i j ∂G.probHaar
def scarf : Atom G k where
 leg := q.leg
 coeff j:= ∑ i: Tooth G k, q.coeff i * prob i j
lemma express (x: Fin k→G.Color): q.poly (fun i=> G.adjoint u (x i))=∑ i:J, q.coeff i*∑ j:J, (ψ u k) i j *∏ a:Fin k,x a (j a):= by unfold Atom.poly; simp_rw [sees u _ x]
local notation "T'"=> Texture.scarf q
lemma pocket (x:Fin k→G.Color): (T').poly x= ∑ i:J,q.coeff i * ∑ j:J, prob i j *∏ a:Fin k,x a (j a):= by unfold Texture.scarf Atom.poly; dsimp only; simp_rw [Finset.sum_mul,Finset.mul_sum,mul_assoc]; exact Finset.sum_comm
set_option maxHeartbeats 200000 in
lemma issuance (x:Fin k→G.Color): (scarf q).poly x= ∫ u:G.El, q.poly (fun i=> G.adjoint u (x i)) ∂μ:= by
 let f(j:Tooth G k)(y:Fin k→ G.Color) := ∏ a:Fin k,y a (j a); let g(i j:Tooth G k)(u:G.El):= Texture.clip u k i j*f j x; have hi(i j): Integrable (g i j) μ:= (hymn k i j).mul_const _;
 have hx : ∀ u:G.El, q.poly (fun i=>G.adjoint u (x i))=∑ i:J,q.coeff i*∑ j:J,g i j u:= fun u=> express ..; simp_rw [hx,pocket]; rw [integral_finsetSum]; swap; · exact fun i _=> (integrable_finsetSum (f:=fun j=> g i j) _ fun j _=> hi i j).const_mul _ -- infer functions
 refine Finset.sum_congr rfl fun i _=> ?_; rw [integral_const_mul, integral_finsetSum]; swap; · exact fun j _=> hi i j
 apply congr_arg (_ * ·); apply Finset.sum_congr rfl; intro j _; unfold g; rw [integral_mul_const]
lemma keeps : (scarf q).Invariant:= by
 intro u x; rw [issuance,issuance]; simp_rw [← G.adjoint_mul]; exact integral_mul_right_eq_self («μ»:= G.probHaar) (fun t=> q.poly (fun i=> G.adjoint t (x i))) u
variable (P: G.El→₀ℝ)(h:Spray G P N)
include h
lemma economy : ∑ i∈P.support,P i=1:= by
 let z (i:Fin 0): G.ColorIndex:=Fin.elim0 i; have he:= h 0 (Nat.zero_le _) z z; simpa [clip] using he.symm
lemma song (u:Fin k → G.Color)(hk:k≤N): (scarf q).poly u=∑ x∈ P.support,P x* q.poly (fun i=> G.adjoint x (u i)):= by
 rw [pocket]; simp_rw [prob,h k hk,Finset.sum_mul,express, Finset.mul_sum]; conv_rhs => rw [Finset.sum_comm]
 apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; -- tricky shifts see errors
 refine Finset.sum_congr rfl (fun j _=>Finset.sum_congr rfl fun v _=>?_); ring
omit h
lemma fee (k:ℕ)(i j:Tooth G k) : |prob i j| ≤ 1:= by simpa using norm_integral_le_of_norm_le_const («μ»:= G.probHaar) (f:= fun u=>Texture.clip u k i j) (ae_of_all _ (fun i'=>bill k i j i'))
lemma mag_nonneg :0≤q.magnitude:= Finset.sum_nonneg fun _i _=>abs_nonneg _
local notation "N₁"=> (G.lieDim+1:ℕ)
lemma budget : (scarf q).magnitude ≤ Fintype.card (Tooth G k)*q.magnitude:= by
 unfold Atom.magnitude Texture.scarf
 apply le_trans (Finset.sum_le_sum (g:=fun i=> q.magnitude) _) (le_of_eq (by simp [Atom.magnitude])); intro i _; exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _=> by change |q.coeff j * prob j i|≤ _; rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (fee k j i)))
end YM.QuadraticLocal.Poetry.Texture
