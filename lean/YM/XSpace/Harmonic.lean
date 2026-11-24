import YM.Work.E01
import YM.Push.LOOP_COEFFICIENT.ExteriorRules
import YM.XSpace.TopFourier
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Free Wilson curl covariance is discrete harmonic outside distance two

A cheap useful property for position estimates with the chosen regulator. All
entries are with incidence normalization (not `SU n` conventions). See
`Top.projector`. `Exterior` indexing: positive axes of plaquettes, counting
measure. Math shortcut: Hodge-Laplace has the correct width with **ordinary**
unweighted metric. Do it directly by a Kronecker product identity using the
already verified orientation comparisons `Push.Loops.wedge_dual`. (We don't
appeal to a general theorem about continuum-limit free Green kernels.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Harmonic
open Lattice Filter Exterior Matrix Function Push.Loops
open scoped Topology BigOperators Kronecker
variable (n : Side)
abbrev Table := Matrix (Site n) (Site n) ℝ

def translation (x : Site n): Table n := Matrix.of fun a b => if b=a+x then 1 else 0
lemma along (x : Site n) (f : Site n →ℝ) (w : Site n): (translation n x *ᵥ f) w=f (w+x):=by simp [translation, Matrix.mulVec,dotProduct,ite_mul]
lemma back (x : Site n): (translation n x)ᵀ=translation n (-x):=by
  ext i j; unfold translation; simp only [Matrix.of_apply, Matrix.transpose_apply]; have he : i=j+x ↔ j=i+ -x:=by constructor <;> intro h <;> rw [h] <;> abel;
  simp only [he]
lemma trans_zero : translation n 0=1:=by ext i j; simp [translation, Matrix.one_apply, eq_comm]
lemma trans_mul (x y : Site n): translation n x*translation n y=translation n (x+y):= by
  apply Matrix.ext_iff_mulVec.mpr; intro v; ext1 w; rw [← Matrix.mulVec_mulVec,along,along, along,add_assoc]

abbrev forward (i : Axis) := translation n (step i) - 1
def plate (i : Axis) (r : ℕ):= (forward n i) ⊗ₖ (left ℝ r i)
lemma kron (r : ℕ) : Exterior.d r n = ∑ i:Axis, plate n i r := by
  ext u v; rw [Matrix.sum_apply]; apply Eq.trans (acts_apply r n u v); refine Finset.sum_congr rfl (fun i _=>?_); rw [mul_comm]
  unfold plate forward translation; obtain ⟨x,y⟩:=u; obtain ⟨z,w⟩:=v; simp [Matrix.one_apply,eq_comm (a:=z)]

lemma forwards_comm (i j : Axis): (forward n i)ᵀ*(forward n j)=(forward n j)*(forward n i)ᵀ:= by
  unfold forward; rw [Matrix.transpose_sub, Matrix.transpose_one, back]
  simp only [_root_.sub_mul,_root_.mul_sub,one_mul,mul_one]; rw [trans_mul,trans_mul,add_comm (-step i)]; abel
lemma returns (i : Axis): (forward n i)*(forward n i)ᵀ = 1+1-(translation n (step i)+translation n (-step i)):= by
  unfold forward; rw [Matrix.transpose_sub, Matrix.transpose_one, back]; simp only [_root_.sub_mul,_root_.mul_sub,one_mul,mul_one]; rw [trans_mul,add_neg_cancel,trans_zero]; abel

lemma plate_pair (i j : Axis) (r : ℕ): (plate n j (r+1))ᵀ*plate n i (r+1) + plate n i r *(plate n j r)ᵀ =
    if i=j then (forward n i*(forward n i)ᵀ)⊗ₖ (1: Matrix (TypeFace (r+1)) (TypeFace (r+1)) ℝ) else 0 := by
  have ht {α β γ δ : Type} (A : Matrix α β ℝ) (B : Matrix γ δ ℝ) : (A⊗ₖ B)ᵀ = Aᵀ⊗ₖ Bᵀ := (Matrix.kroneckerMap_transpose (·*·) A B).symm
  dsimp only [plate]; rw [ht,ht, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, forwards_comm,← Matrix.kronecker_add]
  have hp:=wedge_dual ℝ (Pi.single j 1) i (r:=r)
  have hs (k): wedge k (Pi.single j (1:ℝ))=left ℝ k j:= by simp [wedge, Pi.single_apply,ite_smul,eq_comm]
  set A:= (left ℝ (r+1) j)ᵀ * left ℝ (r+1) i+left ℝ r i * (left ℝ r j)ᵀ
  have he (v) : A *ᵥ v=(Pi.single j (1:ℝ) (M:=fun _ => ℝ) i) • v:= by unfold A; rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,← hs, ← hs]; exact hp v
  split
  next h=> subst j; rw [show A=1 from Matrix.ext_iff_mulVec.mpr (fun v=> by rw [he]; simp)]
  next h=> rw [show A=0 from Matrix.ext_iff_mulVec.mpr (fun v=> by rw [he]; simp [h]),Matrix.kronecker_zero]

def Lap (r : ℕ) : Matrix (Body r n) (Body r n) ℝ:= ∑ i:Axis, (forward n i*(forward n i)ᵀ)⊗ₖ (1:Matrix (TypeFace r) (TypeFace r) ℝ)
lemma hodge (r : ℕ): (Exterior.d (r+1) n)ᵀ * Exterior.d (r+1) n + Exterior.d r n*(Exterior.d r n)ᵀ = Lap n (r+1) :=by
  rw [kron,kron,Matrix.transpose_sum,Matrix.transpose_sum,Matrix.mul_sum, Matrix.sum_mul];
  simp_rw [Matrix.sum_mul, Matrix.mul_sum]; rw [← Finset.sum_add_distrib]; simp only [← Finset.sum_add_distrib,plate_pair,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]; rfl

lemma lap_projector : Lap n 2 * Top.projector n = Exterior.d 1 n * (Exterior.d 1 n)ᵀ:=by
  let P:=Top.projector n; let D:=Exterior.d 1 n; let L:=Exterior.d 2 n
  have ht : Dᵀ * Top.projector n=Dᵀ:= by rw [← (Top.projection n).1]; exact Eq.trans (Matrix.transpose_mul P D).symm (congr_arg Matrix.transpose (Top.projection n).2.2)
  obtain ⟨w,hw⟩:=(Top.projection n).2.1
  rw [← hodge n 1, Matrix.add_mul]
  change (Lᵀ*L)*P+(D*Dᵀ)*P=D*Dᵀ
  rw [Matrix.mul_assoc D Dᵀ,ht,Matrix.mul_assoc,show L*P=0 from ?_,Matrix.mul_zero,zero_add]; dsimp only [P]; rw [hw,← Matrix.mul_assoc]; simp [L,Exterior.closed]

lemma forward_touches (x y : Site n) (h : 1< separation x y) (i : Axis) : forward n i x y=0:= by
  have he:x≠y:=fun H=> by rw [H,separation_self] at h; omega
  have H:y≠x+step i:=fun H=> by rw [H] at h; exact (not_lt.mpr (Work.E01.sep_step_le _ _)) h
  simp [forward,translation,H,he]
lemma d_touches (r : ℕ) (x : Body (r+1) n) (y : Body r n) (h : 1<separation x.1 y.1): Exterior.d r n x y=0:=by
  obtain ⟨x,i⟩:=x; obtain ⟨y,j⟩:=y; rw [kron,Matrix.sum_apply]; exact Finset.sum_eq_zero fun i _=> by rw [plate,Matrix.kronecker_apply, forward_touches _ _ _ h,zero_mul]
lemma local_free (x y : Body 2 n) (h : 2<separation x.1 y.1) : (Exterior.d 1 n*(Exterior.d 1 n)ᵀ) x y=0:=by
  apply Finset.sum_eq_zero; intro (z : Body 1 n) _; change Exterior.d 1 n x z * Exterior.d 1 n y z=_
  by_cases p: 1< separation y.1 z.1
  · rw [d_touches _ _ _ _ p,mul_zero]
  rw [d_touches _ _ _ _ (by have hT:=separation_triangle x.1 z.1 y.1; rw [separation_comm z.1] at hT; omega),zero_mul]

lemma lap_value (r : ℕ) (f : Body r n → ℝ) (x : Site n) (i : TypeFace r):
    (Lap n r *ᵥ f) (x,i) = ∑ j: Axis,(f (x,i)-f (x+step j,i)+(f (x,i)-f (x-step j,i))):=by
  rw [Lap,Matrix.sum_mulVec,Finset.sum_apply]; refine Finset.sum_congr rfl fun j _=> ?_
  have he : ∀ A : Table n,(Matrix.mulVec (A⊗ₖ(1:Matrix (TypeFace r) (TypeFace r) ℝ)) f) (x,i)=(A *ᵥ fun z=> f (z,i)) x := by intro A; simp [Matrix.mulVec,Fintype.sum_prod_type,dotProduct,Matrix.one_apply,mul_ite,ite_mul]
  rw [he,returns, Matrix.sub_mulVec, Matrix.add_mulVec,Matrix.add_mulVec]; simp only [Pi.add_apply, Pi.sub_apply, Matrix.one_mulVec,along]; rw [sub_eq_add_neg x]; abel
lemma harmonic_point (x : Site n) (a : TypeFace 2) (y : Body 2 n) (h : 2<separation x y.1) :
    (∑ j: Axis,(Top.projector n (x,a) y - Top.projector n (x+step j,a) y +(Top.projector n (x,a) y - Top.projector n (x-step j,a) y)))=0:=by
  rw [← lap_value n 2 (fun z=>Top.projector n z y) x a]; change (Lap n 2*Top.projector n) (x,a) y=0; rw [lap_projector]; exact local_free n _ _ h
end YM.XSpace.Harmonic
