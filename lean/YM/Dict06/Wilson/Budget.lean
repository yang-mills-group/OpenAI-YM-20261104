import YM.Dict06.Wilson.PowerRead
import YM.Dict06.Series.Partial

/-!
Explicit symmetrized root-list presentation on positive-link coordinates.
Polynomial and exponential widths can be fixed before any block length:
the displayed cost at a fixed finite horizon uses only the actual source
stencil, Frame and expansion order. Covers arbitrarily large fixed moment
power and width. Not a cost to evolve these packets, or a residual norm
on masked densities. Derivatives here are ordinary Fréchet derivatives in
log-link arrays.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Finance
open Wil Tensor Function Set Lattice Wilson Labels Source
open scoped BigOperators Topology ContDiff Classical
variable {G : Gauge}{d n : ℕ}{F:Frame G d}

abbrev Root (Y:Finset Cover)(G:Gauge):=UsedEdges Y × G.ColorIndex
def reach (y:Cover):ℝ:=∑ i:Axis,(y i).natAbs
-- include both endpoints
def cost {Y:Finset Cover}(i:Root Y G):ℝ:=1+reach i.1.val.1+reach (i.1.val.1+step i.1.val.2)
lemma reach_nonneg (y:Cover):0≤reach y:=Finset.sum_nonneg fun _ _=>by exact_mod_cast Nat.zero_le _
lemma reach_axis (y:Cover)(a:Axis) : (|(y a:ℝ)| : ℝ) ≤ reach y:=by
  exact (show |(y a : ℝ)| = ((y a).natAbs : ℝ) by simp).trans_le (Finset.single_le_sum (fun i _=> (show (0:ℝ)≤ ((y i).natAbs:ℝ) from by exact_mod_cast Nat.zero_le _)) (Finset.mem_univ a))
lemma unit_cost {Y:Finset Cover}(i:Root Y G):1 ≤ cost i:=by unfold cost; linarith [reach_nonneg i.1.val.1, reach_nonneg (i.1.val.1+step i.1.val.2)]

variable {Y:Finset Cover}
def factor (σ:ℝ) (u:ℕ)(i:Root Y G):=Real.exp (σ*cost i)*cost i^u
lemma factor_nonneg (σ:ℝ)(u)(i:Root Y G):0≤factor σ u i:=by unfold factor; have :=unit_cost i; positivity
lemma supplies {σ:ℝ}(hs:0≤σ)(u)(i:Root Y G):1≤factor σ u i:=by
  have h:=unit_cost i; have he :=Real.exp_le_exp.mpr (mul_nonneg hs (le_trans zero_le_one h)); rw [Real.exp_zero] at he
  exact one_le_mul_of_one_le_of_one_le he (one_le_pow₀ h)

def leg (A:Panel Y G)(i:Root Y G):ℝ:=A i.1 i.2
def kick (i:Root Y G):Panel Y G:= Pi.single i.1 ((EuclideanSpace.basisFun G.ColorIndex ℝ) i.2)
lemma all (x:Panel Y G):x=∑ i:Root Y G, leg x i • kick i:=by
  funext i
  rw [Finset.sum_apply,Fintype.sum_prod_type]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp only [leg,kick,Pi.smul_apply,Pi.single_eq_same]; exact Eq.symm ((EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (x i))
  intro j _ hj; simp [kick,Ne.symm hj]

abbrev Chain (Y:Finset Cover)(G:Gauge)(n:ℕ):= Fin n→Root Y G
def fee (T:Tensor.T (Panel Y G) ℂ n)(σ:ℝ)(u:ℕ):ℝ :=
   ∑ w:Chain Y G n, (∏i,factor σ u (w i))* ‖T (kick ∘ w)‖
lemma fee_nonnegative (T:Tensor.T (Panel Y G) ℂ n)(σ:ℝ)(u):0≤fee T σ u:=
   Finset.sum_nonneg fun _ _=>mul_nonneg (Finset.prod_nonneg (fun _ _=>factor_nonneg σ u _)) (norm_nonneg _)
lemma emits (T:Tensor.T (Panel Y G) ℂ n)(x:Fin n→Panel Y G):
    T x=∑ v:Chain Y G n,(∏ i,leg (x i) (v i)) • T (kick ∘ v):=by
  calc
    _ = T (fun i=>∑ j:Root Y G,leg (x i) j • kick j):= congrArg T (funext fun i=>all _)
    _ = _:=by
      rw [T.map_sum_finset (fun i j=>leg (x i) j • kick j) (fun _=>Finset.univ),Fintype.piFinset_univ]; apply Finset.sum_congr rfl; intro i _
      exact T.map_smul_univ _ (kick ∘ i)

def Test (σ:ℝ)(u:ℕ)(t:ℝ)(x:Panel Y G):Prop:= ∀ i:Root Y G, |leg x i| ≤ t*factor σ u i
lemma bound (T:Tensor.T (Panel Y G) ℂ n)(σ:ℝ)(u)(t:ℝ)(x:Fin n→Panel Y G)(he:∀ i,Test σ u t (x i)): ‖T x‖ ≤ fee T σ u * t^n:=by
  rw [emits T x]
  refine (norm_sum_le _ _).trans ?_; unfold fee; rw [Finset.sum_mul]
  apply Finset.sum_le_sum;intro w _
  rw [norm_smul, Real.norm_eq_abs,Finset.abs_prod]; rw [mul_comm _ (t^n), ←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [show t^n = ∏ _ : Fin n,t by simp, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod (fun i _=>abs_nonneg _) fun i _=>he i _

lemma through (T:Tensor.T (Panel Y G) ℂ n)(hT:Tensor.Sym T)(σ:ℝ)(u)(t:ℝ)(x:Panel Y G)(he:Test σ u t x)(j:ℕ)(v:Fin j→Panel Y G)(hv:∀ i,Test σ u t (v i)) :
   ‖iteratedFDeriv ℝ j (Tensor.diagonal T) x v‖ ≤ n.descFactorial j * (fee T σ u * t^n) := by
  obtain ⟨w,hw,h⟩:=Series.all_dirs T hT x v (Test σ u t) he hv
  rw [h,nsmul_eq_mul, norm_mul]; simp only [Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (bound T σ u t w hw) (by positivity)

variable (S:SectionData F)
/-- Polynomial link-field packet test in the actual root budget.
All derivative orders, all σ, and t even scale-varying at an admitted
horizon. Price uses that horizon, pre-block, no schedule constants. The
power t^n is available under **all direction and center bounds** he,hv;
it is not a bound t^n on unscaled-link derivatives.
-/
theorem invoice (i:F.Index)(r j:ℕ)(σ:ℝ)(u)(t:ℝ)(A:Panel S.stencil G)(w:Fin j→Panel S.stencil G)
   (he:Test σ u t A)(hv:∀ i,Test σ u t (w i)):
   let n:=(F.grades i).2+r
   ‖iteratedFDeriv ℝ j (fun x=>PowerSeries.coeff r (letter S i (widen S x))) A w‖ ≤ (n.descFactorial j:ℝ)*(fee (author S (Pi.single i 1) n) σ u * t^n):=by
  intro n
  simp_rw [leg_at,reported,restrict_inverse]
  apply through _ (Tensor.coeff_symm ((echo_smooth S _).contDiffAt.of_le le_top)) _ _ _ _ he j w hv

end YM.Dict06.Finance
