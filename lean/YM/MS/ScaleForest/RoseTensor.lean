import YM.MS.ScaleForest.RoseInput
import YM.MS.ScaleForest.QuarticRule
import YM.Integration.FVA1Physical.Exchange.CalibratedExpansionMarkedQuarticTensor

/-!
# Chiral mark ↔ the projected tensor integrated in the one-loop reading

Use `gradient` in the larger auxiliary space, so also calculate correctly for
loop integration where the momentum needn't lie only in the physical four
axes. In particular contracting with the two separate Landau propagators
costs none of their longitudinal parts. This is not a projection to a D
scalar. Even the final pole computation on this four-axis tensor will use the
fixed continuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest.Quadratic
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum Motif Literal Halo
open Lattice Momentum XSpace XSpace.Chiral Cylinder
open scoped Topology ContDiff InnerProductSpace
variable {G : Gauge} {m : ℕ}

/-- The real momentum factors from a normalized-axis convention with
**Rose.f omitted**. `bare_tensor` below includes it again. -/
def gradient (σ : Bool) (i : P) (p : SectorP m) (s : L m) : ℝ :=
  ∑ a : PlaqAxes, q σ i (six a) (endr a) *
    polar0 (chair m (six a)) (chair m (endr a)) s p

theorem oneColor_rank (σ : Bool) (p : P) (a : G.ColorIndex) : rank 1 (oneColor (m:=m) 0 σ p a) := by
  unfold oneColor cur; simp only [zero_smul,add_zero]; exact Rails.sum _ fun j _=> (rank_α _ _ a).smul _

theorem survives (σ : Bool) (i : P) (s : L m) (a c : G.ColorIndex) (p : SectorP m) :
    oneColor 0 σ i a [vec s c p] = if c=a then Complex.I * (gradient σ i p s : ℝ) else 0 := by
  simp only [oneColor, cur,zero_smul, add_zero, Finset.sum_apply, vec, f_ref, Pi.smul_apply,smul_eq_mul]
  split <;> rename_i h
  · simp only [gradient, Complex.ofReal_sum,Complex.ofReal_mul, Finset.mul_sum ]; refine Finset.sum_congr rfl ?_
    intro k _; exact mul_left_comm ..
  simp

theorem polar_transverse (p : SectorP m) (i j : L m) : ∑ s : L m, p s * polar0 i j s p = 0 := by
  simp only [polar0,Landau.delta,mul_sub,Finset.sum_sub_distrib]
  simp [mul_ite,mul_comm]

theorem gradient_transverse (p : SectorP m) (i : P) (σ : Bool) : ∑ s : L m, p s * gradient σ i p s = 0 := by
  unfold gradient; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_eq_zero fun a _ => ?_
  simp_rw [mul_left_comm _ (q σ i _ _), ← Finset.mul_sum, polar_transverse,mul_zero]

theorem polar_gradient (p : SectorP m) (i : P) (σ : Bool) (t : L m) :
    (∑ s:L m, precision t s p * gradient σ i p s) = p.sq * gradient σ i p t := by
  unfold precision Landau.delta; simp only [sub_mul, mul_assoc,Finset.sum_sub_distrib, ← Finset.mul_sum,gradient_transverse,
    mul_zero,sub_zero]
  simp [ite_mul]

theorem polar_neg (s k : L m) (p : SectorP m) (i : L m) : polar0 s k i (-p) = -polar0 s k i p := by
  simp only [polar0,Landau.delta,Pi.neg_apply]
  split_ifs <;> ring

theorem gradient_neg (p : SectorP m) (i : P) (σ : Bool) (s : L m) : gradient σ i (-p) s = - gradient σ i p s := by
  simp only [gradient,polar_neg,mul_neg,Finset.sum_neg_distrib]

@[simp] theorem gradient_zero (i : P) (σ : Bool) (s : L m) : gradient σ i 0 s = 0 := by
  have ht := gradient_neg (0:SectorP m) i σ s
  rw [neg_zero] at ht; linarith

theorem oneColor_gauge (σ : Bool) (i : P) (a : G.ColorIndex) : Uses (setOf isA) (oneColor (m:=m) 0 σ i a) := by
  intro l j hj hh
  by_cases hp : l.length = 1
  · obtain ⟨p,rfl⟩ := List.length_eq_one_iff.mp hp
    rw [List.mem_singleton] at hj; subst p
    obtain ⟨j,p⟩:= j
    unfold oneColor cur; simp only [zero_smul,add_zero,Finset.sum_apply, Pi.smul_apply,c_α,
      show ∀ i k, j ≠ at_g i k from fun i k h=> hh ⟨_,_,h⟩, if_false, mul_zero,sub_self, smul_zero,
      Finset.sum_const_zero]
  exact oneColor_rank σ i a l (by rw [mod_int]; omega)

theorem onlyGauge : GaugeLegs (roseMark G 0).symbol := by
  intro m; rw [bare_vertex]; exact Uses.smul _ (Uses.smul _ (Uses.sum fun i _=> Uses.pair (oneColor_gauge _ _ _) (oneColor_gauge _ _ _)))

/-- Two A derivatives. Negative sign is the two factors of I; there is no 1/2
left over from the mark there. -/
def incoming (s t : L m) (p r : SectorP m) : ℂ :=
  - (Rose.f:ℂ)^2 * ∑ i : P, ((gradient false i p s : ℝ):ℂ) * (gradient false i r t : ℝ)

theorem bare_tensor (s t : L m) (a c : G.ColorIndex) (p r : SectorP m) :
    (roseMark G 0).symbol m [vec s a p,vec t c r] = if c=a then incoming s t p r else 0 := by
  rw [bare_vertex]
  simp only [Finset.sum_apply, Pi.smul_apply, bite, pairv (oneColor_rank _ _ _) (oneColor_rank _ _ _),
    survives, show field parity (vec s a p) = false from rfl, cross_false,one_mul,smul_eq_mul,Fintype.sum_prod_type]
  split
  · next he=>
      subst c; unfold incoming; simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [Finset.sum_eq_single a]
      · simp only [if_true]; ring_nf; rw [Complex.I_sq]; ring
      · intro j _ h; simp [Ne.symm h]
      simp
  next he=>
    simp_rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun i _=> Finset.sum_eq_zero fun j _=> ?_
    by_cases h : a=j
    · subst j; simp [he]
    simp [h]

theorem gradient_phys (p : SectorP m) (i : P) (σ : Bool) (s : Axis) :
    gradient σ i p (chair m s) = ∑ j : Axis, p (chair m j) * q σ i j s := by
  let X (a b : Axis) := if b=s then p (chair m a)*q σ i a s else 0
  have hj : ∑ j : Axis,∑ k:Axis, X k j = ∑ j:Axis,p (chair m j)*q σ i j s := by rw [Finset.sum_comm]; simp [X]
  rw [← hj,Gland.order_poly X]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rcases k with ⟨⟨a,b⟩, h⟩
    have hu : ∀ a b : Axis, chair m a=chair m b ↔ a=b := fun a b=>(rises _).injective.eq_iff
    simp only [polar0,Landau.delta,hu,X,six,endr]; by_cases ha : a=s <;> by_cases hb : b=s
    · exact False.elim ((show a<b from h).ne (ha.trans hb.symm))
    · simp only [ha,hb,if_true,if_false]; rw [chosen_sqrt2 σ i b s]; ring
    · simp [ha,hb,mul_comm]
    simp [ha,hb]
  intro j; unfold X; split; next h=> subst j; rw [qdiag,mul_zero]
  rfl

theorem gradient_extra (p : SectorP m) (i : P) (σ : Bool) (t : L m) (ht : ∀ s:Axis, chair m s ≠ t) :
    gradient σ i p t = 0 := by
  simp [gradient,polar0,Landau.delta,ht]

theorem chair_same (i j : Axis) : chair m i = chair m j ↔ i=j := (rises _).injective.eq_iff

open Integration.FVA1Physical.Exchange.RoseQuartic

def GramEntry (mu a b : Axis) : ℝ := ↑(projectedGram mu a b)
def projected (mu : Axis) (p v : SectorP m) :=
  ∑ a: Axis, ∑ b: Axis, GramEntry mu a b * p (chair m a) * v (chair m b)

theorem gram_lift (mu a b : Axis) : GramEntry mu a b=∑ i:P,∑ j:Axis,if j=mu then 0 else q false i a j * q false i b j := by
  unfold GramEntry projectedGram q; push_cast; rfl

theorem gram_eval (mu a b : Axis) : GramEntry mu a b = if a=b then (if a=mu then 3 else 2) else 0 := by
  rw [GramEntry, projectedGram_eq]; split_ifs <;> norm_cast

theorem projected_contraction (mu : Axis) (p v : SectorP m) :
    ∑ i:P, ∑ s:L m, (if s = chair m mu then 0 else gradient false i p s * gradient false i v s) = projected mu p v := by
  have hC (s : Apart 0 m) (j : Axis) : chair m j ≠ aside (Nat.zero_le m) s := nowhere _ _ _
  let K(i:P)(s:Axis) a b := if s=mu then (0:ℝ) else q false i a s * q false i b s * p (chair m a) * v (chair m b)
  have hv (i:P) : ∑ s:L m, (if s = chair m mu then 0 else gradient false i p s * gradient false i v s) =
      ∑ s:Axis,∑ a:Axis,∑ b:Axis,K i s a b := by
    rw [cut_sum (Nat.zero_le m), Finset.sum_eq_zero (s:=Finset.univ (α:=Apart 0 m)) (fun s _=> ?_)]
    · rw [add_zero]; apply Finset.sum_congr rfl; intro s _
      change (if chair m s= _ then (0:ℝ) else gradient false i p (chair m s)*gradient false i v (chair m s))=_
      by_cases he : s = mu
      · subst s; simp [K]
      rw [if_neg (mt (chair_same s mu).mp he), gradient_phys, gradient_phys]; unfold K; simp_rw [Finset.sum_mul,
        Finset.mul_sum, if_neg he]; exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _=> by ring))
    rw [gradient_extra _ i _ (aside (Nat.zero_le m) s) (fun j => hC s j)]; simp
  simp_rw [hv]; unfold projected; simp_rw [gram_lift, Finset.sum_mul]
  let V (i:P×Axis) (j:Axis×Axis) := K i.1 i.2 j.1 j.2
  have H : ∑ i:P×Axis,∑ j:Axis×Axis,V i j=∑ j:Axis×Axis,∑ i:P×Axis,V i j := Finset.sum_comm
  simpa only [Fintype.sum_prod_type,V,K,ite_mul,zero_mul] using H
end YM.MS.ScaleForest.Quadratic
