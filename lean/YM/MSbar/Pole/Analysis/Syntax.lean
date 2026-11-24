import YM.MSbar.Pole.Analysis.Bounds

/-! Composition and costs absorbed by enough derivatives of hard amplitudes. -/
noncomputable section
set_option autoImplicit false
namespace YM.MSbar.Pole
open Function Set
open scoped ContDiff Topology BigOperators

variable {E A F G H : Type} [NormedAddCommGroup E]
  [NormedAddCommGroup A] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  [NormedSpace ℝ E] [NormedSpace ℝ A] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
variable {s t : Set E} {grow fast b : Price E} {f g : E → F}

section elementary
omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedSpace ℝ F]
-- combined spatial growth index
instance : Mul (Price E) := ⟨fun x y => ⟨fun i => x i*y i, fun i => one_le_mul_of_one_le_of_one_le (x.large i) (y.large i)⟩⟩
@[simp] lemma mul_price (p q : Price E) (x) : (p*q) x = p x * q x := rfl
@[simp] lemma mul_one_price (p : Price E) : p*1=p := by
  rcases p with ⟨p,hp⟩; change Price.mk (fun i => p i*1) _ = _; simp
def Price.back (p : Price E) (q : A→E) : Price A := ⟨fun x => p (q x), fun _ => p.large _⟩
@[simp] lemma Price.back_apply (p : Price E) (q : A→E) (x) : p.back q x=p (q x) := rfl
lemma Bills.pull {U : Set A} {T : A→E} (h : Bills s grow fast f) (ht : MapsTo T U s) : Bills U (grow.back T) (fast.back T) (f ∘ T) := by
  intro k; obtain ⟨C,e,hc,h⟩ := h k; exact ⟨C,e,hc,fun x hx => h _ (ht hx)⟩
lemma Bills.pow {f : E → ℝ} (h : Bills s grow 1 f) (n : ℕ) : Bills s grow 1 (fun x => f x^n) := by
  induction n with
  | zero => simpa using (Bills.const (1 : ℝ))
  | succ n ih => simpa only [pow_succ] using (ih.mul h)
lemma Bills.spend {f g : E → ℝ} (hf : Bills s grow fast f) (hg : Bills s (grow*fast) 1 g) : Bills s grow fast (f*g) := by
  obtain ⟨C,e,hc,hg⟩ := hg 0; intro k; obtain ⟨D,w,hd,hf⟩ := hf (k+e)
  refine ⟨D*C,w+e,mul_nonneg hd hc,fun x hx => ?_⟩
  have ha : ‖g x‖ ≤ C * (grow x)^e * (fast x)^e := by simpa only [pow_zero,mul_one,mul_price,mul_pow,mul_assoc] using hg x hx
  rw [Pi.mul_apply,norm_mul,mul_right_comm,pow_add,mul_mul_mul_comm D]
  refine (mul_le_mul_of_nonneg_left ha (mul_nonneg (norm_nonneg _) (pow_nonneg (fast.pos _).le _))).trans ?_
  rw [mul_comm _ (fast x^e),← mul_assoc,mul_assoc ‖f x‖,← pow_add]; exact mul_le_mul_of_nonneg_right (hf x hx) (mul_nonneg hc (pow_nonneg (grow.pos _).le _))
/-- bound by own price. -/
lemma Bills.self : Bills s grow 1 (fun x => grow x) := fun k => ⟨1,1,zero_le_one,by simp [Real.norm_of_nonneg (grow.pos _).le]⟩
lemma Bills.bounded {C : ℝ} (hc : 0≤C) (hv : ∀ x∈s, ‖f x‖ ≤ C) : Bills s grow 1 f := by
  refine (Bills.const (s:=s) (grow:=grow) C).dominates (fun x hx => ?_); simpa [Real.norm_of_nonneg hc] using hv _ hx
end elementary

namespace Packet
/-- Product jet bound uses strictly chosen lower orders only. -/
lemma spendAt {g : E → G} {n : ℕ}
    (sf : ∀ x∈s, ContDiffAt ℝ n f x) (hf : ∀ i ≤ n, Bills s grow fast (iteratedFDeriv ℝ i f))
    (sg : ∀ x∈s, ContDiffAt ℝ n g x) (hg : ∀ i ≤ n, Bills s (grow*fast) 1 (iteratedFDeriv ℝ i g)) (L : F →L[ℝ] G →L[ℝ] H) :
    Bills s grow fast (iteratedFDeriv ℝ n (fun x => L (f x) (g x))) := by
  let w : ℕ → E → ℝ := fun i x => (n.choose i) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖
  have hw (i : ℕ) (hi : i∈Finset.range (n+1)) : Bills s grow fast (w i) := by
    simp_rw [w,mul_comm (↑(n.choose _) : ℝ)]
    exact (((hf i (by simpa using hi)).norm.mul (Bills.const _)).spend (hg (n-i) (by omega)).norm)
  have hz := (Bills.sum (Finset.range (n+1)) w hw).mul (Bills.const ‖L‖)
  refine hz.dominates (fun x hx => ?_)
  obtain ⟨t,ht,ho,hy⟩ := mem_nhds_iff.mp (((sf x hx).eventually (by simp)).and ((sg x hx).eventually (by simp)))
  have hh := L.norm_iteratedFDerivWithin_le_of_bilinear (s:=t) (ho.contDiffOn_iff.mpr fun _ hh => (ht hh).1)
    (ho.contDiffOn_iff.mpr fun _ hh => (ht hh).2) ho.uniqueDiffOn hy (n:=n) (by exact le_rfl)
  simp_rw [iteratedFDerivWithin_of_isOpen _ ho hy] at hh
  dsimp
  rw [mul_comm _ ‖L‖]
  exact hh.trans (le_abs_self _)
lemma localn (h : Packet s grow fast f) (n : ℕ) {x : E} (hx : x ∈ s) : ContDiffAt ℝ n f x :=
  (h.smooth x hx).of_le (by exact_mod_cast (show (↑n:ℕ∞) ≤ ⊤ from le_top))
lemma spending {g : E → G} (hf : Packet s grow fast f) (hg : Packet s (grow*fast) 1 g) (L : F →L[ℝ] G →L[ℝ] H) :
    Packet s grow fast (fun x => L (f x) (g x)) :=
  ⟨fun x hx => L.isBoundedBilinearMap.contDiff.contDiffAt.comp x ((hf.smooth x hx).prodMk (hg.smooth x hx)),
    fun n => spendAt (fun _ hx => hf.localn n hx) (fun i _ => hf.budget i)
      (fun _ hx => hg.localn n hx) (fun i _ => hg.budget i) L⟩
lemma mul {f g : E → ℂ} (hf : Packet s grow fast f) (hg : Packet s grow 1 g) : Packet s grow fast (f*g) := hf.bilinear hg (ContinuousLinearMap.mul ℝ ℂ)
lemma mul_spending {f g : E → ℂ} (hf : Packet s grow fast f) (hg : Packet s (grow*fast) 1 g) : Packet s grow fast (f*g) := hf.spending hg (ContinuousLinearMap.mul ℝ ℂ)
lemma built (hv : Function.HasTemperateGrowth f) (hh : Bills s grow 1 (fun x => ticket (@id E) x)) : Packet s grow 1 f := by
  apply Packet.growing (grow:=ticket (@id E)) _ hh
  refine ⟨fun x _ => hv.1.contDiffAt,fun n k => ?_⟩
  obtain ⟨j,C,hc,h⟩ := hv.norm_iteratedFDeriv_le_uniform n
  exact ⟨C,j,hc,by simpa using (fun x (_ : x∈s) => h n (le_refl n) x)⟩
lemma const (c : F) : Packet s grow 1 (fun _ => c) := by
  refine ⟨fun _ _ => contDiffAt_const,fun n k => ?_⟩; cases n with
  | zero => exact ⟨‖c‖,0,norm_nonneg _,by simp⟩
  | succ n => exact ⟨0,0,le_rfl,by intro x _; rw [iteratedFDeriv_const_of_ne (by omega)]; simp⟩
lemma jets (h : Packet s grow fast f) (i : ℕ) : Packet s grow fast (iteratedFDeriv ℝ i f) := by
  induction i generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp]; exact h.apply (X:=(continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap)
  | succ n ih =>
    let X := (continuousMultilinearCurryRightEquiv' ℝ n E F).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact Packet.congr (g:=iteratedFDeriv ℝ (n+1) f) ((ih h.fderiv).apply (X:=X)) (fun _ _ => Filter.Eventually.of_forall fun _ => iteratedFDeriv_succ_eq_comp_right)
lemma neg (h : Packet s grow fast f) : Packet s grow fast (-f) := by
  exact h.apply (X:=-(ContinuousLinearMap.id ℝ F))
lemma sub (hf : Packet s grow fast f) (hg : Packet s grow fast g) : Packet s grow fast (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using! hf.add hg.neg

section Comp
variable {T : A→E} {U : Set A} {p q : Price A} (hf : Packet s grow fast f)
  (ht : MapsTo T U s) (hp : Bills U p 1 (fun x => grow (T x))) (hq : Bills U (fast.back T) 1 q.val)
  (hT : Packet U (p*q) 1 T)
include hf ht hp hq hT
private lemma compUp (n : ℕ) : ∀ i ≤ n, Bills U p q (iteratedFDeriv ℝ i (f ∘ T)) := by
  induction n generalizing F with
  | zero =>
    rintro _ hh; rw [Nat.eq_zero_of_le_zero hh]
    have hb := (hf.values.pull ht).growing hp|>.weakening hq
    exact hb.dominates (by simp)
  | succ n ih =>
    intro i hi; rcases eq_or_lt_of_le hi with hi|hi
    · subst i
      let f₁ := (_root_.fderiv ℝ f) ∘ T
      let L := ContinuousLinearMap.compL ℝ A E F
      let P (x : A) := L (f₁ x) (_root_.fderiv ℝ T x)
      have he : Bills U p q (iteratedFDeriv ℝ n P) :=
        spendAt (fun z hz => (hf.fderiv.localn n (ht hz)).comp z (hT.localn n hz))
          (ih hf.fderiv) (fun z hz => hT.fderiv.localn n hz) (fun i _ => hT.fderiv.budget i) L
      refine he.dominates (fun x hx => ?_)
      have hs := (hf.localn 1 (ht hx)).eventually (by simp)
      have hs' := (hT.localn 1 hx).eventually (by simp)
      have hr : _root_.fderiv ℝ (f ∘ T) =ᶠ[nhds x] P := by
        filter_upwards [(hT.localn 1 hx).continuousAt.preimage_mem_nhds hs, hs'] with y hy hv
        have hy : ContDiffAt ℝ (↑(1:ℕ):WithTop ℕ∞) f (T y) := hy
        exact _root_.fderiv_comp y (hy.differentiableAt (by simp)) (hv.differentiableAt (by simp))
      rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.norm_map,(hr.iteratedFDeriv ℝ n).eq_of_nhds]
    exact ih hf i (by omega)
lemma comp : Packet U p q (f ∘ T) :=
  ⟨fun x hx => (hf.smooth _ (ht hx)).comp x (hT.smooth x hx), fun i => compUp hf ht hp hq hT i i le_rfl⟩
end Comp
end Packet
end YM.MSbar.Pole
