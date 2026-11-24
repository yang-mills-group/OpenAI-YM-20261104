import YM.RG12.Frames.Tests

/-! # Stability and adjacent measurements from quadratic Gram tests (e.g. reflected)

Even on the moving pivot family, don't need positive lower tests over a whole range of k vs IR
for this implication. Nor a path-ordered solution or full coefficient identification. Require
an independent leading form on the pivot family, and a dilation comparison up to a relative
consecutive-log ratio correction, here realized by *cancellation of the terms of orders zero
and one*. This is far below core physical comparison precision, but requires actual data at
all these scales: not claiming to supply those hypotheses by just composing endpoints of
existence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Frames.Gram
open Function Finset Filter
open scoped Topology BigOperators
variable {d : ℕ} {V : Grade d → Type} [∀ i, NormedAddCommGroup (V i)] [∀ i, NormedSpace ℂ (V i)]
variable {F E : Type} [AddCommGroup F] [Module ℂ F]

/-- Only the diagonal part of a polarization is consumed. E.g. take the real part of a
reflection sesquilinear reading. -/
structure Square (F : Type) [AddCommGroup F] [Module ℂ F] where
  eval : F → ℝ
  cross : F → F → ℝ
  zero : eval 0 = 0
  joint (x y : F) (t : ℝ) : eval (x+(t:ℂ) • y)=eval x + t * cross x y + t^2 * eval y
  scale (x : F) (t : ℝ) : eval ((t:ℂ) • x)=t^2 * eval x

abbrev Sesqui (F : Type) [AddCommGroup F] [Module ℂ F] := F →ₗ[ℂ] (F →ₛₗ[starRingEnd ℂ] ℂ)

def fromSesqui (P : Sesqui F) : Square F where
  eval x := (P x x).re
  cross x y := (P x y).re+(P y x).re
  zero := by rw [map_zero]; rfl
  joint x y t := by
    simp only [map_add,LinearMap.add_apply,map_smul P,LinearMap.smul_apply,map_smulₛₗ (P x),map_smulₛₗ (P y),Complex.conj_ofReal, smul_eq_mul,Complex.add_re,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]; ring
  scale x t := by simp only [map_smul P,LinearMap.smul_apply,map_smulₛₗ (P x),Complex.conj_ofReal,smul_eq_mul,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]; ring

lemma Square.precombine (P : Square F) (Y : Col V →ₗ[ℂ] F)
    (h : ∀ x, 0 ≤ P.eval (Y x)) (x y) :
    Real.sqrt (P.eval (Y (x+y))) ≤ Real.sqrt (P.eval (Y x)) + Real.sqrt (P.eval (Y y)) := by
  let X:= Real.sqrt (P.eval (Y x)); let U:= Real.sqrt (P.eval (Y y)); let Z:=Real.sqrt (P.eval (Y (x+y)))
  let c:= P.cross (Y x) (Y y)
  have hx : X^2=P.eval (Y x):= Real.sq_sqrt (h _); have hu : U^2 =P.eval (Y y):=Real.sq_sqrt (h _); have hz : Z^2=P.eval (Y (x+y)):= Real.sq_sqrt (h _)
  have hp : Z^2=X^2+c+U^2:=by rw [hz,map_add, ← one_smul ℂ (Y y), ← Complex.ofReal_one,P.joint, hx, hu, one_pow,one_mul,one_mul]
  have hh(t:ℝ) := h (x+(t:ℂ) • y)
  have he(t:ℝ) : 0 ≤ X^2 +t*c+t^2*U^2:=by rw [hx,hu]; specialize hh t; rwa [map_add,map_smul,P.joint] at hh
  have hXN:0 ≤ X:= Real.sqrt_nonneg _; have hn :0 ≤ U:=Real.sqrt_nonneg _
  change Z ≤ X+U
  suffices ht : c ≤ 2*X*U by nlinarith only [hp, hXN,hn, Real.sqrt_nonneg (P.eval (Y (x+y))),ht]
  rcases eq_or_lt_of_le hn with hh|hu
  · have hp(t:ℝ):0 ≤ X^2 +t*c:=by simpa only [← hh, ne_eq,OfNat.ofNat_ne_zero, not_false_eq_true,zero_pow,mul_zero,add_zero] using he t
    by_contra! hel
    have hc:0<c:=by simpa [← hh] using hel
    have he:=hp (-((1+X^2)/c)); rw [neg_mul, div_mul_cancel₀ _ hc.ne'] at he; linarith
  rcases eq_or_lt_of_le hXN with hh|hx
  · specialize he (-c/(2*U^2))
    field_simp at he
    rw [← hh]; rw [← hh] at he; nlinarith [he]
  specialize he (-X/U)
  field_simp at he
  -- XU * c <= 2X²U², divide
  nlinarith only [he,hx,hu,mul_pos hx hu]

/-- Leading reflected matrix on the independent pivot blocks, uncorrected measurements at a
single length. K in this criterion bounds squared-norm costs. -/
structure Regular (P : Square F) (Y : Col V →ₗ[ℂ] F) (K : ℝ) : Prop where
  legal : 1 ≤ K
  upper x : P.eval (Y x) ≤ K * ‖x‖^2
  coerc x : ‖x‖^2 ≤ K * P.eval (Y x)

theorem stable {P : Square F} {Y : Col V →ₗ[ℂ] F} {K : ℝ} (h : Regular P Y K) :
    Tests (Real.sqrt ∘ P.eval ∘ Y) K := by
  have hk:=h.legal; have ht:=zero_lt_one.trans_le hk
  have hn(x : Col V):0≤ P.eval (Y x):= nonneg_of_mul_nonneg_right ((sq_nonneg _).trans (h.coerc x)) ht
  let N x:= Real.sqrt (P.eval (Y x)); have hs (x): N x^2=P.eval (Y x):=Real.sq_sqrt (hn x); have hp(x):0≤N x:= Real.sqrt_nonneg _
  refine ⟨hk, fun x=> ?_, fun x=> ?_, fun x y=> P.precombine Y hn x y, fun c x he=> ?_⟩
  · change N x≤ _
    have hc:=mul_le_mul_of_nonneg_right (show K ≤ K^2 by simpa using le_self_pow₀ hk (by decide : 2≠0)) (sq_nonneg ‖x‖)
    nlinarith [hs x,h.upper x,hp x,norm_nonneg x,mul_nonneg ht.le (norm_nonneg x)]
  · change _ ≤ K*N x
    have hc:=mul_le_mul_of_nonneg_right (show K ≤ K^2 by simpa using le_self_pow₀ hk (by decide : 2≠0)) (hn x)
    apply le_of_pow_le_pow_left₀ (n:=2) (by norm_num) (mul_nonneg ht.le (hp x)); nlinarith only [(h.coerc x).trans hc,hs x] -- rewrite
  dsimp only [Function.comp_apply]; rw [map_smul,P.scale, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq he]
end YM.RG12.Frames.Gram
