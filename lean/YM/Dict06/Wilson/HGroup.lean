import YM.Dict06.Wilson.Section

/-! Color and signed axial permutations (including time reflections) on
literal series. The full orthogonal group acts on continuum Labels, not on
lattice cylinders. Conjugation recorded coefficientwise over fixed real
input link amplitudes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Wil
open PowerSeries Function Series Lattice Wilson Labels Source
open scoped BigOperators Matrix.Norms.Frobenius Topology ContDiff Classical
variable {G : Gauge} {d : ℕ} {F : Frame G d}

/-- Pull on positive-edge exponential coordinates. -/
def pullLog {X : Type*} [AddCommGroup X] [One X] (s : Signed) (x : Four X) (A : Links X G.Color) : Links X G.Color :=
  fun e => oriented A (affine s x e.1) ((posDir e.2).rotate s)
lemma pull_sends {X : Type*} [AddCommGroup X] [One X] (s : Signed) (x : Four X) (A : Links X G.Color) (t:ℝ):
    positive (pullLog s x A) t = pull s x (positive A t) := by
  funext e; apply G.mat_injective
  rw [pull, oriented_exp]; simp [positive,pullLog]

lemma adj_sends {X : Type*} [AddCommGroup X] [One X] (c : G.El) (A : Links X G.Color) (t:ℝ) :
    positive (G.adjoint c ∘ A) t = Lattice.gauge (fun _=>c) (positive A t) := by
  funext e; unfold positive Function.comp Lattice.gauge; rw [← map_smul]; apply G.mat_injective
  rw [G.mat_mul,G.mat_mul,G.mat_inv,G.mat_lieExp,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl

variable (S : SectionData F) {H} (hs : S.Sound H)

private def registry (A : Links ℤ G.Color) : F.Coeff →ₗ[ℂ] PowerSeries ℂ :=
  (MvPolynomial.aeval (ink (restrictLog S.stencil A))).toLinearMap ∘ₗ S.evalC
private lemma book_reg (p : F.Coeff) (A:Links ℤ G.Color) : book S p A= registry S A p := rfl

def stamped (S : SectionData F) (A : Links ℤ G.Color) : F.Coeff →ₗ[ℂ] PowerSeries ℂ :=
   Finset.univ.sum fun i:F.Index=> (LinearMap.proj (R:=ℂ) (φ:=fun _ : F.Index=>ℂ) i).smulRight (letter S i A)
lemma stamped_eq (A : Links ℤ G.Color) (v : F.Coeff) :
    stamped S A v=∑ i : F.Index, v i • letter S i A := by
  unfold stamped; simp
lemma stamp_at (A : Links ℤ G.Color) (v : F.Coeff) (n:ℕ) :
    coeff n (stamped S A v) = ∑ i : F.Index, v i * coeff n (letter S i A) := by
  rw [stamped_eq,map_sum]; simp only [map_smul, smul_eq_mul]

private lemma slots_snap (A : Links ℤ G.Color) (v : F.Coeff) (k:ℕ×ℕ)
    (hv : F.coords.symm v∈ Grade k) (r:ℕ) :
    coeff r (stamped S A v) = coeff (k.2+r) (book S v A) := by
  rw [stamp_at]
  have e : v = ∑ i : F.Index, v i • Pi.single i (1:ℂ) := by ext i; simp [Pi.single_apply]
  conv_rhs => rw [book_reg, e, map_sum,map_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [_root_.map_smul,_root_.map_smul,← book_reg]; by_cases h : k=F.grades i
  · rw [leg_at,h,smul_eq_mul]
  have ht:=F.power_coefficient i h hv; rw [F.coords.apply_symm_apply] at ht
  rw [ht,zero_mul,zero_smul]

include hs
lemma signed_series (s : Signed) (v : F.Coeff) (A : Links ℤ G.Color) :
    book S v (pullLog s 0 A) = book S (F.act s.ortho v) A := by
  simp_rw [← echo_book,pull_sends,hs.Hpart]
lemma signed_letter (s : Signed) (i:F.Index) (A : Links ℤ G.Color) :
    letter S i (pullLog s 0 A) = stamped S A (F.act s.ortho (Pi.single i 1)) := by
  ext1 n
  rw [leg_at,signed_series _ hs, slots_snap _ _ _ (F.grades i)]
  rw [← F.coords_basis,F.act_coords,F.coords.symm_apply_apply]
  have h := gradePart_mem (F.grades i) (tensor s.ortho (F.basis i))
  rwa [gradePart_turn,gradePart_self (F.basis i) _ (F.pure i)] at h
lemma signed_stamp (s : Signed) (v:F.Coeff) (A : Links ℤ G.Color) :
    stamped S (pullLog s 0 A) v = stamped S A (F.act s.ortho v) := by
  have e : v = ∑ i : F.Index, v i • Pi.single i (1:ℂ) := by ext i; simp [Pi.single_apply]
  conv_rhs => rw [e,map_sum,map_sum]
  simp_rw [_root_.map_smul]
  simp only [stamped_eq S (pullLog s 0 A) v, signed_letter _ hs]

lemma real_series (p : F.Coeff) (A:Links ℤ G.Color) (n:ℕ) :
    coeff n (book S (star p) A)=star (coeff n (book S p A)) := by
  simp_rw [← echo_book,hs.ordinary_real,ps_at]
  let f (t : ℝ):= S.evaluate p (positive A t)
  let L:ℂ→L[ℝ] ℂ:= (starL' ℝ : ℂ≃L[ℝ]ℂ).toContinuousLinearMap
  have hf : ContDiffAt ℝ n f 0 := by
    unfold f; simp_rw [echo_exact]; exact ((echo_smooth S p).comp (g:=echo S p) (f:=fun t:ℝ=>t • restrictLog S.stencil A) (contDiff_id.smul contDiff_const)).contDiffAt.of_le le_top
  exact ordinary_map f n hf L
lemma real_letter (i:F.Index) (A:Links ℤ G.Color) (n:ℕ) :
    star (coeff n (letter S i A))=coeff n (letter S i A) := by
  rw [leg_at,←real_series S hs]; have h:star (Pi.single i (1:ℂ):F.Coeff)=Pi.single i 1:=by
    funext j; change star ((Pi.single i (1:ℂ):F.Coeff) j) = _; simp only [Pi.single_apply]; split_ifs <;> simp
  rw [h]
lemma real_stamp (v:F.Coeff) (A:Links ℤ G.Color) (n:ℕ) :
    coeff n (stamped S A (star v))=star (coeff n (stamped S A v)) := by
  rw [stamp_at,stamp_at,star_sum]; apply Finset.sum_congr rfl; intro i _
  rw [star_mul,real_letter S hs,mul_comm]; rfl
lemma color_stamp (v:F.Coeff) (A:Links ℤ G.Color) (c:G.El) :
    stamped S (G.adjoint c ∘ A) v = stamped S A v := by
  ext1 n; rw [stamp_at,stamp_at]; apply Finset.sum_congr rfl; intro i _
  simp_rw [leg_at,← echo_book,adj_sends]
  have h (t : ℝ) := hs.gaugeInvariant (Pi.single i 1) (fun _ : Cover=>c) (positive A t); simp_rw [h]
end YM.Dict06.Wil
