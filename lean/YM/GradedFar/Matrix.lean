import YM.GradedFar.Width
/-!
# Toward detector inversion: exercise the reflected Gram in the exact book

The formal left basis in the bank is the input at zero, output projected over **all** weights
through h. Right basis the correspondingly reflected-conjugate detector `prism` exactly as in
the supplier. Choose the orientation with Far at +1 on the time axis (by `Point.GramP`
and inserted accordingly -- reflecting at midpoint). Estimates prove bounds for converting to
its unit-ball rescaled version to use on the physical measurements. Stability uses a pointwise
margin. No inferred matrix estimate on the *measured* rows in this file.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open MS Dframe O O.Score O.Enh
open scoped Topology BigOperators Classical Matrix ComplexOrder

variable {G : Gauge} {h : ℕ}
namespace Bank
def probe (i : Toon G h) := Read.prism (theory i)
def shrink (i : Toon G h) := (1+width (probe i))⁻¹
def detector (i : Toon G h) := ((shrink i:ℝ):ℂ) • probe i
lemma shrink_pos (i : Toon G h) : 0 < shrink i := inv_pos.mpr (by linarith [width_nn (probe i)])
lemma detector_width (i : Toon G h) : width (detector i) ≤ 1 := by
  rw [detector,width_smul,Complex.norm_real,Real.norm_of_nonneg (shrink_pos _).le,shrink, inv_mul_le_iff₀ (by linarith [width_nn (probe i)] : 0 < 1+width (probe i))]
  linarith

def play (i : Toon G h) : Inputs G (Output h) := fun _ => detector i
lemma plays (i : Toon G h) : Box (play i) 1 := (boxes zero_le_one).2 fun _ => detector_width _
-- keep h measurement cap, promoting if necessary
abbrev wall := RootG

def place (h : ℕ) (B : Both G (Output h) (Output h)) : Sec G h →ₗ[ℂ] Sheet G h :=
    LinearMap.pi fun i => response B (play i)
lemma placed (B : Both G (Output h) (Output h)) (a : Sec G h) (i : Toon G h) :
    place h B a i = B (fun _ => a) (play i) := response_apply ..

def initial (A : Arenas G) (h : ℕ) : Both G (Output h) (Output h) :=
    rawCoeff A (fun _ => le_refl h) (fun _ => le_refl h) (outgoing wall) 0
variable {A : Arenas G} (hr : Ground A)
include hr
lemma maxim (a b : Sec G h) : initial A h (fun _ => a) (fun _ => b) = Maxwell.Free.bond G 0 nail a.val b.val := by
  have hv : outgoing wall ∈ conf (1+1) := ok_wall
  rw [initial, rawCoeff_apply A (d:=Output h) (e:=Output h) (fun _ => le_refl h)
      (fun _ => le_refl h) (outgoing wall) (fun _ => a) (fun _ => b) 0 hv,
    hr h (1+1) ⟨_,hv⟩]
  change Normalize.scene (outgoing wall) _ _ = _
  rw [Normalize.screen, Maxwell.Free.bond_eval]; unfold outgoing wall RootG; rw [O.Enh.lamp]
  apply congrArg (Maxwell.Wick.moment G (Maxwell.Free.pairPoints 0 nail))
  funext i; fin_cases i <;> rfl
lemma stencil (b a : Toon G h) : place h (initial A h) (theory a) b = (shrink b:ℂ)*Read.GramP G h b a := by
  rw [placed, show play b = (fun _ : Fin 1 => (shrink b:ℂ) • probe b) from rfl,
    (initial A h (fun _ => theory a)).map_smul_univ (fun _ => (shrink b:ℂ)) (fun _ => probe b),
    Fin.prod_univ_one, smul_eq_mul]; exact congrArg ((shrink b:ℂ) * ·) (maxim hr (theory a) (probe b))
lemma matrix (a : Sec G h) (b : Toon G h) :
    place h (initial A h) a b = (shrink b:ℂ) * (Read.GramP G h *ᵥ columns G h a) b := by
  have hp : a = ∑ i : Toon G h, columns G h a i • theory i := (all_sig a).symm
  nth_rw 1 [hp]; rw [map_sum, Finset.sum_apply]; simp only [_root_.map_smul, Pi.smul_apply,
    smul_eq_mul, stencil hr]; unfold Matrix.mulVec dotProduct; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _=> by ring

theorem detected : Injective (place h (initial A h)) := by
  intro a b h
  apply (columns G _).injective; apply Matrix.mulVec_injective_iff_isUnit.mpr (Read.positive_unit Read.GramP_pos)
  funext i; replace h := congr_fun h i; rw [matrix hr,matrix hr] at h
  exact mul_left_cancel₀ (show (shrink i:ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr (shrink_pos i).ne') h

omit hr
lemma fully {B : Sec G h →ₗ[ℂ] Sheet G h} (hp : Injective B) : Bijective B := by
  refine ⟨hp, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (LinearEquiv.finrank_eq (columns G h))).1 hp
-- Price the genuine inverse operator under motto below.
def decode (B : Sec G h →ₗ[ℂ] Sheet G h) (hp : Injective B) :=
  (LinearEquiv.ofBijective B (fully hp)).symm

def invPrice (B : Sec G h →ₗ[ℂ] Sheet G h) (hp : Injective B) :=
  ‖(((columns G h).toLinearMap.comp (decode B hp).toLinearMap).toContinuousLinearMap : Sheet G h →L[ℂ] Sheet G h)‖
lemma recovers (B : Sec G h →ₗ[ℂ] Sheet G h) (hp : Injective B) (x : Sec G h) : decode B hp (B x)=x :=
  (LinearEquiv.ofBijective B (fully hp)).symm_apply_apply ..
lemma forward (B : Sec G h →ₗ[ℂ] Sheet G h) (hp : Injective B) (x) : B (decode B hp x)=x :=
  (LinearEquiv.ofBijective B (fully hp)).apply_symm_apply x
lemma margin {B : Sec G h →ₗ[ℂ] Sheet G h} (hp : Injective B) (x : Sec G h) :
    width x ≤ invPrice B hp * ‖B x‖ := by
  let M := ((columns G h).toLinearMap.comp (decode B hp).toLinearMap).toContinuousLinearMap
  calc
    _ = ‖M (B x)‖ := by change _ = width (decode B hp (B x)); rw [recovers]
    _ ≤ _ := M.le_opNorm _
lemma margin_inverse {B : Sec G h →ₗ[ℂ] Sheet G h} {C : ℝ} (hC : 0 ≤ C)
    (H : ∀ a, width a ≤ C*‖B a‖) : ∃ hp : Injective B, invPrice B hp ≤ C := by
  have hp : Injective B := (injective_iff_map_eq_zero B).mpr fun a ha => by
    exact width_eq_zero.mp (le_antisymm ((H a).trans_eq (by simp [ha])) (width_nn _))
  refine ⟨hp, ContinuousLinearMap.opNorm_le_bound _ hC (fun x => ?_)⟩
  change width (decode B hp x) ≤ _; apply le_trans (H _); rw [forward]

include hr in
lemma stable : ∃ b : ℝ, 1 ≤ b ∧ ∃ e : ℝ, 0 < e ∧ ∀ B : Sec G h →ₗ[ℂ] Sheet G h,
    (∀ a, width a ≤ 1 → ‖place h (initial A h) a - B a‖ ≤ e) →
    ∀ x, width x ≤ b*‖B x‖ := by
  let D := place h (initial A h)
  have hd : Injective D := detected hr
  let b := max (invPrice D hd) 1
  have h : 1 ≤ b := le_max_right ..
  have hf (x) : width x ≤ b*‖D x‖ := (margin hd x).trans (by gcongr; apply le_max_left)
  refine ⟨2*b,by linarith,(2*b)⁻¹,by positivity,fun B hb x=>?_⟩
  have hx := row_le (D-B) x
  have hi := row_pay (B:=D-B) (show 0 ≤ (2*b)⁻¹ by positivity) hb
  have he (x) := norm_sub_le_norm_sub_add_norm_sub (D x) (B x) 0
  change ‖D x-B x‖ ≤ _ at hx
  have hy : width x ≤ b * ((2*b)⁻¹ * width x + ‖B x‖) := by
    refine (hf x).trans (mul_le_mul_of_nonneg_left ((?_:‖D x‖ ≤ ‖D x-B x‖+‖B x‖).trans ?_) (by linarith))
    · simpa using he x
    exact add_le_add (hx.trans (mul_le_mul_of_nonneg_right hi (width_nn _))) (le_refl _)
  have hS : b*(2*b)⁻¹=1/2 := by field_simp
  rw [mul_add, ← mul_assoc, hS] at hy; linarith
end Bank
end YM.FVA2.GradedFar
