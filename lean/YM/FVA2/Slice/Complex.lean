import YM.FVA2.Slice.Coordinates

/-! # Master Fourier range is the complex span of the real Landau-gauge directions -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Slice
open Function Set Finset Lattice Pert Orb
open MS MS.Plane MS.Koszul MS.City MS.Orbit MS.Tone MS.Landau
open Complex (I)
open Fourier
open scoped BigOperators Matrix
variable {G : Gauge} {n : Side}
local notation "E" => FixedMode G n
local notation "C" => G.ColorIndex
local notation "A" => MS.Landau.gauge
local notation "K" => Fourier.kernel G n true

section
variable {R S : Type} [AddCommGroup R] [AddCommGroup S]
lemma position_map {v : E→R} (h : Fourier.Position v) (f : R →+ S) :
    Fourier.Position (f ∘ v) where
  divergence c x := by simp only [comp_apply, ← map_sub f, ← map_sum, h.divergence c x, map_zero]
  one_form c x i := by simp only [comp_apply,h.one_form,map_neg]
  even_ghost c x := congr_arg f (h.even_ghost c x)
  mean_ghost c := by simp only [comp_apply, ← map_sum, h.mean_ghost, map_zero]
  B c x := by simp only [comp_apply,h.B,map_zero]
  exact_form c := by
    obtain ⟨y,he,hy,hw⟩ := h.exact_form c; refine ⟨f ∘ y, fun x=>congr_arg f (he x),?_,?_⟩
    · simp only [comp_apply,← map_sum,hy,map_zero]
    intro x i; simp only [comp_apply,hw,map_sub]
lemma position_add {v w : E→R} (h : Fourier.Position v) (H : Fourier.Position w) :
    Fourier.Position (v+w) where
  divergence c x := by
    simp only [Pi.add_apply,add_sub_add_comm,Finset.sum_add_distrib,h.divergence,H.divergence,add_zero]
  one_form c x i := by simp only [Pi.add_apply,h.one_form,H.one_form,neg_add]
  even_ghost c x := congr_arg₂ (·+·) (h.even_ghost c x) (H.even_ghost c x)
  mean_ghost c := by simp only [Pi.add_apply, Finset.sum_add_distrib, h.mean_ghost, H.mean_ghost, add_zero]
  B c x := by simp only [Pi.add_apply,h.B,H.B,add_zero]
  exact_form c := by
    obtain ⟨v,hv,hv',hf⟩ := h.exact_form c; obtain ⟨w,hw,hw',hg⟩ := H.exact_form c
    refine ⟨v+w,fun x=>congr_arg₂ (·+·) (hv x) (hw x),?_,?_⟩
    · simp only [Pi.add_apply,Finset.sum_add_distrib,hv',hw',add_zero]
    intro x i; simp only [Pi.add_apply,hf,hg,add_sub_add_comm]
end

theorem re_im (v : E→ℂ) : Fourier.Position v ↔ Fourier.Position (Complex.re ∘ v) ∧ Fourier.Position (Complex.im ∘ v) := by
  let f := Complex.ofRealHom.toAddMonoidHom
  constructor
  · intro h; exact ⟨position_map h Complex.reCLM.toLinearMap.toAddMonoidHom,
                     position_map h Complex.imCLM.toLinearMap.toAddMonoidHom⟩
  rintro ⟨h,h'⟩; apply Eq.mp _ (position_add (position_map h f)
    (position_map h' ((LinearMap.mulLeft ℂ I).toAddMonoidHom.comp f)))
  congr 1; funext i; change ((v i).re:ℂ)+ I * (v i).im = v i; rw [mul_comm, Complex.re_add_im]

variable {J : Type} [Fintype J]
variable (B : Module.Basis J ℝ (Directions G n))

def placeMatrix : Matrix E J ℂ := Matrix.of fun i j => fieldDir G n (B j) i

def basisMatrix := toFreq G n * placeMatrix B

omit [Fintype J] in
lemma basis_unpack : toSite G n * basisMatrix B = placeMatrix B := by rw [basisMatrix, ← Matrix.mul_assoc, unpack_pack, Matrix.one_mul]

lemma place_real_part (x : J→ℂ) : Complex.re ∘ (placeMatrix B *ᵥ x) = fieldDir G n (∑ j, ((x j).re) • B j) := by
  funext i; unfold Matrix.mulVec dotProduct
  simp only [placeMatrix, comp_apply, Matrix.of_apply, map_sum, map_smul, Pi.smul_apply,
    Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm ..
lemma place_imag_part (x : J→ℂ) : Complex.im ∘ (placeMatrix B *ᵥ x) = fieldDir G n (∑ j, ((x j).im) • B j) := by
  funext i; unfold Matrix.mulVec dotProduct
  simp only [placeMatrix, comp_apply, Matrix.of_apply, map_sum, map_smul, Pi.smul_apply,
    Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm ..

lemma place_matrix_real (v : E → ℂ) : (∃ x, placeMatrix B *ᵥ x = v) ↔ Fourier.Position v := by
  rw [re_im]; constructor
  · rintro ⟨x,rfl⟩; rw [place_real_part,place_imag_part]; exact ⟨in_position _,in_position _⟩
  rintro ⟨he,hq⟩; obtain ⟨i,hi⟩ := position_real he; obtain ⟨t,ht⟩ := position_real hq
  let x (j : J) : ℂ := ⟨B.repr i j,B.repr t j⟩
  refine ⟨ x,?_⟩
  have heck : ∑ j, (x j).re • B j = i := B.sum_repr i
  have imck : ∑ j, (x j).im • B j = t := B.sum_repr t
  have h_re : Complex.re ∘ (placeMatrix B *ᵥ x) = Complex.re ∘ v := by rw [place_real_part,heck,hi]
  have h_im : Complex.im ∘ (placeMatrix B *ᵥ x) = Complex.im ∘ v := by rw [place_imag_part,imck,ht]
  funext j; exact Complex.ext (congr_fun h_re j) (congr_fun h_im j)

lemma place_matrix_inj (x y : J→ℂ) (h : placeMatrix B *ᵥ x = placeMatrix B *ᵥ y) : x=y := by
  classical
  have hre := place_real_part B x
  have him := place_imag_part B x
  rw [h,place_real_part B y] at hre; rw [h, place_imag_part B y] at him
  have hr (f g : J→ℝ) (h : fieldDir G n (∑ j, g j • B j) = fieldDir G n (∑ j, f j • B j)) : f=g := by
    have he := congr_arg B.equivFun (field_inj h); funext i
    simpa only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,Module.Basis.equivFun_self, smul_eq_mul, mul_ite, mul_one,
      mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using (congr_fun he i).symm
  funext i; exact Complex.ext (congr_fun (hr _ _ hre) i) (congr_fun (hr _ _ him) i)

lemma basis_matrix_inj (x y : J → ℂ) (h : basisMatrix B *ᵥ x = basisMatrix B *ᵥ y) : x=y := by
  apply place_matrix_inj B; rw [← basis_unpack B, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h]

lemma basis_range (v : E→ℂ) : (∃ x, K *ᵥ x = v) ↔ (∃ x, basisMatrix B *ᵥ x = v) := by
  let y := toSite G n *ᵥ v
  have h : toFreq G n *ᵥ y = v := by unfold y; rw [Matrix.mulVec_mulVec,pack_unpack,Matrix.one_mulVec]
  rw [← h,master_position y, ← place_matrix_real B]; constructor
  · rintro ⟨x,hx⟩; exact ⟨x,by rw [basisMatrix,← Matrix.mulVec_mulVec,hx]⟩
  rintro ⟨x,hx⟩; exact ⟨x,by rw [h] at hx; unfold y; rw [← hx,Matrix.mulVec_mulVec,basis_unpack]⟩

end YM.FVA2.Slice
