import YM.FVA2.Fourier.Letters
/-! # Range of Master in position space: Landau with the even inversion regulator -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Fourier
open Function Set Finset Lattice
open YM.MS YM.MS.Plane YM.MS.Koszul YM.MS.City YM.MS.Tone YM.MS.Landau YM.MS.Momentum YM.MS.Orbit
open scoped BigOperators Matrix
open Complex (I)
variable {G : Gauge} {n : Side}
local notation "C" => G.ColorIndex
local notation "T" => Site n
local notation "E" => FixedMode G n
local notation "A" => Landau.gauge
local notation "K" => kernel G n true

variable {R : Type} [AddCommGroup R]

/-- Complexification not needed in the definition; orientation is the conventional positive link
at its *starting* point. The ghost constraints mean-zero sum is over the whole torus; a fixed
point contributes only once. K is not an independent species -- it codes the antighost. -/
structure Position (v : E→R) : Prop where
  divergence (c : C) (x : T) : ∑ i, (v ((A i,c),x) - v ((A i,c),x-step i)) = 0
  one_form (c : C) (x : T) (i : Axis) : v ((A i,c),-x-step i) = -v ((A i,c),x)
  even_ghost (c : C) (x : T) : v ((ghost,c),-x) = v ((ghost,c),x)
  mean_ghost (c : C) : ∑ x, v ((ghost,c),x) = 0
  B (c : C) (x : T) : v ((gaugeC,c),x) = 0
  exact_form (c : C) : ∃ f : T → R, (∀ x, f (-x)=f x) ∧ (∑ x, f x)=0 ∧
      ∀ x i, v ((anti i,c),x) = f x - f (x + step i)

variable (v : FixedMode G n → ℂ) (c : G.ColorIndex)
local notation "w" => (toFreq G n *ᵥ v)
local notation "U" => hat n

lemma inv_eq (a : BH G) :
    (∀ p, w (a,-p) = w (a,p) * switch (a,Coord p)) ↔
    (∀ x, sgn a * v (a,-x-shiftBase a) = v (a,x)) := by
  let f x := v (a,x)
  let f' x := sgn a * v (a,-x-shiftBase a)
  have H p : w (a,p) * switch (a,Coord p) = U f' (-p) := by
    rw [show U f' (-p)=_ from hat_inv f a p, pack_hat]; exact mul_comm ..
  simp_rw [H]; constructor
  · intro h; suffices hk : f'=f from congr_fun hk
    apply (hat n).injective
    funext p; rw [← neg_neg p,← h, pack_hat, neg_neg]
  intro h p; rw [show f'=f from funext h, pack_hat]

lemma div_eq : (∀ p : T, ∑ i, freq p i * mid p c w (A i)=0) ↔
    (∀ x : T, ∑ i, (v ((A i,c),x) - v ((A i,c),x-step i)) = 0) := by
  let f i x := v ((A i,c),x)
  let d (x : T) := ∑ i, (f i x - f i (x-step i))
  have h (p:T) : U d p = I * ∑ i, freq p i * mid p c w (A i) := by
    simp_rw [mid,pack_hat, show ∀ i : Axis, flag (A i,c) (Coord p) = midpoint p i from fun _=>rfl]
    exact hat_div f p
  constructor
  · intro he x; exact congr_fun (all_off (f:=d) fun p => by rw [h, he, mul_zero]) x
  intro he p; apply (mul_eq_zero.mp _).resolve_left I_ne
  rw [← h, show d=0 from funext he, map_zero, Pi.zero_apply]
where I_ne : I ≠ 0 := Complex.I_ne_zero

lemma mid_hat_K (i : Axis) (p : T) : mid p c w (anti i) = (midpoint p i)⁻¹ * U (fun x => v ((anti i,c),x)) p := by
  unfold mid; rw [pack_hat]; rfl

lemma of_gradient (f : T→ℂ) (p : T) (i : Axis) :
    (midpoint p i)⁻¹ * U (fun x => f x - f (x + step i)) p = freq p i * (- I * U f p) := by
  rw [hat_grad]; field_simp [midpoint_ne]

private lemma sym_grad (y : T → Axis → ℂ)
    (hf : ∃ f : T → ℂ, (∑ x, f x)=0 ∧ ∀ x i, y x i=f x-f (x+step i))
    (he : ∀ i x, y (-x-step i) i = -y x i) :
    ∃ f : T → ℂ, (∀ x, f (-x)=f x) ∧ (∑ x, f x)=0 ∧ ∀ x i, y x i = f x-f (x+step i) := by
  obtain ⟨f,hf,h⟩ := hf
  let l x := (f x + f (-x))/2
  refine ⟨l,fun i => by simp [l, add_comm],?_,fun x i=>?_⟩
  · unfold l; rw [← Finset.sum_div, Finset.sum_add_distrib, show (∑ x:T, f (-x)) = _ from Equiv.sum_comp (Equiv.neg T) f, hf]; simp
  have hi := he i x
  unfold l; rw [h, show -(x+step i) = -x-step i from by abel]; rw [h,h,sub_add_cancel] at hi
  linear_combination (1/2:ℂ) * hi

lemma get_gradient (ha : ∀ p : T, ∃ z : ℂ, ∀ i, mid p c w (anti i)= freq p i * z) :
    ∃ f : T → ℂ, (∑ x, f x)=0 ∧ ∀ x i, v ((anti i,c),x) = f x - f (x + step i) := by
  choose z hz using ha
  let f := (U).symm (fun p => if p=0 then 0 else I*z p)
  have h p : U f p = if p=0 then 0 else I*z p := by unfold f; rw [LinearEquiv.apply_symm_apply]
  refine ⟨f, ?_, fun x i => ?_⟩
  · apply (mul_eq_zero.mp _).resolve_left (scale_ne n)
    rw [← hat_zero, h, if_pos rfl]
  suffices he : (fun x => v ((anti i,c),x)) = fun x => f x - f (x+step i) from congr_fun he x
  apply (hat n).injective; funext p
  apply mul_left_cancel₀ (inv_ne_zero (midpoint_ne p i)); rw [← mid_hat_K v c, of_gradient f p i, hz, h]
  split
  next he => rw [he, freq_zero, zero_mul, zero_mul]
  next _ => linear_combination freq p i * z p * Complex.I_mul_I

lemma mid_scalar (k : Bool) (p : T) : mid p c w (none,k) = U (fun x => v (((none,k),c),x)) p := by
  rw [mid, pack_hat, scalar_flag, inv_one, one_mul]

theorem position_of_range (H : ∃ x, K *ᵥ x = w) : Position v := by
  obtain ⟨h,hp⟩ := (in_range w).mp H
  constructor
  · exact fun c => (div_eq v c).mp fun p => (h p c).trans
  · intro c x i; have hx := (inv_eq v (A i,c)).mp (hp (A i,c)) x
    change -1 * _ = _ at hx; rw [neg_one_mul] at hx; exact neg_eq_iff_eq_neg.mp hx
  · intro c x; have hx := (inv_eq v (ghost,c)).mp (hp (ghost,c)) x
    change 1 * v ((ghost,c),-x-0) = _ at hx; rwa [sub_zero,one_mul] at hx
  · intro c; apply (mul_eq_zero.mp _).resolve_left (scale_ne n); rw [← hat_zero, ← mid_scalar v c false 0,(h 0 c).removed rfl]; rfl
  · intro c x; refine congr_fun (all_off (f:=fun x=>v ((gaugeC,c),x)) (fun p =>?_)) x
    rw [← mid_scalar]; exact (h p c).closed
  intro c; apply sym_grad _ (get_gradient v c fun p => (h p c).axial)
  intro i x; have hx := (inv_eq v (anti i,c)).mp (hp _) x
  change -1 * _ = _ at hx; rw [neg_one_mul] at hx; exact neg_eq_iff_eq_neg.mp hx

lemma gauge_shadow {R : Type} [AddCommGroup R] {f : T→R} (h : ∀ x : T, f (-x)=f x) (x : T) (i : Axis) :
    f (-x-step i) - f ((-x-step i)+step i)= -(f x-f (x+step i)) := by
  rw [sub_add_cancel, show -x-step i= -(x+step i) from by abel,h,h]; abel

lemma range_of_position (H : Position v) : ∃ x, K *ᵥ x = w := by
  rw [in_range]
  have ht (a : BH G) := (inv_eq v a)
  have h (a : BH G) : ∀ p, w (a,-p) = w (a,p) * switch (a,Coord p) := by
    apply (ht a).mpr; intro x
    rcases a with ⟨⟨_|i,_|_⟩,c⟩
    · change 1 * v ((ghost,c),-x-0) = _; rw [sub_zero, one_mul]; exact H.even_ghost c x
    · change 1 * v ((gaugeC,c), _) = v ((gaugeC,c),_); rw [H.B,H.B,mul_zero]
    · change -1 * v ((A i,c),-x-step i) = v ((A i,c),x); rw [H.one_form]; simp
    change -1 * v ((anti i,c),-x-step i) = v ((anti i,c),x)
    obtain ⟨f,hf,-,hh⟩ := H.exact_form c; rw [hh,hh,gauge_shadow hf]; simp
  refine ⟨fun p c => ⟨(div_eq v c).mpr (H.divergence c) p,?_,?_,?_⟩,h⟩
  · obtain ⟨f, -, -, hh⟩ := H.exact_form c; exact ⟨ _,fun i=> by simp_rw [mid_hat_K,hh]; exact of_gradient f _ _⟩
  · rw [mid_scalar]; simp_rw [H.B]; exact congr_fun (map_zero U) p
  rintro rfl; funext q
  rcases q with ⟨_|i,b⟩
  · rw [mid_scalar, hat_zero]
    cases b
    · change scaleZ n * ∑ x, v ((ghost,c),x) = _; rw [H.mean_ghost, mul_zero]; rfl
    change scaleZ n * ∑ x, v ((gaugeC,c),x) = _; simp [H.B]
  let a : BH G := ((some i,b),c)
  have he := h a 0; rw [switch_at, neg_zero, Bloch.cell_duality 0, Bloch.cell_origin, inv_one,mul_one] at he
  unfold mid; change _ * w (a,0) = 0
  apply mul_eq_zero_of_right
  change w (a,0) = w (a,0) * (-1) at he
  linear_combination (1/2:ℂ)*he

theorem master_position : (∃ x, K *ᵥ x = toFreq G n *ᵥ v) ↔ Position v :=
  ⟨position_of_range v, range_of_position v⟩
end YM.FVA2.Fourier
