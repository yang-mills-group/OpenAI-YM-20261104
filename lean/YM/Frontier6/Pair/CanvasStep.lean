import YM.Frontier6.Pair.LowChart

set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Canvas
open Function Lattice Wilson RG Labels Bid Work.G08
open scoped BigOperators
variable {G:Gauge}(C:Levels G)(W:Worth)

def bound (i:ℕ):= W.K (C.clock.J (i+1))
def slope (i:ℕ):ℝ:= 4*(bound C W i)^2
private theorem banked (h:Bank W C) (i:ℕ) :
    let c:= bound C W i; let p:=barunit (C.S.block i)
    let L:ℝ:= (C.S.block i).val
    0≤p ∧ c*p≤1/8 ∧ 2*slope C W (i+1) ≤ L:=by
   intro c p L; let D:= W.K (C.clock.J (i+1)+1); let X:= puffs (C.S.block i)
   let a:= bound C W (i+1); let s:=(C.params (i+1)).columns
   have hx : 100000*D^6*(1+s)^2 ≤ X:= h i
   have hd : 1≤D:= W.prices _
   have hc : c ≤ D:= W.growth (Nat.le_succ _); have hc' : 1 ≤ c:= W.prices _
   have ha : a ≤ D:= W.growth (C.fits.stepSlow _); have ha' : 1 ≤ a:= W.prices _
   have hS : 1≤ s:= (C.params (i+1)).columns_ge
   have hv : 8*D^6 ≤ X:=by
      refine le_trans (le_trans ?_ (le_mul_of_one_le_right (by positivity) (show 1≤(1+s)^2 from one_le_pow₀ (by linarith)))) hx
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
   have he : D ≤ D^6:= by simpa using pow_le_pow_right₀ hd (show 1≤6 by decide)
   have hh:1 ≤ X:=by linarith
   have hL:1 ≤ L:=by unfold L; exact_mod_cast (C.S.block i).property
   refine ⟨pow_nonneg (inv_nonneg.mpr (zero_le_one.trans hh)) _,?_,?_⟩
   · change c * ((X⁻¹)^ (3:ℕ)) ≤ _; rw [inv_pow, ← div_eq_mul_inv]
     apply (div_le_iff₀ (by positivity)).2; linarith only [show X≤X^3 by simpa using pow_le_pow_right₀ hh (show 1≤3 by decide),hv,hc,he]
   have h₂ : a^2 ≤ D^6:= (pow_le_pow_left₀ (zero_le_one.trans ha') ha _).trans (pow_le_pow_right₀ hd (show 2≤6 by decide))
   have h₃ : X ≤ L:= by change L^( (1:ℝ)/8) ≤ L; simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL (by norm_num : (1:ℝ)/8 ≤ 1)
   change 2*(4*a^2) ≤ _; linarith only [h₂,hv,h₃]

variable (h:Bank W C)(i:ℕ){D:ℕ}(F:Labels.Frame G D)(e:ℕ)(x y:F.Coeff){T:F.Coeff≃ₗ[ℂ] F.Coeff}{c:ℝ}
set_option quotPrecheck false
local notation "f"=>F.coeffSize
local notation "w"=> vowel F (C.S.block i)
local notation "V"=> (C.S.block i).val
local notation "A"=> bound C W i
local notation "p"=> barunit (C.S.block i)
local notation "g"=> cut F e
local notation "b"=> shed F e
variable (hT: Push.Local.Leading T.toLinearMap c) (ht: ∀ x,F.coeffSize (T x)≤ bound C W i*F.coeffSize x ∧ F.coeffSize (T.symm x)≤ bound C W i*F.coeffSize x) (hx:F.coeffSize (y-T (vowel F (C.S.block i) x))≤ barunit (C.S.block i) * F.coeffSize (F.core x))
include h hT ht hx
lemma descend_step (he:e<D)(hu:f (b x)≤slope C W (i+1)* f (g x)) : (V:ℝ)^(D-e)* f (g x) ≤ 2*A*f (g y) ∧ f (b y) ≤ slope C W i * f (g y) := by
   have hL: 1 ≤ (V:ℝ):= by exact_mod_cast (C.S.block i).property
   let z:= w x; let L:= f (g z); let t:= f (b z); let D':= f (y-T z)
   have hl:= below_size F e (C.S.block i) x
   obtain ⟨h₀,h₁,h₂⟩:= banked C W h i
   have hA : 1 ≤ A:= W.prices _; have hA': 0≤ A:= zero_le_one.trans hA; have hn:0 ≤ L:= size_nonneg ..; have hp':0 ≤ D':= size_nonneg ..
   have hh : 2*t ≤ L := by
      apply le_trans _ hl; let Y:= (V:ℝ)^(D-(e+1))
      have hY : 0 ≤ Y:=by unfold Y; positivity
      have he': (V:ℝ)^(D-e)= Y * V:=by unfold Y; rw [← pow_succ, show D-(e+1)+1=D-e by omega]
      rw [he']; linarith only [show t ≤ _ from ((above_size F e (C.S.block i) x).trans (mul_le_mul_of_nonneg_left hu hY)),mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₂ hY) (size_nonneg F (g x))] -- expand let?
   have hw:f z = L+t:= pair_size ..
   have hD : A * D' ≤ L/4:= by
      have hf : f (F.core x) ≤ 2*L:=by linarith only [hw, hh, (size_core F x).trans (show f x ≤ f z from (size_vowel F (C.S.block i) x).1),hn]
      have hz : D' ≤ p*(2*L):= hx.trans (mul_le_mul_of_nonneg_left hf h₀)
      linarith only [mul_le_mul_of_nonneg_left hz hA',mul_le_mul_of_nonneg_right h₁ hn]
   have hh₁ : L ≤ 2*A*f (g y):= by
      have he:L≤ A*(f (g y)+D'):= by
         apply (inverse_bill F e z hT (fun x=>(ht x).2)).trans; apply mul_le_mul_of_nonneg_left _ hA'; refine (size_triangle F (g (T z)) (g y)).trans (add_le_add_right ?_ _)
         rw [size_sub_rev, ← map_sub]; exact price_cut F e _
      have hf := mul_nonneg hA' (size_nonneg F (g y)); linarith only [he,hD,hf]
   have hh₂ : f y ≤ 2*A*L:= by
      have ht : f (T z) ≤ A*f z := (ht z).1
      have hz:f z ≤ 3/2*L:=by linarith only [hw,hh]
      have h₄:= size_triangle F y (T z); change f y ≤ _+D' at h₄
      have h₅:= (le_mul_of_one_le_left hp' hA).trans hD; linarith only [h₅,h₄, ht.trans (mul_le_mul_of_nonneg_left hz hA'), le_mul_of_one_le_left hn hA,hn]
   refine ⟨hl.trans hh₁,(price_shed F e _).trans (hh₂.trans ?_)⟩
   exact (mul_le_mul_of_nonneg_left hh₁ (by positivity : 0 ≤ 2*A)).trans_eq (by unfold slope; ring)

omit hT in
lemma transverse_step (hu:g x=0) : f y ≤ 2*A* ((V:ℝ)^(D-(e+1)))* f x:=by
   obtain ⟨h₀,h₁,-⟩:= banked C W h i; have hA : 1 ≤ A:= W.prices _; have hA':0≤A:=by linarith only [hA]
   have hz:f (w x) ≤ (V:ℝ)^(D-(e+1)) * f x := by
      have ht:= above_size F e (C.S.block i) x; rwa [shed_is,shed_is,cut_vowel,hu,show w 0 = 0 from (funext fun i=> by simp [vowel]),sub_zero,sub_zero] at ht
   have hw: p ≤ A:= by linarith only [h₁,hA,le_mul_of_one_le_left h₀ hA] -- arg?
   have hy:= hx.trans (mul_le_mul hw ((size_core ..).trans (size_vowel F (C.S.block i) x|>.1)) (size_nonneg F _) hA')
   linarith only [size_triangle F y (T (w x)), (ht (w x)).1,hy,mul_le_mul_of_nonneg_left hz hA']
end YM.Frontier6.Canvas
