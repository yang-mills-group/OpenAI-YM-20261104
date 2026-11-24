import YM.Integration.WilsonVacuumPreResetFiniteHeatBudget
import YM.WilsonCoeffUV.Step.Source

/-! The inhomogeneous finite heat acting on a genuinely marked input. There are
two drift cross terms and one normalized original unmarked heat. The field-rank
zero coefficient stays in the return. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentFiniteHeat
open Function Finset Lattice Laurent Wilson RG Precision WilsonCoeffUV WilsonCoeffUV.Blue
open WilsonVacuumPreResetFiniteHeatBudget (sum line join)
open scoped BigOperators Classical
variable {U:Type}[Fintype U]

private theorem cross (cap limit k i r:ℕ)(K:Matrix U U ℝ)(E F:Layers ℝ U)
    (B M:ℝ)(base:1≤B)(pos:0≤M)(room:∀v:ℕ,v≤cap+2 → (v:ℝ)≤B)(dim:(Fintype.card U:ℝ) ≤ B)
    (matrix:∀a z,|K a z|≤B)(ic:i≤limit)(lc:limit≤cap)(rc:r+2*(k+1)≤cap)
    (quiet:∀a≤k,∀v≤limit,∀l,l+2*a≤cap → ∀x,|E a v l x|≤M)
    (row:∀a≤k,∀v≤limit,∀l,l+2*a≤cap → ∀x,|F a v l x|≤M)(x):
    |ravel K E F k i r x|≤B^8*M^2:=by
  have bp:=zero_le_one.trans base
  simp only [ravel,Finset.sum_apply]
  calc
    _≤B*(B*(B^6*M^2)):=by
      apply sum _ _ (by positivity) (by simpa using room (k+1) (by omega))
      intro a ha
      have eq:a.1+a.2=k:=by simpa using ha
      apply sum _ _ (by positivity) (by simpa using room (i+1) (by omega))
      intro z hz
      have split:z.1+z.2=i:=by simpa using hz
      exact join K _ _ r base pos (room _ (by omega)) dim matrix
        (fun l hl y=>quiet a.1 (by omega) z.1 (by omega) l (by omega) y)
        (fun l hl y=>row a.2 (by omega) z.2 (by omega) l (by omega) y) x
    _=B^8*M^2:=by ring

/-- Native unnormalized size of the finite linear source heat on the actual
quiet background, with a torus-polynomial cost independent of spatial width. -/
theorem through (cap limit:ℕ)(lc:limit≤cap)(K:Matrix U U ℝ)(P T:ℕ→Gen ℝ U)(B:ℝ)(base:2≤B)
    (width:((cap+2:ℕ):ℝ)≤B)(dim:(Fintype.card U:ℝ)≤B)(matrix:∀a z,|K a z|≤B)
    (quiet:∀i≤limit,∀l≤cap,∀x,|P i l x|≤B)(row:∀i≤limit,∀l≤cap,∀x,|T i l x|≤B):
    ∀h i r,i≤limit → r+2*h≤cap → ∀x,|bul K (abr K P) T h i r x|≤B^(20*3^h):=by
  have b:1≤B:=by linarith
  have bp:=zero_le_one.trans b
  have room(v:ℕ)(le:v≤cap+2):(v:ℝ)≤B:=(by exact_mod_cast le:(v:ℝ)≤((cap+2:ℕ):ℝ)).trans width
  have original:=WilsonVacuumPreResetFiniteHeatBudget.through cap limit lc K P B base width dim matrix quiet
  intro h
  induction h using Nat.strong_induction_on with
  | h n ih=>
    intro i r ic rc x
    cases n with
    | zero=>
      rw [bul_zero]
      exact (row i ic r (by omega) x).trans (le_self_pow₀ b (by norm_num))
    | succ k=>
      let M:=B^(20*3^k)
      have high:1≤M:=one_le_pow₀ b
      have mp:=zero_le_one.trans high
      have older:∀a≤k,∀v≤limit,∀l,l+2*a≤cap → ∀y,|abr K P a v l y|≤M:=by
        intro a age v hv l hl y
        apply (original a v l hv hl y).trans
        exact pow_le_pow_right₀ b (Nat.mul_le_mul (by decide) (Nat.pow_le_pow_right (by decide) age))
      have prev:∀a≤k,∀v≤limit,∀l,l+2*a≤cap → ∀y,|bul K (abr K P) T a v l y|≤M:=by
        intro a age v hv l hl y
        apply (ih a (by omega) v l hv hl y).trans
        exact pow_le_pow_right₀ b (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) age))
      have diffusion:=line K (bul K (abr K P) T k i) r b mp (room _ (by omega)) dim matrix
        (fun y=>prev k le_rfl i ic (r+2) (by omega) y) x
      have drift (K':Matrix U U ℝ)(pay:∀a z,|K' a z|≤B):=
        cross cap limit k i r K' _ _ B M b mp room dim pay ic lc rc older prev x
      have tiny:B^5*M≤B^8*M^2:=mul_le_mul (pow_le_pow_right₀ b (by decide))
        (le_self_pow₀ high (by decide)) mp (pow_nonneg bp _)
      have clipped:|((k+1:ℕ):ℝ)⁻¹|≤1:=by
        rw [abs_of_nonneg (by positivity)]
        exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
      have both:=add_le_add ((abs_add_le ..).trans (add_le_add diffusion (drift K matrix)))
        (drift K.transpose (fun a z=>matrix z a))
      simp only [bul_next,Pi.smul_apply,Pi.add_apply,smul_eq_mul,abs_mul]
      calc
        _≤1*(B^5*M+B^8*M^2+B^8*M^2):=mul_le_mul clipped ((abs_add_le ..).trans both) (abs_nonneg _) zero_le_one
        _≤B^2*(B^8*M^2):=by
          have four:3≤B^2:=by nlinarith
          have h:=mul_le_mul_of_nonneg_right four (by positivity:0≤B^8*M^2)
          linarith
        _=B^(10+(20*3^k)*2):=by simp only [M,pow_mul,pow_add];ring
        _≤_:=by
          apply pow_le_pow_right₀ b
          rw [pow_succ]
          have positive:0<3^k:=Nat.pow_pos (by decide)
          omega

private theorem scaled (K:Matrix U U ℝ)(E:Layers ℝ U)(T:ℕ→Gen ℝ U)(a:ℝ)(h i r:ℕ)(x):
    bul K E (a • T) h i r x=a*bul K E T h i r x:=by
  let f:ℝ→ₗ[ℝ]ℝ:=a • LinearMap.id
  exact (congrFun (congrFun (cloak_bul f K E T h i) r) x).symm

/-- The signed marked input carries its small parameter exactly once even at
an arbitrarily high angular or coupling order. -/
theorem original (cap limit:ℕ)(lc:limit≤cap)(K:Matrix U U ℝ)(P T:ℕ→Gen ℝ U)(B η:ℝ)(base:2≤B)(hot:0<η)
    (width:((cap+2:ℕ):ℝ)≤B)(dim:(Fintype.card U:ℝ)≤B)(matrix:∀a z,|K a z|≤B)
    (quiet:∀i≤limit,∀l≤cap,∀x,|P i l x|≤B)(row:∀i≤limit,∀l≤cap,∀x,|T i l x|≤η*B):
    ∀h i r,i≤limit → r+2*h≤cap → ∀x,|bul K (abr K P) T h i r x|≤η*B^(20*3^h):=by
  let W:=η⁻¹ • T
  have test:∀i≤limit,∀l≤cap,∀x,|W i l x|≤B:=by
    intro i hi l hl x
    change |η⁻¹*T i l x|≤B
    rw [abs_mul,abs_of_pos (inv_pos.mpr hot)]
    have b:=mul_le_mul_of_nonneg_left (row i hi l hl x) (inv_pos.mpr hot).le
    simpa only [←mul_assoc,inv_mul_cancel₀ hot.ne',one_mul] using b
  have bound:=through cap limit lc K P W B base width dim matrix quiet test
  intro h i r hi hr x
  have id:T=η • W:=by simp only [W,smul_smul,mul_inv_cancel₀ hot.ne',one_smul]
  rw [id,scaled,abs_mul,abs_of_pos hot]
  exact mul_le_mul_of_nonneg_left (bound h i r hi hr x) hot.le

end YM.Integration.WilsonMarkedIndependentFiniteHeat
end
