import YM.Integration.WilsonVacuumPreResetWindingPolynomial

/-! A finite-side polynomial cost for the actual connected heat recursion.
The exponent depends on the heat step, independently of the cardinality
of the torus and the ultraviolet history. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHeatBudget
open Function Finset Lattice Laurent Wilson RG Precision
open WilsonCoeffUV WilsonCoeffUV.Blue
open scoped BigOperators Classical

theorem sum {I:Type*}(s:Finset I)(f:I→ℝ){M B:ℝ}(pos:0 ≤ M)
    (many:(s.card:ℝ) ≤ B)(cost:∀i∈s,|f i| ≤ M):|∑i∈s,f i| ≤ B*M:=by
  calc
    _ ≤ ∑i∈s,|f i|:=abs_sum_le_sum_abs .. 
    _ ≤ ∑_i∈s,M:=Finset.sum_le_sum cost
    _=(s.card:ℝ)*M:=by simp [nsmul_eq_mul]
    _ ≤ B*M:=mul_le_mul_of_nonneg_right many pos

variable {U:Type}[Fintype U] {B M:ℝ}
omit [Fintype U] in
private theorem averaged {r:ℕ}(T:Ten ℝ U r)(h:∀x,|T x| ≤ M)(pos:0 ≤ M)(x):
    |swirl T x| ≤ M:=by
  let C:ℝ:=Fintype.card (Equiv.Perm (Fin r))
  have good:0<C:=Nat.cast_pos.mpr Fintype.card_pos
  have q:=sum univ (fun p:Equiv.Perm (Fin r)=>T (x∘p)) pos
    (show ((univ:Finset (Equiv.Perm (Fin r))).card:ℝ) ≤ C by simp [C]) (fun p _=>h _)
  simp only [swirl,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  change |C⁻¹*(∑p:Equiv.Perm (Fin r),T (x∘p))| ≤ M
  rw [abs_mul,abs_of_pos (inv_pos.mpr good)]
  exact (mul_le_mul_of_nonneg_left q (inv_nonneg.mpr good.le)).trans_eq
    (by rw [←mul_assoc,inv_mul_cancel₀ good.ne',one_mul])

omit [Fintype U] in
private theorem cut (P:Gen ℝ U)(a:U)(r:ℕ)(_pos:0 ≤ M)(room:(r+1:ℕ) ≤ B)
    (h:∀y,|P (r+1) y| ≤ M)(x):|sever a P r x| ≤ B*M:=by
  simp only [sever,prune,Pi.smul_apply,nsmul_eq_mul,abs_mul, Nat.abs_cast]
  exact mul_le_mul room (h _) (abs_nonneg _) (le_trans (Nat.cast_nonneg _) room)

theorem line (K:Matrix U U ℝ)(P:Gen ℝ U)(r:ℕ)(b:1 ≤ B)(pos:0 ≤ M)
    (room:((r+2:ℕ):ℝ) ≤ B)(many:(Fintype.card U:ℝ) ≤ B)
    (matrix:∀a z,|K a z| ≤ B)(h:∀x,|P (r+2) x| ≤ M)(x):
    |ripple K P r x| ≤ B^5*M:=by
  have bp:=zero_le_one.trans b
  have cost (a z:U):|K a z/2| ≤ B:=by rw [abs_div,abs_of_pos (by norm_num:0<(2:ℝ))];linarith [matrix a z]
  have rim:((r+1:ℕ):ℝ) ≤ B:=by push_cast at *;linarith
  have leaf (a z:U):|sever a (sever z P) r x| ≤ B*(B*M):=
    cut _ _ _ (mul_nonneg bp pos) rim (fun y=>cut P z (r+1) pos room h y) x
  simp only [ripple,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ ≤ B*(B*(B*(B*(B*M)))):=by
      apply sum univ _ (by positivity) (by simpa using many)
      intro a _
      apply sum univ _ (by positivity) (by simpa using many)
      intro z _
      rw [abs_mul]
      exact mul_le_mul (cost _ _) (leaf _ _) (abs_nonneg _) bp
    _=B^5*M:=by ring

theorem join (K:Matrix U U ℝ)(P Q:Gen ℝ U)(r:ℕ)(b:1 ≤ B)(pos:0 ≤ M)
    (room:((r+1:ℕ):ℝ) ≤ B)(many:(Fintype.card U:ℝ) ≤ B)
    (matrix:∀a z,|K a z| ≤ B)(first:∀l ≤ r+1,∀x,|P l x| ≤ M)
    (second:∀l ≤ r+1,∀x,|Q l x| ≤ M)(x):
    |arbor K P Q r x| ≤ B^6*M^2:=by
  have bp:=zero_le_one.trans b
  have BM:=mul_nonneg bp pos
  have cost (a z:U):|K a z/2| ≤ B:=by rw [abs_div,abs_of_pos (by norm_num:0<(2:ℝ))];linarith [matrix a z]
  have brief {l:ℕ}(hr:l ≤ r):((l+1:ℕ):ℝ) ≤ B:=(by exact_mod_cast Nat.succ_le_succ hr:((l+1:ℕ):ℝ) ≤ r+1).trans (by simpa using room)
  have node(a z:U)(y):|spore (sever a P) (sever z Q) r y| ≤ B*((B*M)*(B*M)):=by
    simp only [spore,Finset.sum_apply]
    apply sum _ _ (mul_nonneg BM BM) (by simpa using room)
    intro j hj
    have g:j.1+j.2=r:=by simpa using hj
    rw [interweave,dif_pos g,smul_eq_mul,abs_mul]
    exact mul_le_mul (cut _ _ _ pos (brief (by omega)) (first _ (by omega)) _)
      (cut _ _ _ pos (brief (by omega)) (second _ (by omega)) _) (abs_nonneg _) BM
  simp only [arbor_form,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  calc
    _ ≤ B*(B*(B*(B*((B*M)*(B*M))))) :=by
      apply sum univ _ (by positivity) (by simpa using many)
      intro a _
      apply sum univ _ (by positivity) (by simpa using many)
      intro z _
      rw [abs_mul]
      exact mul_le_mul (cost _ _) (averaged _ (node a z) (by positivity) x) (abs_nonneg _) bp
    _=B^6*M^2:=by ring

/-- Every original finite heat tensor through a fixed cap is polynomially
bounded by the actual number of coordinates and the prices of the inputs. -/
theorem through (cap limit:ℕ)(limited:limit ≤ cap)(K:Matrix U U ℝ)(P:ℕ→Gen ℝ U)(B:ℝ)(base:2 ≤ B)
    (width:((cap+2:ℕ):ℝ) ≤ B)(many:(Fintype.card U:ℝ) ≤ B)
    (kernel:∀a z,|K a z| ≤ B)(enter:∀i ≤ limit,∀l ≤ cap,∀x,|P i l x| ≤ B):
    ∀ (h i r : ℕ), i ≤ limit → (r + 2 * h ≤ cap) → ∀ x, |abr K P h i r x| ≤ B^(16*3^h):=by
  have b:1 ≤ B:=by linarith
  have bp:=zero_le_one.trans b
  have room(k:ℕ)(le:k ≤ cap+2): (k:ℝ) ≤ B:= (by exact_mod_cast le:(k:ℝ) ≤ ((cap+2:ℕ):ℝ)).trans width
  intro h
  induction h using Nat.strong_induction_on with
  | h n ih=>
    intro i r ic rc x
    cases n with
    | zero=>
      rw [abr]
      exact (enter i ic r (by omega) x).trans (le_self_pow₀ b (by norm_num))
    | succ k=>
      let M:=B^(16*3^k)
      have root:1 ≤ M:=one_le_pow₀ b
      have mp:=zero_le_one.trans root
      have prev (a v l:ℕ)(ha:a ≤ k)(lt:v ≤ limit)(rank:l+2*a ≤ cap)(y):
          |abr K P a v l y| ≤ M:=by
        apply (ih a (by omega) v l lt rank y).trans
        exact pow_le_pow_right₀ b (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) ha))
      have fresh:=line K (abr K P k i) r b mp (room _ (by omega)) many kernel
        (fun y=>prev k i (r+2) le_rfl ic (by omega) y) x
      have tree:|ravel K (abr K P) (abr K P) k i r x| ≤ B^8*M^2:=by
        simp only [ravel,Finset.sum_apply]
        calc
          _ ≤ B*(B*(B^6*M^2)):=by
            apply sum _ _ (by positivity) (by simpa using room (k+1) (by omega))
            intro j hj
            have a:j.1+j.2=k:=by simpa using hj
            apply sum _ _ (by positivity) (by simpa using room (i+1) (by omega))
            intro q hq
            have v:q.1+q.2=i:=by simpa using hq
            exact join K _ _ r b mp (room _ (by omega)) many kernel
              (fun l hl y=>prev j.1 q.1 l (by omega) (by omega) (by omega) y)
              (fun l hl y=>prev j.2 q.2 l (by omega) (by omega) (by omega) y) x
          _=B^8*M^2:=by ring
      have f:B^5*M ≤ B^8*M^2:=mul_le_mul (pow_le_pow_right₀ b (by decide))
        (le_self_pow₀ root (by decide)) mp (pow_nonneg bp _)
      have capsum:B^5*M+B^8*M^2 ≤ B^9*M^2:=by
        calc
          _ ≤ 2*(B^8*M^2):=by linarith
          _ ≤ B*(B^8*M^2):=mul_le_mul_of_nonneg_right base (by positivity)
          _=_:=by ring
      have clipped:|((k+1:ℕ):ℝ)⁻¹| ≤ 1:=by
        rw [abs_of_nonneg (by positivity)]
        apply inv_le_one_of_one_le₀;exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      simp only [abr_next,Pi.smul_apply,Pi.add_apply,smul_eq_mul,abs_mul]
      calc
        _ ≤ 1*(B^5*M+B^8*M^2):=mul_le_mul clipped ((abs_add_le ..).trans (add_le_add fresh tree))
            (abs_nonneg _) zero_le_one
        _ ≤ B^9*M^2:=by simpa using capsum
        _=B^(9+(16*3^k)*2):=by simp only [M,pow_add,pow_mul]
        _ ≤ _:=by
          apply pow_le_pow_right₀ b
          rw [pow_succ]
          have z:0<3^k:=Nat.pow_pos (by decide)
          omega

theorem original (cap:ℕ)(K:Matrix U U ℝ)(P:ℕ→Gen ℝ U)(B:ℝ)(base:2 ≤ B)
    (width:((cap+2:ℕ):ℝ) ≤ B)(many:(Fintype.card U:ℝ) ≤ B)
    (kernel:∀a z,|K a z| ≤ B)(enter:∀i ≤ cap,∀l ≤ cap,∀x,|P i l x| ≤ B):
    ∀ (h i r:ℕ), i ≤ cap → (r+2*h ≤ cap) → ∀x,|abr K P h i r x| ≤ B^(16*3^h):=
  through cap cap le_rfl K P B base width many kernel enter

end YM.Integration.WilsonVacuumPreResetFiniteHeatBudget
end
