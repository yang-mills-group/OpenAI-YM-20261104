import YM.RG05Readout.Many.Pick
import YM.RG05Readout.Aligned.Geometry

/-! On the original finite lower interval, estimate the unweighted price of
one original physical mode by the logarithm of its actual interval length. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedCaptureRadii
open Finset Function Lattice Wilson RG Marker RG05Readout.Many
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G}

def cost (T d k h : ℕ) : ℝ := (3*k+4:ℕ)*(T:ℝ)+(k:ℝ)+h+(d:ℝ)*T

/-- One common upper bound for every represented lower inverse width, including
the full product of the original rust factors. -/
theorem radius (simple : G.Simple) {b m i T d k h : ℕ} (bi : b ≤ i) (im : i ≤ m)
    {Q : ℝ} (qp : 0 < Q) (cap : Q ≤ (C.path.levels.clock.hatBeta m)^h)
    (ratio : C.S.a b / C.S.a m ≤ (RG05Readout.Lambda C.path.levels m)^T)
    (gap : ((m-b:ℕ):ℝ) ≤ (T:ℝ)*(1+Real.log (RG05Readout.Lambda C.path.levels m))) :
    let x := Real.log (C.path.levels.clock.hatBeta m)
    let y := Real.log (RG05Readout.Lambda C.path.levels m)
    0 < envelope C m d k Q i ∧ 
      1 ≤ Real.exp (cost T d k h*(1+x)*(1+y))*envelope C m d k Q i := by
  let A:=C.path.levels
  let β:=A.clock.hatBeta
  let mast:=RG05Readout.Lambda A m
  let x:=Real.log (β m)
  let y:=Real.log mast
  let t:=3*k+4
  have bp (j : ℕ) : 0 < β j := zero_lt_one.trans (A.fits.delayed j)
  have bmpos := bp m
  have bipos := bp i
  have meshpos := div_pos (C.S.a_pos i) (C.S.a_pos m)
  have lp : 1 ≤ mast := by
    change 1 ≤ 2+Real.log (β m)
    linarith only [Real.log_nonneg (A.fits.delayed m).le]
  have pos : 0 < mast := zero_lt_one.trans_le lp
  have x0 : 0 ≤ x := Real.log_nonneg (A.fits.delayed m).le
  have y0 : 0 ≤ y := Real.log_nonneg lp
  have wide : 0 < envelope C m d k Q i := by
    unfold envelope west markWidth
    exact mul_pos (rust_paid (C:=C) (m:=m) (k:=k) i).1
      (div_pos (inv_pos.mpr (pow_pos (bp i) k)) (totalpos qp i))
  refine ⟨wide,(inv_le_iff_one_le_mul₀ wide).1 ?_⟩
  let E := ((β m)^t)^(m-i)*(β m)^k*(β m)^h*(mast^T)^d
  have bal : (envelope C m d k Q i)⁻¹ =
      (∏ j ∈ Ico i m,(β j)^t)*(β i)^k*Q*(C.S.a i/C.S.a m)^d := by
    simp [envelope,west,markWidth,total,rusty,not_lt.mpr im,div_eq_mul_inv,mul_inv_rev,
      β,A,t,mul_assoc,mul_comm,mul_left_comm]
  have rust : (∏ j ∈ Ico i m,(β j)^t) ≤ ((β m)^t)^(m-i) := by
    calc _ ≤ ∏ _j ∈ Ico i m,(β m)^t :=
            Finset.prod_le_prod (fun j _=>pow_nonneg (bp j).le _) (fun j hj=>
              pow_le_pow_left₀ (bp j).le (beta_le' (C:=C) simple (Finset.mem_Ico.mp hj).2.le) _)
         _ = _ := by simp
  have mesh : C.S.a i/C.S.a m ≤ mast^T :=
    (div_le_div_of_nonneg_right (C.S.strictAnti.antitone bi) (C.S.a_pos m).le).trans ratio
  have size : (envelope C m d k Q i)⁻¹ ≤ E := by
    rw [bal]
    unfold E
    have middle := mul_le_mul rust (pow_le_pow_left₀ bipos.le
      (beta_le' (C:=C) simple im) k) (pow_nonneg bipos.le k)
      (pow_nonneg (pow_nonneg bmpos.le t) (m-i))
    have subtotal := mul_le_mul middle cap qp.le (by positivity)
    exact mul_le_mul subtotal (pow_le_pow_left₀ meshpos.le mesh d)
      (pow_nonneg meshpos.le d) (by positivity)
  have xp : 0 < E := by dsimp [E]; positivity
  have logE : Real.log E = (t:ℝ)*(m-i:ℕ)*x+(k:ℝ)*x+(h:ℝ)*x+(d:ℝ)*T*y := by
    dsimp only [E]
    rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
    simp only [Real.log_pow]
    dsimp only [x,y]
    ring
  let F := (1+x)*(1+y)
  have xF : x ≤ F := by unfold F; nlinarith only [x0,y0,mul_nonneg x0 y0]
  have yF : y ≤ F := by unfold F; nlinarith only [x0,y0,mul_nonneg x0 y0]
  have dgap : ((m-i:ℕ):ℝ) ≤ (T:ℝ)*(1+y) :=
    (show ((m-i:ℕ):ℝ) ≤ ((m-b:ℕ):ℝ) by exact_mod_cast Nat.sub_le_sub_left bi m).trans gap
  have gF : ((m-i:ℕ):ℝ)*x ≤ (T:ℝ)*F := by
    calc _ ≤ (T:ℝ)*(1+y)*x := mul_le_mul_of_nonneg_right dgap x0
         _ ≤ (T:ℝ)*F := by
           have := mul_le_mul_of_nonneg_left
             (mul_le_mul_of_nonneg_right (show x ≤ 1+x by linarith) (show 0 ≤ 1+y by linarith))
             (Nat.cast_nonneg T : (0:ℝ) ≤ T)
           dsimp [F]; nlinarith only [this]
  have due : Real.log E ≤ cost T d k h*(1+x)*(1+y) := by
    rw [logE,show cost T d k h*(1+x)*(1+y)=cost T d k h*F by unfold F;ring]
    unfold cost
    dsimp only [t] at *
    nlinarith only [mul_le_mul_of_nonneg_left gF (Nat.cast_nonneg (3*k+4) : (0:ℝ) ≤ (3*k+4:ℕ)),
      mul_le_mul_of_nonneg_left xF (Nat.cast_nonneg k : (0:ℝ) ≤ k),
      mul_le_mul_of_nonneg_left xF (Nat.cast_nonneg h : (0:ℝ) ≤ h),
      mul_le_mul_of_nonneg_left yF (mul_nonneg (Nat.cast_nonneg d : (0:ℝ) ≤ d)
        (Nat.cast_nonneg T : (0:ℝ) ≤ T))]
  exact size.trans (by exact (Real.exp_log xp).symm.le.trans (Real.exp_le_exp.mpr due))

theorem mode {V:Type} [DecidableEq V] {J:Census V} (simple:G.Simple)
    {b m i T d k h L:ℕ} (bi:b ≤ i) (im:i ≤ m) (Q:V → ℝ) (qp:∀v,0 < Q v)
    (cap:∀v,Q v ≤ (C.path.levels.clock.hatBeta m)^h)
    (ratio:C.S.a b/C.S.a m ≤ (RG05Readout.Lambda C.path.levels m)^T)
    (gap:((m-b:ℕ):ℝ) ≤ (T:ℝ)*(1+Real.log (RG05Readout.Lambda C.path.levels m)))
    (s:J.Mode) (count:s.val.card ≤ L) :
    let x:=Real.log (C.path.levels.clock.hatBeta m)
    let y:=Real.log (RG05Readout.Lambda C.path.levels m)
    1 ≤ Real.exp ((L:ℝ)*cost T d k h*(1+x)*(1+y))*
      Poly.toll (fun v=>envelope C m d k (Q v) i) s := by
  intro x y
  let E:=cost T d k h*(1+x)*(1+y)
  have x0 : 0 ≤ x := Real.log_nonneg (C.path.levels.fits.delayed _).le
  have y0 : 0 ≤ y := Real.log_nonneg (by
    change 1 ≤ 2+Real.log (C.path.levels.clock.hatBeta m)
    linarith only [x0])
  have e0 : 0 ≤ E := by unfold E cost; positivity
  have one : 1 ≤ ∏ v∈s.val,Real.exp E*envelope C m d k (Q v) i :=
    Finset.one_le_prod fun v _=>(radius simple bi im (qp v) (cap v) ratio gap).2
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.exp_nat_mul] at one
  refine one.trans (mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun v _=>
    (radius simple bi im (qp v) (cap v) ratio gap).1.le))
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_right (show (s.val.card:ℝ) ≤ L by exact_mod_cast count) e0
  unfold E at this
  linarith only [this]

end YM.Integration.WilsonMixedTaggedCaptureRadii
