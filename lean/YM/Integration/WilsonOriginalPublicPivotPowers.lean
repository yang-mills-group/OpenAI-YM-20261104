import YM.Integration.WilsonOriginalPublicPivotRoster

/-! Collar depth pays the stable error. A higher Taylor order pays the raw
convolution tail only. The public loss is fixed before the collar depth. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicPivotPowers
open Filter Finset RG PhysicalNext.Repeat.Legato
open scoped Classical BigOperators

structure Window (N h p:ℕ)(E D ζ:ℝ) where
  eta : ℝ
  depth : ℝ
  drift : 0<eta
  positive : 0<depth
  stable : (N:ℝ)*eta ≤ ζ/2
  minimum : (p:ℝ)+1+N*(E+D) ≤ depth*(ζ/2)

def window {E D ζ:ℝ}(ep:0 ≤ E)(dp:0 ≤ D)(zp:0<ζ)(N h p:ℕ):Window N h p E D ζ where
  eta:=ζ/(4*((N:ℝ)+1))
  depth:=((p:ℝ)+2+N*(E+D))/(ζ/2)
  drift:=div_pos zp (by positivity)
  positive:=div_pos (by positivity) (by positivity)
  stable:=by
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    have nn:0 ≤ (N:ℝ)*ζ:=mul_nonneg (Nat.cast_nonneg _) zp.le
    nlinarith only [nn,zp]
  minimum:=by field_simp;linarith

def tailOrder {N h p:ℕ}{E D ζ:ℝ} (W:Window N h p E D ζ)(upper:ℝ) : ℕ:=
  ⌈(p:ℝ)+N*E+upper*(h+N*W.eta)+2⌉₊

theorem tariff {N h p:ℕ}{E D ζ:ℝ} (W:Window N h p E D ζ)(upper:ℝ):
    (p:ℝ)+N*E+upper*(h+N*W.eta)+1 ≤ (tailOrder W upper:ℝ):=
  (by linarith : (p:ℝ)+N*E+upper*(h+N*W.eta)+1 ≤ (p:ℝ)+N*E+upper*(h+N*W.eta)+2).trans (Nat.le_ceil ..)

private theorem wages {I:Type*} [Fintype I] (x:I→ℝ)(nn:∀i,0 ≤ x i)
    {v:ℝ}(cap:∀i,x i ≤  Real.exp v):
    ∏i,x i ≤ Real.exp ((Fintype.card I:ℝ)*v):=by
  calc
    _  ≤  ∏_i:I,Real.exp v:=prod_le_prod (fun i _=>nn i) (fun i _=>cap i)
    _ = _:=by simp only [Finset.prod_const,Finset.card_univ,Real.exp_nat_mul]

/-- Every proper partition restores one actual source/residual salary per
occupied member. A common stable read pays one mesh gain on each nonempty
remainder group, irrespective of its number of lower coordinates. -/
theorem remainder {N h p:ℕ}{E D ζ:ℝ} (W:Window N h p E D ζ) (N₀:Type*) [Fintype N₀]
    (load:Fintype.card N₀ ≤ N) {s a u:ℝ} (s0:0 ≤ s)(a0:0 ≤ a)(finer:W.depth*s ≤ a)
    (ep:0 ≤ E)(dp:0 ≤ D)(zp:0 ≤ ζ) (_cash:0 ≤ u)(price:u ≤ Real.exp (s-ζ*a))
    (used:Finset N₀)(raw coord:N₀→ℝ)(rn:∀i,0 ≤ raw i)(cn:∀i,0 ≤ coord i)
    (size:∀i,raw i ≤ Real.exp (E*s+W.eta*a))(known:∀i,coord i ≤ Real.exp (D*s)):
    u*∏i, (if i∈used then raw i else coord i) ≤ Real.exp (-(p:ℝ)*s):=by
  have up:0 ≤ (E+D)*s+W.eta*a:=add_nonneg (mul_nonneg (add_nonneg ep dp) s0) (mul_nonneg W.drift.le a0)
  have one (i:N₀):(if i∈used then raw i else coord i) ≤ Real.exp ((E+D)*s+W.eta*a):=by
    by_cases yes:i∈used
    · rw [if_pos yes];apply (size i).trans;apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg dp s0]
    · rw [if_neg yes];apply (known i).trans;apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg ep s0,mul_nonneg W.drift.le a0]
  have bound: (∏i,(if i∈used then raw i else coord i)) ≤ Real.exp ((N:ℝ)*((E+D)*s+W.eta*a)):=by
    apply (wages _ (fun i=>by split_ifs <;> first | exact rn i | exact cn i) one).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast load) up)
  apply (mul_le_mul price bound (prod_nonneg fun i _=>by split_ifs <;> first | exact rn i | exact cn i) (Real.exp_pos _).le).trans
  rw [←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e:=mul_le_mul_of_nonneg_right W.stable a0
  have b:=mul_le_mul_of_nonneg_left finer (show 0 ≤ ζ/2 by positivity)
  have c:=mul_le_mul_of_nonneg_right W.minimum s0
  nlinarith only [e,b,c]

theorem tail {N h p:ℕ}{E D ζ:ℝ} (W:Window N h p E D ζ)(I:Type*) [Fintype I]
    (load:Fintype.card I ≤ N){s a upper:ℝ}(s0:0 ≤ s)(a0:0 ≤ a)(reach:a ≤ upper*s)(ep:0 ≤ E)
    (q:ℕ)(order:tailOrder W upper ≤ q)(raw:I→ℝ)(rn:∀i,0 ≤ raw i)
    (size:∀i,raw i ≤ Real.exp (E*s+W.eta*a)):
    Real.exp (-(q:ℝ)*s+(h:ℝ)*a+s)*(∏i,raw i) ≤ Real.exp (-(p:ℝ)*s):=by
  have inc:0 ≤ E*s+W.eta*a:=add_nonneg (mul_nonneg ep s0) (mul_nonneg W.drift.le a0)
  have bill:=wages raw rn size
  have all:(∏i,raw i) ≤ Real.exp ((N:ℝ)*(E*s+W.eta*a)):=bill.trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by exact_mod_cast load) inc))
  apply (mul_le_mul_of_nonneg_left all (Real.exp_pos _).le).trans
  rw [←Real.exp_add];apply Real.exp_le_exp.mpr
  have high:=mul_le_mul_of_nonneg_left reach (show 0 ≤ (h:ℝ)+N*W.eta from add_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) W.drift.le))
  have aq:=mul_le_mul_of_nonneg_right ((tariff W upper).trans (show (tailOrder W upper:ℝ) ≤ (q:ℝ) by exact_mod_cast order)) s0
  nlinarith only [high,aq]

theorem coupling {g:ℝ} (pos:0<g)(p:ℕ):Real.exp (-(p:ℝ)*Real.log g⁻¹)=g^p:=by
  rw [Real.log_inv,neg_mul_neg,Real.exp_nat_mul,Real.exp_log pos]

/-- The small parameter on these two original dates is exactly the mesh
of the independently filed finite reading at the preselected index. -/
theorem mesh {G:Gauge} (R:Run G)(D:XSpace.Run){start stage n j b:ℕ}{w:ℕ→ℕ}
    (C:WilsonPositionProgramTrialCollarMesh.Corridor R D start w stage n j b):
    Real.log (D.step (WilsonPositionProgramTrialCollarMesh.index w n j)).spacing⁻¹=
      Real.log ((R.family.S.a (start+n+j)/R.family.S.a (start+n))⁻¹):=by rw [C.spacing]

end YM.Integration.WilsonOriginalPublicPivotPowers
end
