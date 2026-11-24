import YM.WilsonCoeffUV.Series.Components.Ramp
/-! Verify ordered log-after-denominators, Polchinski polynomial power identities
with the exact edge counts and factorials for the W-reader. No infinite time
(or column) evolution. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function Finset PowerSeries
open scoped BigOperators
variable {U: Type*} [Fintype U]

-- algebra identity on heat equation
lemma lap_split (G:Matrix U U ℝ)(u v:Ink (Option U)) : goLap G (u*v)= goLap G u*v + u*goLap G v+goLip G u v+goLip G.transpose u v := by
  simp only [spelt,goLip,Derivation.leibniz,map_add,smul_eq_mul, smul_add]
  simp_rw [Finset.sum_add_distrib, Finset.sum_mul,Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  -- manipulate purely
  conv_rhs => arg 2; rw [Finset.sum_comm]
  conv_lhs => arg 2; arg 1; enter [2,i,2,j,2]; rw [mul_comm]
  conv_lhs => arg 1; arg 2; enter [2,i,2,j,2]; rw [mul_comm]
  simp_rw [Matrix.transpose_apply]; abel
lemma lap_exp (G:Matrix U U ℝ)(u:Ink (Option U))(h:constantCoeff u=0) : goLap G (raiseE u)=raiseE u*(goLap G u+goLip G u u) := by
  have hg (i:U) : brush (.some i) (raiseE u)=raiseE u * brush (.some i) u := raise_diff h _
  rw [spelt,goLip,spelt]; simp_rw [mul_add,Finset.mul_sum,hg,Derivation.leibniz, hg,smul_eq_mul,smul_add, Finset.sum_add_distrib,mul_smul_comm]; refine congr_arg₂ (· + ·) rfl ?_
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [mul_left_comm]; rw [mul_comm (brush (some j) u)]
lemma lip_prime (G:Matrix U U ℝ)(u:Ink (Option U))(h:constantCoeff u=0)(v) : goLip G (raiseE u) v= raiseE u*goLip G u v := by
  unfold goLip; simp_rw [Finset.mul_sum,brush, raise_diff h]; simp only [mul_smul_comm, mul_assoc]
lemma caloric_eva (G:Matrix U U ℝ) (f p)(h:brush none (f:Ink (Option U))=goLap G f) (e:stopF 0 f=p):
    stopF 1 f=blur G p := by
  ext1 n; rw [overlay_apply];
  have he : foldsH (G:=G) (coeff n p) (coeff n f) := ⟨by
    have he :=congrArg (coeff n) h; rw [brush, blot_apply,goLap,overlay_apply] at he; apply he,by
    rw [← e]; exact (coeff_map _ _ _).symm⟩
  rw [glazed,givenSpread he]; apply coeff_map

lemma rolls_clean (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(z:P 0=0) :
    constantCoeff (ramp (abr G P) 2)=0 := by
  have ht h: totalR ((abr G P) h 0)=0 := by rw [bare_abr G z h]; simp [totalR]
  rw [← coeff_zero_eq_constantCoeff_apply,ramp,coeff_mk]; simp_rw [ht]; simp
lemma F0_apply (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(h:shellK 2 P)(z:P 0=0): stopF 0 (ramp (abr G P) 2)= flash P := by
  rw [setV (stops_abr G h z)]; rw [show abr G P 0=P from funext fun j=>abr_zero ..]
lemma H0_apply (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(h:shellK 2 P)(z:P 0=0){l}{Q:ℕ→Gen ℝ U}(v:shellK l Q): stopF 0 (ramp (bul G (abr G P) Q) l)=flash Q := by
  rw [setV (stops_bul G (span_abr G h z) l v), show bul _ _ _ _= Q from funext fun j=> bul_zero G (abr G P) Q j]
lemma first_heat (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(h:shellK 2 P)(z:P 0=0)(p:∀ i,Pure (P i)):
    let F:=ramp (abr G P) 2; brush none (raiseE F)=goLap G (raiseE F) := by
  intro F; rw [show brush _ _= _ from raise_diff (rolls_clean G z) (MvPolynomial.pderiv none), show blot _ F=goLap G F+goLip G F F from lamp_abr h p z G, lap_exp G F (rolls_clean G z)];

theorem as_normal_exp (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(h:shellK 2 P)(z:P 0=0)(p:∀ i,Pure (P i)) :
    blur G (raiseE (flash P))= raiseE (stopF 1 (ramp (abr G P) 2)) := by
  have q:=rolls_clean G z
  rw [← caloric_eva G _ _ (first_heat G h z p) ?e,raise_map _ (by simp [stopF]) q]
  case e=> rw [raise_map _ (by simp [stopF]) q,F0_apply G h z]

theorem as_normal_log (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(h:shellK 2 P)(z:P 0=0)(p:∀ i,Pure (P i)) :
    logOf (blur G (raiseE (flash P)))=stopF 1 (ramp (abr G P) 2) := by
  rw [as_normal_exp G h z p]; have he : constantCoeff (stopF 1 (ramp (abr G P) 2))=0 := by
    rw [←coeff_zero_eq_constantCoeff_apply,stopF, coeff_map,coeff_zero_eq_constantCoeff_apply,rolls_clean G z,map_zero]
  have hu:=raise_one he; apply raise_inj (constantCoeff_logOf hu) he; exact raising_log hu
omit [Fintype U] in
lemma brush_back {u:Ink (Option U)}(z:constantCoeff u=0) : brush none (raiseE u)=raiseE u*brush none u := raise_diff z _
/-- One label at fixed demand. Division by the all-vacuum formal density
at the GIVEN fields before projection. Use products/connected algebra with
all labels BEFORE capture externally. -/
theorem as_column (G:Matrix U U ℝ){P:ℕ→Gen ℝ U}(h:shellK 2 P)(z:P 0=0)(p:∀ i,Pure (P i)){l}{Q:ℕ→Gen ℝ U}(v:shellK l Q)(w:∀ i,Pure (Q i)) :
    blur G (raiseE (flash P)*flash Q)=blur G (raiseE (flash P))*stopF 1 (ramp (bul G (abr G P) Q) l) := by
  have he:=rolls_clean G z
  let F:=ramp (abr G P) 2; let H:=ramp (bul G (abr G P) Q) l
  have hx : brush none (raiseE F * H)=goLap G (raiseE F * H) := by
    rw [Derivation.leibniz,first_heat G h z p, lamp_bul (span_abr G h z) v w (pure_abr G p) G, lap_split, lip_prime G F he H, lip_prime G.transpose F he H];
    change raiseE F • (goLap G H+ goLip G F H + goLip G.transpose F H)+H • _= _; simp only [smul_eq_mul]; ring
  have hf :=F0_apply G h z; change stopF 0 F= _ at hf
  have hy : stopF 0 (raiseE F*H)= raiseE (flash P)*flash Q := by
    rw [map_mul, raise_map _ (by simp [stopF]) (show constantCoeff F=0 from he),hf, H0_apply G h z v]
  rw [as_normal_exp G h z p,← caloric_eva G _ _ hx hy,map_mul, raise_map _ (by simp [stopF]) he]
end YM.WilsonCoeffUV.Blue
