import YM.WilsonCoeffUV.Series.Components.HeatRanks
/-! Ramp evaluated and its linear/quadratic calculus. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Blue
open Matrix Function Finset PowerSeries
open scoped BigOperators
variable {U R: Type*} [Fintype U]

def ramp (P:Layers ℝ U)(n:ℕ) : Ink (Option U) := mk fun e=> ∑ j∈range (1+n+3*e),MvPolynomial.X none ^ j * launchT (totalR (P j e))
def flash (P:ℕ→ Gen ℝ U) : Ink U:= mk fun e=>totalR (P e)
omit [Fintype U] in
lemma finite_stops {P:Layers ℝ U}{n}(h:stops n P)(j e:ℕ) : FiniteGen (P j e) := ⟨n+e+1,fun i hi=>h j e i (Or.inl hi)⟩
omit [Fintype U] in
lemma height_stops {P:Layers ℝ U}{n}(h:stops n P){j e:ℕ}(p:1+n+3*e≤j): P j e=0 := funext fun i=> h j e i (Or.inr (by omega))
lemma finite_ravel {P Q:Layers ℝ U}{e j k t}(h:stops k P)(g:stops t Q)(G:Matrix U U ℝ) : FiniteGen (ravel G P Q j e) := by unfold ravel; apply finite_sum; intro i _; apply finite_sum; intro j _; exact finite_arbor _ (finite_stops h ..) (finite_stops g ..)

omit [Fintype U] in
lemma past_lamp (p:POL U) (e j : ℕ) : spanT e U (MvPolynomial.X none ^ j * launchT p) = if j=e then p else 0 := by
  rw [span_time,map_mul,map_pow,launched,MvPolynomial.optionEquivLeft_X_none,mul_comm,Polynomial.C_mul_X_pow_eq_monomial,Polynomial.coeff_monomial]
lemma glance {P:Layers ℝ U} {n:ℕ}(h:stops n P)(j e : ℕ) : spanT j U (coeff e (ramp P n))=totalR (P j e) := by
  simp_rw [ramp,coeff_mk,map_sum,past_lamp]
  rw [Finset.sum_eq_single j]; simp
  · intro i hi hh; rw [if_neg hh]
  intro hi; rw [height_stops h (by simpa using hi)]; simp [totalR]

-- time projection
abbrev stopF (x:ℝ) : Ink (Option U)→+*Ink U := PowerSeries.map (stopT x).toRingHom
lemma setV {P:Layers ℝ U}{n:ℕ}(h:stops n P): stopF 0 (ramp P n)=flash (P 0) := by
  ext1 e; rw [flash,stopF,coeff_mk,coeff_map]; exact (span_zero (coeff e _)).symm.trans (glance h 0 e)
lemma step_eva (x:ℝ)(P:Layers ℝ U)(n)(e): coeff e (stopF x (ramp P n))=
      ∑ j∈range (1+n+3*e), x^j • totalR (P j e) := by
  rw [stopF,coeff_map,ramp,coeff_mk,map_sum]; apply sum_congr rfl; intro i _
  change stopT x _= _; rw [map_mul,map_pow,stopT_launch,Algebra.smul_def,_root_.map_pow,stopT_X]; rfl
lemma at_one (P:Layers ℝ U)(n:ℕ) (h:stops n P): stopF 1 (ramp P n)=flash fun e=> ∑ j∈range (1+n+3*e),P j e := by
  ext1 e; rw [step_eva,flash,coeff_mk,visible_sum (fun i _=>finite_stops h i e)]; simp

-- read packed times

def goLap (G:Matrix U U ℝ) := overlay (windowLap G (some : U→Option U))
def goLip (G:Matrix U U ℝ)(P Q:Ink (Option U)): Ink (Option U) := ∑ i:U,∑ j:U,(G i j/2) • (brush (.some i) P * brush (.some j) Q)
lemma spelt (G:Matrix U U ℝ)(P:Ink (Option U)) : goLap G P=∑ i:U,∑ j:U,(G i j/2) • brush (.some i) (brush (.some j) P) := by
  ext1 n; simp_rw [goLap,overlay_apply,map_sum,windowLap_apply, coeff_smul,brush, blot_apply]
lemma lamp_count (G:Matrix U U ℝ)(P:Layers ℝ U){n}(h:stops n P)(j e) (hh:Pure (P j e)) : spanT j U (coeff e (goLap G (ramp P n))) = totalR (ripple G (P j e)) := by
  rw [goLap,overlay_apply,cadenceLap,glance h,visible_ripple G (finite_stops h j e) hh]
omit [Fintype U] in
lemma span_brush (i:U)(u: Ink (Option U)) (j e:ℕ) : spanT j U (coeff e (brush (.some i) u)) = MvPolynomial.pderiv i (spanT j U (coeff e u)) := by
  rw [brush,blot_apply,span_excise]
omit [Fintype U] in
private lemma leaves (P Q:Ink (Option U))(i j:ℕ) : spanT i U (coeff j (P*Q)) = ∑ a∈antidiagonal i,∑ b∈antidiagonal j, spanT a.1 U (coeff b.1 P) * spanT a.2 U (coeff b.2 Q) := by
  simp_rw [coeff_mul,map_sum, span_time,map_mul,Polynomial.coeff_mul]; rw [Finset.sum_comm]
lemma lip_count (G:Matrix U U ℝ)(P Q:Layers ℝ U){n t}(h:stops n P)(g:stops t Q)(j e) (p:∀ i v,Pure (P i v))(q:∀ i v,Pure (Q i v)) :
    spanT j U (coeff e (goLip G (ramp P n) (ramp Q t))) = totalR (ravel G P Q j e) := by
  simp_rw [goLip,map_sum, coeff_smul,map_smul,leaves, Finset.smul_sum,span_brush,glance h,glance g]
  conv_lhs => enter [2,u]; rw [Finset.sum_comm]
  rw [Finset.sum_comm];
  have ht i v (a b:ℕ):= finite_arbor G (finite_stops h i v) (finite_stops g a b)
  rw [ravel, visible_sum (fun i _=>finite_sum fun j _=>ht _ _ _ _)]
  apply sum_congr rfl; intro i _
  rw [visible_sum (fun j _=>ht _ _ _ _)]
  conv_lhs => enter [2,u]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]; exact sum_congr rfl fun k _=> (visible_arbor G (finite_stops h _ _) (p _ _) (finite_stops g _ _) (q _ _)).symm
omit [Fintype U] in
lemma lamp_ext {P Q:Ink (Option U)} (h:∀ j i:ℕ,spanT j U (coeff i P)=spanT j U (coeff i Q)): P=Q := by
  ext1 i; apply (MvPolynomial.optionEquivLeft ℝ U).injective; exact Polynomial.ext (fun j=> h j i)
omit [Fintype U] in
private lemma eclipse (P:Ink (Option U))(n e : ℕ): spanT n U (coeff e (brush none P)) = (n+1) • spanT (n+1) U (coeff e P) := by rw [brush,blot_apply]; exact span_clock ..
lemma lamp_abr {P:ℕ→Gen ℝ U}(h:shellK 2 P)(p:∀ i,Pure (P i))(z:P 0=0)(G:Matrix U U ℝ):
    let F:= ramp (abr G P) 2
    brush none F=goLap G F+goLip G F F := by
  intro F
  have q:=stops_abr G h z
  have μ:=pure_abr G p
  apply lamp_ext; intro i e
  rw [map_add,map_add,eclipse,show spanT (i+1) U (coeff e F)=totalR _ from glance q .., lamp_count G _ q _ _ (μ i e),lip_count G _ _ q q _ _ μ μ]
  have hf := finite_ripple G (finite_stops q i e); have he:=finite_ravel (e:=e) (j:=i) q q G
  rw [abr_next, visible_μ (finite_add hf he), ←Nat.cast_smul_eq_nsmul (R:=ℝ), smul_smul,mul_inv_cancel₀ (by positivity),one_smul, visible_add hf he]
lemma lamp_bul {P:ℕ→Gen ℝ U}{D:Layers ℝ U}(d:∀ h e r,r>2+e ∨ r+2*h>3*e → D h e r=0){l}(p:shellK l P)(q:∀ i,Pure (P i))(u:∀ i v,Pure (D i v))(G:Matrix U U ℝ):
    let F:= ramp (bul G D P) l; let Y:= ramp D 2
    brush none F=goLap G F+goLip G Y F+goLip G.transpose Y F := by
  intro F Y
  have q':=stops_bul G d l p; have v : stops 2 D:= fun h e r H=> d _ _ _ (by omega)
  have μ:=pure_bul G D q
  apply lamp_ext; intro i e
  rw [map_add,map_add, map_add,map_add,eclipse,show spanT (i+1) U (coeff e F)=totalR _ from glance q' .., lamp_count G _ q' _ _ (μ i e),lip_count G _ _ v q' _ _ u μ,lip_count G.transpose _ _ v q' _ _ u μ]
  have hf := finite_ripple G (finite_stops q' i e); have he H:=finite_ravel (e:=e) (j:=i) v q' H
  rw [bul_next, visible_μ (finite_add (finite_add hf (he G)) (he _)), ←Nat.cast_smul_eq_nsmul (R:=ℝ), smul_smul,mul_inv_cancel₀ (by positivity),one_smul, visible_add (finite_add hf (he G)) (he _),visible_add hf (he _)]
end YM.WilsonCoeffUV.Blue
