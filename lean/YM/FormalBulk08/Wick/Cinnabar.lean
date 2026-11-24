import YM.FormalBulk08.Wick.Ash

/-! Heat flow formulas for g-dependent weights. Equivalence with *logarithm after heat*.
Two-point transfer is not estimated by averaging disconnected weights. `coal` will
have coefficients read directly in (connected) root sums. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series
open scoped Classical BigOperators
open PowerSeries
variable {R : Type*} {V : Type*} [CommRing R] [Algebra ℚ R] [Fintype V] (q : V → V → R)
abbrev Heat (R V : Type*) [CommRing R] := PowerSeries (Polynomial (Glyphs R V))
def cinder : Heat R V →ₗ[R] Heat R V:= beam (stove q)
lemma track (p : Heat R V) : cinder q p = ∑ i,∑ j,C (Polynomial.C (MvPolynomial.C (halve (q i j)))) * shaft (grain i) (shaft (grain j) p) := by
   ext1 n; simp only [cinder,coeff_beam,stove_eq,map_sum,coeff_C_mul,coeff_shaft]

def crossHeat (p t : Heat R V) := ∑ i,∑ j, C (Polynomial.C (MvPolynomial.C (halve (q i j)))) * shaft (grain i) p * shaft (grain j) t

lemma ignite (p : Heat R V) (hp : coeff 0 p=0) : cinder q (expan p)=expan p*(cinder q p + crossHeat q p p) := by
   unfold crossHeat
   simp_rw [track, shaft_expan_over _ p hp,Derivation.leibniz,shaft_expan_over _ p hp,smul_eq_mul,mul_add, Finset.mul_sum, Finset.sum_add_distrib]
   simp_rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
lemma cross_turn (s : ∀ i j, q i j=q j i) (p t : Heat R V) : crossHeat q p t=crossHeat q t p := by
   unfold crossHeat; rw [Finset.sum_comm];apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [s j]; ring
lemma cinder_prod (p t : Heat R V) : cinder q (p*t)=p*cinder q t+t*cinder q p+crossHeat q p t+crossHeat q t p := by
   simp_rw [track,crossHeat];simp only [Derivation.leibniz, _root_.map_add, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
   apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
lemma cross_expan (p t : Heat R V) (hp : coeff 0 p=0) : crossHeat q (expan p) t=expan p*crossHeat q p t := by
   unfold crossHeat; simp_rw [shaft_expan_over _ _ hp, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring

def smoke : PowerSeries (Glyphs R V) →ₗ[R] Heat R V := beam (bake q)
lemma rack_law (p : PowerSeries (Glyphs R V)) : shaft Polynomial.derivative' (smoke q p)=cinder q (smoke q p) := by ext1 n; simp only [coeff_shaft,cinder,smoke,coeff_beam]; exact bake_law ..
def early (p : Heat R V) := PowerSeries.map (Polynomial.evalRingHom 0) p
def late (p : Heat R V) := PowerSeries.map (Polynomial.evalRingHom 1) p
lemma rack_zero (p : PowerSeries (Glyphs R V)) : early (smoke q p)=p := by ext1 n; simp [early,smoke,←Polynomial.coeff_zero_eq_eval_zero]
lemma rack_finish (p : PowerSeries (Glyphs R V)) : late (smoke q p)=beam (hearth q) p := by ext1 n; simp [late,smoke,hearth_def]

/-- Connected vacuum+parameters, all orders. -/
def coal (f : PowerSeries (Glyphs R V)) : Heat R V := covelog (smoke q (expan f))
section
variable (f : PowerSeries (Glyphs R V)) (hp : coeff 0 f=0)
include hp
lemma smoke_unit : coeff 0 (smoke q (expan f))=1 := by rw [smoke,coeff_beam,expan_zero hp,bake_one]
lemma coal_base : coeff 0 (coal q f)=0 := covelog_rank (smoke_unit q f hp)
lemma coal_recovers : expan (coal q f)=smoke q (expan f) := expan_after (smoke_unit q f hp)
lemma coal_initial : early (coal q f)=f := by
   unfold early coal; rw [map_covelog _ (smoke_unit q f hp),← early,rack_zero,covelog_after hp]
lemma coal_result : late (coal q f)=covelog (beam (hearth q) (expan f)) := by
   unfold coal late; rw [map_covelog _ (smoke_unit q f hp),← late,rack_finish]
theorem coal_law : shaft Polynomial.derivative' (coal q f)=cinder q (coal q f)+crossHeat q (coal q f) (coal q f) := by
   have h:=rack_law q (expan f); rw [←coal_recovers _ _ hp] at h
   let p:=coal q f; have h0 := coal_base q f hp
   rw [shaft_expan_over _ _ h0,ignite _ _ h0] at h
   exact ((expan_unit h0).mul_right_inj).mp h
end

lemma coal_unique (p t : Heat R V) (hp : coeff 0 p=0) (ht : coeff 0 t=0) (he : early p=early t)
    (A : shaft Polynomial.derivative' p=cinder q p+crossHeat q p p)
    (B : shaft Polynomial.derivative' t=cinder q t+crossHeat q t t) : p=t := by
   apply (expan_inj hp ht).mp; ext1 n
   have h (F : Heat R V) (H : coeff 0 F=0) (T : shaft Polynomial.derivative' F=cinder q F+crossHeat q F F) : Polynomial.derivative (coeff n (expan F))=stove q (coeff n (expan F)) := by
      have h := congr_arg (coeff n) (show shaft Polynomial.derivative' (expan F)= cinder q (expan F) by rw [ignite q _ H,shaft_expan_over _ _ H,T]); simp only [coeff_shaft,cinder,coeff_beam] at h; exact h
   refine bake_unique q _ _ ?_ (h p hp A) (h t ht B)
   have hh : early (expan p)=early (expan t) := by unfold early; rw [map_expan _ hp,map_expan _ ht]; rw [show (PowerSeries.map _ _) = _ from he]; rfl
   simpa [early,Polynomial.coeff_zero_eq_eval_zero] using (congr_arg (coeff n) hh)
end YM.FormalBulk08.Wick
