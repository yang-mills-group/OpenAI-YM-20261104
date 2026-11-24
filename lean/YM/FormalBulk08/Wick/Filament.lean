import YM.FormalBulk08.Wick.Pistil

/-!
Completed-square conditional Wick is invariant under all formal coordinate changes
tangent to the identity (Jacobian and quadratic precursor retained). No choice of period or
Gaussian reference determinant presumed. This is an all-orders calculation, NOT an
identity about actual small-field densities.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries Matrix
open scoped BigOperators
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [Fintype V] [DecidableEq V] (T : Saddle R V)
lemma call_slide (c:R) (p : PowerSeries (Polynomial (Glyphs R V))) : beam T.call (PowerSeries.map (glass c) p)=PowerSeries.map (Polynomial.evalRingHom c) (beam T.sweep p) := by
   ext1 n; simp only [coeff_beam,coeff_map]
   generalize coeff n p=z
   induction z using Polynomial.induction_on' with
   | add u v hu hv=> simp_rw [map_add,hu,hv]
   | monomial i a=>
      have he : T.sweep (Polynomial.monomial i a)=Polynomial.monomial i (T.call a) := by ext k; by_cases hk:i=k <;> simp [Polynomial.coeff_monomial,hk]
      rw [he]; change T.call (Polynomial.eval _ _) = Polynomial.eval _ _; rw [Polynomial.eval_monomial, Polynomial.eval_monomial, ← _root_.map_pow MvPolynomial.C c i, mul_comm _ (MvPolynomial.C _), MvPolynomial.C_mul',map_smul,smul_eq_mul,mul_comm (c^i)]
lemma shaft_static (A : PowerSeries (Polynomial R)) (E : shaft Polynomial.derivative' A=0) (b c : R) : PowerSeries.map (Polynomial.evalRingHom b) A= PowerSeries.map (Polynomial.evalRingHom c) A := by
   ext1 n; rw [coeff_map,coeff_map];generalize h : coeff n A=z
   have H := congr_arg (coeff n) E; rw [coeff_shaft,h,map_zero] at H
   change Polynomial.derivative _=0 at H
   -- no torsion
   have hz : z=Polynomial.C (z.coeff 0) := by
      ext1 i; rcases i with (_|i)
      · simp
      have he:=congr_arg (fun p : Polynomial R=>p.coeff i) H
      simp only [Polynomial.coeff_derivative,Polynomial.coeff_zero] at he
      rw [← Nat.cast_succ] at he; simp; apply (IsUnit.mul_left_inj ?_).mp (he.trans (zero_mul (↑i.succ:R)).symm)
      simpa only [_root_.map_natCast] using ((isUnit_iff_ne_zero.mpr (by exact_mod_cast Nat.succ_ne_zero i) : IsUnit (↑i.succ:ℚ)).map (algebraMap ℚ R))
   rw [hz];simp

omit T [Algebra ℚ R] [Fintype V] [DecidableEq V] in
lemma bloom_eq (y : V→Plate R V) (F : Glyphs R V) (hy : ∀ i,coeff 0 (y i)=MvPolynomial.X i) : coeff 0 (roam R (pollen y) (C F))= Polynomial.C F := by
   simp_rw [roam_level,bloom y hy]
   induction F using MvPolynomial.induction_on with
   | C c=> simp [Polynomial.algebraMap_apply]
   | add u v hu hv=> rw [map_add,hu,hv,map_add]
   | mul_X p i hi=> rw [map_mul,MvPolynomial.aeval_X,hi,map_mul]

theorem smooth (y : V→Plate R V) (F : Plate R V) (hy : ∀ i,coeff 0 (y i)=MvPolynomial.X i) :
   beam T.call ((clock y).det * expan (roam R y (C T.base)-C T.base) * roam R y F) = beam T.call F := by
    let z:= pollen y; let d:= veins (R:=R) grain z; let v:= d⁻¹ *ᵥ (fun i=>shaft tint (z i)); let B:=C (Polynomial.C T.base); let A:= C T.base; let Δ:= roam R z A - B
    let U:= d.det * expan Δ * roam R z F
    have hp : coeff 0 Δ=0 := by rw [show Δ=_ from (rfl: Δ=roam R z (C T.base)-C (Polynomial.C T.base)),map_sub,bloom_eq y _ hy]; simp [B]
    have h : shaft tint U=∑ k,(shaft (grain k) (v k*U)+shaft (grain k) B*v k*U) := by
       refine blade _ _ _ _ (pilot _ _ _ (isUnit_iff_constantCoeff.mpr ?_)) (fun i j k=>grain_turn ..) (fun i j=>Eq.symm (grain_pin ..)) F A B ?_ hp
       · rw [veins_zero y hy]; exact isUnit_one
       rw [show B= _ from (rfl:B=C (Polynomial.C _)),shaft_C,tint_apply,Polynomial.derivative_C,map_zero]
    have hz : shaft Polynomial.derivative' (beam T.sweep U)=0 := by
       rw [shaft_tint,h,map_sum]; refine Finset.sum_eq_zero fun i _=> ?_
       rw [mul_assoc (shaft _ B)]; exact T.icon (v i*U) i
    have hh := shaft_static _ hz 1 0
    rw [←call_slide,←call_slide] at hh
    have h0 : PowerSeries.map (glass (0:R)) U=F := by
       change PowerSeries.map _ (d.det * expan Δ * roam R (pollen y) F)= F;rw [map_mul,map_mul, map_expan _ hp]
       change PowerSeries.map _ ((veins (R:=R) _ _).det) * expan (PowerSeries.map _ (roam R (pollen y) (C T.base)-C (Polynomial.C _))) * _=F
       simp_rw [map_sub,roam_glass,close_pollen,virgin]; simp [z,glass_veins,close_pollen, clock_own,show ∀ p : Glyphs R V, glass (0:R) (Polynomial.C p)=p from fun p=>by simp [glass]]
    have h1 : PowerSeries.map (glass (1:R)) U=(clock y).det * expan (roam R y (C T.base)-C T.base)*roam R y F := by
       unfold U;rw [map_mul,map_mul,map_expan _ hp]; unfold d Δ B A z; simp_rw [map_sub,roam_glass,glass_veins, open_pollen]; simp [glass]
    rwa [h1,h0] at hh
end YM.FormalBulk08.Wick
