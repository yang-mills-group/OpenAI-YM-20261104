import YM.FormalOPE.RG10.Wing.Rush
/-! # Power series change of fields at fixed formal parameter, ring identities applied
 only on finite petal families. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Wing.Facets
open Function PowerSeries Finset Route Route.mapCoeff HStein
open scoped Topology BigOperators Classical

variable {I B J : Type} (P:Channel I) (p:Packet I) (u:I→Channel B) (v:B→Channel J) (t:ℕ)
lemma through {k:ℕ} {p q:Channel I} (he:Through k p q): Through k (replot u p) (replot u q):= near_aux (f:=(MvPolynomial.aeval u:Packet I→ₐ[ℂ] Channel B).toRingHom) he
lemma grain (c:ℂ) : (PowerSeries.C (MvPolynomial.C (σ:=I) c))= algebraMap ℂ (Channel I) c:= by apply PowerSeries.ext; intro k; cases k <;> simp [Algebra.algebraMap_eq_smul_one,coeff_C]; exact Algebra.algebraMap_eq_smul_one c -- inspect
lemma rules (c:ℂ) : replot u (algebraMap ℂ (Channel I) c) = algebraMap ℂ (Channel B) c:= by rw [←grain,replot_constant,MvPolynomial.aeval_C]
lemma radical : monomial t p = X^t * C p:= by rw [X_pow_eq, ← monomial_zero_eq_C_apply, monomial_mul_monomial, one_mul, add_zero]
lemma spine : replot u X = X := by nth_rw 1 [X_eq]; change mapCoeff.push (MvPolynomial.aeval u:Packet I→ₐ[ℂ]Channel B).toRingHom _ = _; rw [push_mono,map_one,pow_one,mul_one]
lemma paper : Through t P (∑ i∈range (t+1), monomial i (coeff i P)) := by intro i hi; rw [map_sum]; simp [coeff_monomial,hi]
lemma hangs (i:I) : replot u (HStein.sprout i)=u i:= by rw [HStein.sprout,replot_constant,MvPolynomial.aeval_X]
lemma jag : replot u (X^t : Channel I)=X^t:= by rw [map_pow,spine]
-- factorizable onto all finite reports
lemma summit : replot v (replot u P)=replot (fun i=> replot v (u i)) P:= by
 have hv (p:Packet I): replot v (replot u (C p))=replot (fun i=>replot v (u i)) (C p):= by
    induction p using MvPolynomial.induction_on with
    | C c=> rw [grain,rules,rules,rules]
    | add p q hp hq => rw [map_add,map_add,map_add,map_add,hp,hq]
    | mul_X p i hp =>
       rw [map_mul,map_mul,map_mul,map_mul,hp,show C (MvPolynomial.X (R:=ℂ) (σ:=I) i)=sprout i from rfl, hangs, hangs]
 let f:= fun i=>replot v (u i)
 have h (p:Packet I)(n:ℕ): replot v (replot u (monomial n p))=replot f (monomial n p):= by rw [radical,map_mul,map_mul,map_mul,jag,jag,jag,hv]
 apply PowerSeries.ext; intro i; let p x := monomial x (coeff x P); let q:=∑ x∈range (i+1), p x
 rw [through v (through u (paper P i)) i le_rfl, through f (paper P i) i le_rfl]; congr 1
 change replot v (replot u q) = replot f q; unfold q; rw [map_sum,map_sum,map_sum]; exact sum_congr rfl (fun x _=>h _ _)
end YM.FormalOPE.RG10.Wing.Facets
