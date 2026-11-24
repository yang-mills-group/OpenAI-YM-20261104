import YM.FormalBulk08.Jets.Glean
import YM.FormalBulk08.Orb.Triplet

/-! Extended polynomial evaluation. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick Jets Matrix PowerSeries
open scoped BigOperators Classical
variable {V I : Type*} (x : Rays V) (y : Rays I)
def duplex : (Glyphs (Glyphs ℝ I) V) →+* ℝ:= MvPolynomial.eval₂Hom (MvPolynomial.aeval y).toRingHom x
lemma duplex_def (p : Glyphs (Glyphs ℝ I) V): duplex x y p=traceP x (MvPolynomial.map (MvPolynomial.aeval y).toRingHom p) := by
   induction p using MvPolynomial.induction_on <;> simp_all [traceP,duplex]
lemma duplex_C (a : TypeR I) : duplex x y (MvPolynomial.C a)=traceP y a := by simp [traceP,duplex]
lemma duet {p q : Glyphs (Glyphs ℝ I) V} (h : ∀ x y,duplex x y p=duplex x y q) : p=q := by
   ext1 n; apply orbit_ext; intro y
   have he (x:Rays V) := h x y
   simp_rw [duplex_def] at he; have hu := orbit_ext he; have h':=congr_arg (MvPolynomial.coeff n) hu; simp only [MvPolynomial.coeff_map] at h'; exact h'
lemma boost_flat (F : Pap I): coeff 0 (boost V F)=MvPolynomial.C (coeff 0 F) := by rw [boost,coeff_map]
lemma roam_first {W R : Type*} [CommRing R] [Algebra ℝ R] (a : W → PowerSeries R) (p : Pap W) : coeff 0 (roam ℝ a p)= MvPolynomial.aeval (fun i=>coeff 0 (a i)) (coeff 0 p) := by
   rw [← Wick.roam_level a]; unfold roam; rw [change_coeff_zero,change_coeff_zero,coeff_zero_C]

variable [Fintype V] [DecidableEq V] (H : Hull V I)
lemma toInk_value (F : Pap (V⊕I)) : duplex x y (coeff 0 (toInk H F))=traceP (Sum.elim (fun i=> x i + traceP y (H.drift i)) y) (coeff 0 F) := by
   rw [toInk,roam_first]; generalize coeff 0 F=z
   unfold traceP; induction z using MvPolynomial.induction_on with
   | C c=> simp [duplex]
   | add p q hp hq=> simp_rw [map_add,hp,hq]
   | mul_X p i hi=> simp_rw [map_mul, MvPolynomial.aeval_X,hi]; cases i with
     | inl i=> simp [fueled,duplex,boost]
     | inr i=> simp [fueled,duplex,boost]
lemma trace_base (T : Saddle ℝ V) : traceP x T.base = -(dotProduct x (T.P*ᵥ x))/2 := by
   simp only [Saddle.base,Matrix.mulVec,dotProduct,traceP,map_neg,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X,Finset.mul_sum,neg_div];
   congr 1
   simp [halve,div_eq_mul_inv, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>by ring
lemma levelDp (T : Saddle ℝ V): duplex x y (variation T I).base=traceP x T.base := by
   rw [←apply_base]; simp_rw [duplex_def];
   rw [show (MvPolynomial.map _ (MvPolynomial.map MvPolynomial.C T.base) :Glyphs ℝ V)=T.base from ?_]
   ext n; simp [MvPolynomial.coeff_map]
end YM.FormalBulk08.Orb
