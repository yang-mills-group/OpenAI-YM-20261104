import YM.FormalBulk08.Wick.Shield

/-! Endpoints of the formal homotopy. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries Matrix
open scoped BigOperators
variable {R V S : Type*} [CommRing R] [CommRing S] [Algebra R S]
abbrev Plate (R V : Type*) [CommRing R] := PowerSeries (Glyphs R V)
variable (y : V→ Plate R V)

def glass (c:R) : Polynomial (Glyphs R V) →+* Glyphs R V := Polynomial.evalRingHom (MvPolynomial.C c)
lemma grain_glass (c:R) (p : Polynomial (Glyphs R V)) (i:V) : glass c (grain i p)=MvPolynomial.pderiv i (glass c p) := by
   induction p using Polynomial.induction_on' with
   | add u v ha hv=> simp only [map_add,ha,hv]
   | monomial n a=>
      have h : grain i (Polynomial.monomial n a)=Polynomial.monomial n (MvPolynomial.pderiv i a) := by ext m; by_cases hm:n=m <;> simp [Polynomial.coeff_monomial,hm]
      rw [h]; simp [glass,Derivation.leibniz_pow];ring
lemma shaft_glass (c:R) (p : PowerSeries (Polynomial (Glyphs R V))) (i:V) : PowerSeries.map (glass c) (shaft (grain i) p) = shaft (MvPolynomial.pderiv i) (PowerSeries.map (glass c) p) := by ext1 n; simp [grain_glass]
lemma roam_glass (c:R) (y : V → PowerSeries (Polynomial (Glyphs R V))) (p : Plate R V) : PowerSeries.map (glass c) (roam R y p)=roam R (fun i=> PowerSeries.map (glass c) (y i)) p := by
   unfold roam; rw [change_beam, show (PowerSeries.map (glass c)).comp (insertAt R y)=_ from ?h];
   case h => ext <;> simp [glass]
lemma virgin (a : Plate R V) : roam R (fun i => C (MvPolynomial.X i : Glyphs R V)) a=a := by
   unfold roam; rw [show (fun i:V=>C (MvPolynomial.X i : Glyphs R V))= PowerSeries.C ∘ MvPolynomial.X from rfl,const_insertAt, pure_map, show (MvPolynomial.aeval MvPolynomial.X).toRingHom=RingHom.id (Glyphs R V) from (by ext <;> simp)]; simp
lemma roam_level (z : V → PowerSeries S) (F : Glyphs R V) :
    coeff 0 (roam R z (C F))=MvPolynomial.aeval (fun i => coeff 0 (z i)) F := by
   induction F using MvPolynomial.induction_on with
   | C c=> rw [roam,change_C,insert_C,coeff_zero_C,MvPolynomial.aeval_C]
   | add p q hp hq=> simp_rw [map_add,hp,hq]
   | mul_X p i hi=>
      simp_rw [show (C (p * MvPolynomial.X i))=C p*C (MvPolynomial.X i) from map_mul _ _ _, map_mul (roam R z), coeff_zero_eq_constantCoeff_apply _]
      rw [map_mul,map_mul (MvPolynomial.aeval _),←coeff_zero_eq_constantCoeff_apply,←coeff_zero_eq_constantCoeff_apply]; simp_rw [←coeff_zero_eq_constantCoeff_apply,hi,MvPolynomial.aeval_X,roam,change_C,insert_X]

def pollen (y : V→Plate R V) : V→PowerSeries (Polynomial (Glyphs R V)) := fun i=>
     let x:=C (Polynomial.C (MvPolynomial.X i))
     x + C Polynomial.X * (PowerSeries.map Polynomial.C (y i)-x)
lemma open_pollen (i) : PowerSeries.map (glass (1:R)) (pollen y i)=y i := by
   have h (p:Plate R V) : PowerSeries.map (glass (1:R)) (PowerSeries.map Polynomial.C p)=p := by ext1 n; simp [glass]
   unfold pollen;simp_rw [map_add,map_mul,map_sub,PowerSeries.map_C,h]; simp [glass]
lemma close_pollen (i) : PowerSeries.map (glass (0:R)) (pollen y i)=C (MvPolynomial.X i) := by simp [pollen,glass]
lemma bloom (h : ∀ i,coeff 0 (y i)=MvPolynomial.X i) (i:V) : coeff 0 (pollen y i)=Polynomial.C (MvPolynomial.X i) := by
   unfold pollen; dsimp only;rw [map_add,coeff_C_mul,map_sub,coeff_map,h];simp
lemma grain_turn (i j:V) (p : PowerSeries (Polynomial (Glyphs R V))) : shaft (grain i) (shaft (grain j) p) = shaft (grain j) (shaft (grain i) p) := by ext i' k s; simp [alphabet_swap (p:=((coeff i') p).coeff k) i j]
lemma grain_pin (i:V) (p : PowerSeries (Polynomial (Glyphs R V))) : shaft tint (shaft (grain i) p)=shaft (grain i) (shaft tint p) := by
   ext1 n; ext1 k; simp only [coeff_shaft,grain_coeff, tint_apply,Polynomial.coeff_derivative,←Nat.cast_succ]
   rw [Derivation.leibniz]; simp [mul_comm]
variable [Fintype V] [DecidableEq V]
def clock (y : V→Plate R V) := veins (R:=R) MvPolynomial.pderiv y
lemma glass_veins (z : V→ PowerSeries (Polynomial (Glyphs R V))) (c:R) : PowerSeries.map (glass c) (veins (R:=R) grain z).det=(clock (fun i=>PowerSeries.map (glass c) (z i))).det := by
   rw [RingHom.map_det]; congr 1; ext1 i j; dsimp only [veins,Matrix.of_apply,RingHom.mapMatrix_apply,Matrix.map_apply]; exact shaft_glass ..
lemma clocks_flat (h : ∀ i,coeff 0 (y i)=MvPolynomial.X i) : PowerSeries.constantCoeff (clock y).det=1 := by
   rw [RingHom.map_det,show PowerSeries.constantCoeff.mapMatrix (clock y)=1 from ?_,Matrix.det_one]
   ext i j n; simp [clock,veins,← coeff_zero_eq_constantCoeff_apply,h,Matrix.one_apply,Pi.single_apply]
lemma veins_zero (h : ∀ i,coeff 0 (y i)=MvPolynomial.X i) : PowerSeries.constantCoeff (veins (R:=R) grain (pollen y)).det=1 := by
   rw [RingHom.map_det,show PowerSeries.constantCoeff.mapMatrix (veins (R:=R) grain (pollen y))=1 from ?_,Matrix.det_one]
   ext i j n m; rw [RingHom.mapMatrix_apply]; change MvPolynomial.coeff m ((_ : Polynomial _).coeff n)=_
   simp only [veins,Matrix.map_apply, Matrix.of_apply, ←coeff_zero_eq_constantCoeff_apply,coeff_shaft,bloom y h,Matrix.one_apply]
   by_cases he:i=j
   · subst i; rcases n with (_|n) <;> simp [Polynomial.coeff_one]
   rcases n with (_|n) <;> simp [he]
omit [Fintype V] in
lemma clock_own : (clock (fun i => C (MvPolynomial.X i : Glyphs R V)))=1 := by
   ext i j n b; by_cases hi:i=j <;> simp [clock,veins,Matrix.one_apply,hi]
end YM.FormalBulk08.Wick
