import YM.FormalBulk08.Jets.Tallow

/-! The external alphabet. Treat it separately as scalars in the Gaussian,
so that Ward can change every chart simultaneously. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Orb
open Series Wick PowerSeries Matrix
open scoped BigOperators
variable {V I J : Type*}
abbrev Pap (I : Type*) := Plate ℝ I
abbrev TypeR (I : Type*) := Glyphs ℝ I
abbrev Ink (V I : Type*) := Plate (TypeR I) V
def boost (V : Type*) {I : Type*} : Pap I →+* Ink V I := PowerSeries.map MvPolynomial.C
lemma roam_boost (y : V→Ink V I) (F : Pap I) : roam (TypeR I) y (boost V F)= boost V F := by
   unfold boost roam; rw [change_after,show (insertAt (TypeR I) y).comp MvPolynomial.C=C.comp MvPolynomial.C from RingHom.ext fun _=>by simp,pure_map]

-- A spectator variable hom can go INSIDE the expectation.
def tri (z : I→Pap J) (V : Type*) := MvPolynomial.eval₂Hom ((boost V).comp (insertAt ℝ z)) (fun i:V => C (MvPolynomial.X (R:=TypeR J) i))
def teleport (z : I→Pap J) : Ink V I →+* Ink V J := changeBy (tri z V)
@[simp] lemma teleport_C (z : I→Pap J) (r : Glyphs (TypeR I) V) : teleport z (C r)=tri z V r := change_C ..
@[simp] lemma teleport_X (z : I→Pap J) : teleport (V:=V) z X=X := change_X _
lemma teleport_boost (z : I→Pap J) (F : Pap I) : teleport (V:=V) z (boost V F) = boost V (roam ℝ z F) := by
   unfold teleport boost roam; rw [change_beam,change_after]; rw [show (tri z V).comp MvPolynomial.C=_ from ?hex]
   case hex => ext <;> simp [tri,boost]

section
variable [DecidableEq V] [Fintype V]
def variation (T : Saddle ℝ V) (I : Type*) : Saddle (TypeR I) V :=
  { q := MvPolynomial.C.mapMatrix T.q
    P := MvPolynomial.C.mapMatrix T.P
    ok i j := by simp [T.ok i j]
    valid i j := by simp [T.valid i j]
    inv := by rw [←map_mul, T.inv,map_one] }
lemma vanish_mapped (T : Saddle ℝ V) (p : TypeR V) : (variation T I).call (MvPolynomial.map MvPolynomial.C p)= MvPolynomial.C (σ:=I) (T.call p) := by
   have he : (variation T I).q = Matrix.of (fun i j=>MvPolynomial.C (T.q i j)) := by ext; simp [variation]
   simp only [Saddle.call, he]; exact (moment_map T.q MvPolynomial.C p).symm
lemma apply_base (T : Saddle ℝ V): MvPolynomial.map MvPolynomial.C T.base=(variation T I).base := by
   simp_rw [Saddle.base, map_neg,map_sum,map_mul,MvPolynomial.map_C,MvPolynomial.map_X, halve_map]; simp only [variation,RingHom.mapMatrix_apply, Matrix.map_apply]
omit [DecidableEq V] [Fintype V] in
lemma teleport_real (z : I→Pap J) (p : TypeR V) : teleport (V:=V) z (C (MvPolynomial.map MvPolynomial.C p))=C (MvPolynomial.map MvPolynomial.C p) := by
   induction p using MvPolynomial.induction_on with
   | C c=> simp [tri,boost]
   | add p q hp hq=> simp_rw [map_add,hp,hq]
   | mul_X p i hp=>
     -- simp
     simp only [map_mul,MvPolynomial.map_X,hp]; simp [tri,boost]
lemma teleport_base (T : Saddle ℝ V) (z : I→Pap J) : teleport (V:=V) z (C (variation T I).base)= C (variation T J).base := by simp_rw [←apply_base]; exact teleport_real z _
lemma suction (T : Saddle ℝ V) (p : Ink V I) (u : Pap I) :
     beam (variation T I).call (boost V u * p)=u*beam (variation T I).call p := by
   ext1 i; simp [boost,coeff_mul,MvPolynomial.C_mul'] -- dot polynomial

lemma blade_case (T : Saddle ℝ V) (z : I→ Pap J) (p : Glyphs (TypeR I) V) :
    beam (variation T J).call (teleport z (C p))= roam ℝ z (C ((variation T I).call p)) := by
   -- use monomial at external coeff map
   induction p using MvPolynomial.induction_on' with
   | add p q hp hq=>simp_rw [map_add,hp,hq]
   | monomial n a=>
      let f:= MvPolynomial.monomial n (1:ℝ)
      have h : MvPolynomial.monomial n a=MvPolynomial.C a*MvPolynomial.map MvPolynomial.C f := by simp [f,MvPolynomial.C_mul_monomial]
      rw [h]; rw [map_mul,map_mul,show (C (MvPolynomial.C a) : Ink V I)= boost V (C a) by simp [boost],teleport_boost, teleport_real,suction]
      simp_rw [beam_C, vanish_mapped,MvPolynomial.C_mul',map_smul,vanish_mapped, smul_eq_mul,map_mul]
      congr 1; simp [roam]
lemma vacuum_commutes (T : Saddle ℝ V) (z : I→Pap J) (F : Ink V I) :
    beam (variation T J).call (teleport z F)=roam ℝ z (beam (variation T I).call F) := by
   apply Through.top; intro n
   have h1 : Through n (teleport z F) (teleport z (∑ i ∈ Finset.range (n+1), C (coeff i F) * X^i)) := Through.change_congr (tri z V) (dict F n)
   let p:= beam (variation T I).call F
   refine Through.trans (beam_through (variation T J).call h1) (Through.trans ?_ (liquid (insertAt ℝ z) p n).symm)
   simp_rw [map_sum,map_mul,map_pow,teleport_X]
   have h (G : Ink V J) (i) : beam (variation T J).call (G*X^i)=beam (variation T J).call G*X^i := by
      ext1 j; simp only [coeff_beam,coeff_mul_X_pow']; split_ifs <;> simp
   simp_rw [h,blade_case]
   unfold p; simp_rw [coeff_beam]; unfold roam; simp only [change_C]; exact Through.exact_eq _ _
end
end YM.FormalBulk08.Orb
