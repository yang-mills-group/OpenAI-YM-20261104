import YM.FormalBulk08.Plait.Rect

/-! Hit exponent orders k=1,2 in external valence metric, isolate
marginal trace before using the finite-period assembler. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Wick Orb Series Jets PowerSeries
open Matrix (of)
open scoped BigOperators Topology Classical Matrix
variable {R V I:Type*} [CommRing R] [Algebra ℚ R]
lemma bearing_one (p: PowerSeries R)(h:coeff 0 p=0): coeff 1 (expan p)=coeff 1 p:= by
    rw [(til_expan h (le_refl 1)).apex];simp [tray,Finset.sum_range_succ]
lemma kilo (a b : R): halve (a*b)=halve a * b:= by unfold halve;ring
lemma kilo_plus (a b : R): halve (a+b)=halve a+ halve b:= by unfold halve;ring
lemma kilo_neg (a:R): halve (-a)= -halve a:= by unfold halve;ring
lemma sock_adds {T:Type*} (f:T→R)(A:Finset T): halve (∑ x∈A,f x)=∑ x∈A,halve (f x):= by simp [halve,Finset.mul_sum]
omit [Algebra ℚ R] in lemma kilo_succ (p : PowerSeries R)(h: coeff 0 p=0): coeff 2 (p^2)=coeff 1 p*coeff 1 p:= by
   rw [pow_two,coeff_mul, Finset.sum_eq_single (1,1)]
   intro a ha hp; have hh:=Finset.mem_antidiagonal.mp ha; by_cases hz:a.1=0
   · rw [hz,h,zero_mul]
   have he : a.2=0:= by by_contra hu;apply hp; apply Prod.ext <;> dsimp <;> omega
   rw [he,h,mul_zero]
   norm_num
lemma bearing_two (p: PowerSeries R)(h:coeff 0 p=0): coeff 2 (expan p)=coeff 2 p+ halve ((coeff 1 p)^2):= by
    rw [(til_expan h (le_refl 2)).apex]; simp [tray,Finset.sum_range_succ,halve]; norm_num [Nat.factorial,pow_two]
    rw [show (algebraMap ℚ R⟦X⟧) (1/2)= PowerSeries.C ((algebraMap ℚ R) (1/2)) from IsScalarTower.algebraMap_apply ℚ R _ _,coeff_C_mul,←sq p,kilo_succ p h]

lemma returning_one (p:PowerSeries R)(h:coeff 0 p=1): coeff 1 (covelog p)=coeff 1 p:=by nth_rw 2 [←expan_after h]; rw [bearing_one _ (covelog_rank h)]
lemma returning_two (p:PowerSeries R)(h:coeff 0 p=1): coeff 2 (covelog p)=coeff 2 p-halve ((coeff 1 p)^2):= by
   have hx:=bearing_two (covelog p) (covelog_rank h);rw [expan_after h,returning_one p h] at hx; rw [hx]; ring
variable [Fintype V] [DecidableEq V]
-- Rental estimates and curvature pieces
omit [DecidableEq V] in lemma Rental.moment {n:ℕ}{p:Pairs V I}(Q:V→V→ℝ)(h:Rental p n): ((Wick.moment (fun a b=> MvPolynomial.C (Q a b))) p).totalDegree≤n:= by
    let T:= Wick.moment (fun a b=>MvPolynomial.C (Q a b): V→V→TypeR I); change (T p).totalDegree≤n
    rw [show p=∑ m∈p.support,MvPolynomial.monomial m (p.coeff m) from p.as_sum,map_sum];apply graded_price; intro i _
    have he: T (MvPolynomial.monomial i (p.coeff i))=p.coeff i* MvPolynomial.C ((Wick.moment Q) (MvPolynomial.monomial i (1:ℝ))) := by
       rw [show MvPolynomial.monomial i (p.coeff i)=MvPolynomial.C (p.coeff i)*MvPolynomial.map MvPolynomial.C (MvPolynomial.monomial i (1:ℝ)) by simp [MvPolynomial.C_mul_monomial]]
       rw [MvPolynomial.C_mul',map_smul,smul_eq_mul]; rw [moment_map]
    rw [he]; exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C];exact h i) -- add_zero
lemma op_one (T : Hull V I)(p:Pap (V⊕I))(h:Solved T p): coeff 1 (out T p)= (variation T.saddle I).call (coeff 1 (positive T p)) := by
    rw [out,map_add,coeff_C, if_neg (by omega),zero_add,returning_one _ (voice T p h),vocal, coeff_beam,bearing_one _ (plur T p h)]
lemma beam_half (L:Saddle (TypeR I) V)(p:Pairs V I): L.call (halve p)=halve (L.call p):= by
   let a:= algebraMap ℚ (TypeR I) (1/2); have he:(algebraMap ℚ (Pairs V I)) (1/2)=MvPolynomial.C a:= by rw [IsScalarTower.algebraMap_apply ℚ (TypeR I)]; rfl
   rw [halve, he, MvPolynomial.C_mul',map_smul,smul_eq_mul];rfl
lemma op_two (T:Hull V I)(p:Pap (V⊕I))(h:Solved T p):
       let A:=(variation T.saddle I).call
       let f:=coeff 1 (positive T p); coeff 2 (out T p)= A (coeff 2 (positive T p)) + halve (A (f*f)) -halve ((A f)*(A f)):= by
    intro A f; rw [out,map_add,coeff_C, if_neg (by omega),zero_add,returning_two _ (voice T p h),vocal,coeff_beam,bearing_two _ (plur T p h),coeff_beam,bearing_one _ (plur T p h),sq,sq,map_add,beam_half]
lemma op_coeff (T:Hull V I)(p:Pap (V⊕I))(n:ℕ)(h:n≠0): coeff n (positive T p)=coeff n (toInk T p) := by
    unfold positive; rw [map_sub,map_sub]; simp only [boost,coeff_C,coeff_map,if_neg h,map_zero,sub_zero]
-- covariance removes a pure external constant in any coefficient.
lemma tilt_drop (Z:Saddle (TypeR I) V)(A:Pairs V I)(a:TypeR I): let T:=Z.call; let C:=MvPolynomial.C a+A
    halve (T (C*C))-halve (T C*T C)=halve (T (A*A))-halve (T A*T A):= by
    intro T F; let c:=MvPolynomial.C (σ:=V) a
    have ht:T c=a:=moment_C ..; have hh (p:Pairs V I):T (c*p)=a*T p:= by rw [show c*p=a • p from MvPolynomial.C_mul' ..,map_smul,smul_eq_mul]
    unfold F; change _=_; rw [show (c+A)*(c+A)=c*c+c*A+c*A+A*A by ring]; simp_rw [show ∀(x y : Pairs V I),T (x+y)=_ from fun x y=>map_add T ..]
    change halve (T (c*c)+T (c*A)+T (c*A)+T (A*A))-halve ((T c+T A)*(T c+T A))=_; rw [hh,hh,ht]; unfold halve; ring
end YM.FormalBulk08.Plait
