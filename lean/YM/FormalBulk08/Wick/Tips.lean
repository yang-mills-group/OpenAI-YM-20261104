import YM.FormalBulk08.Wick.Cinnabar

/-! Connected graph coefficient readout including denominator for a single test. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Wick
open Series PowerSeries
open scoped Classical BigOperators
variable {R : Type*} {V : Type*} [CommRing R] [Algebra ℚ R] [Fintype V] (q : V→V→R)
variable (f t : PowerSeries (Glyphs R V)) (hp : coeff 0 f=0)
def flare : Heat R V := expan (- coal q f) * smoke q (expan f * t)

section
include hp
lemma flare_undo : expan (coal q f)*flare q f t = smoke q (expan f*t) := by unfold flare; rw [←mul_assoc,expan_mul (coal_base q f hp) (by simp only [map_neg,coal_base q f hp,neg_zero]),add_neg_cancel, root_expan,one_mul]
lemma flare_initial : early (flare q f t) = t := by
   have h : PowerSeries.map (Polynomial.evalRingHom 0) (smoke q (expan f*t))=expan f*t := rack_zero q _
   rw [←flare_undo _ _ _ hp,map_mul,map_expan _ (coal_base q f hp)] at h
   change expan (early (coal q f)) * early (flare q f t)=_ at h; rw [coal_initial q f hp] at h
   exact ((expan_unit hp).mul_right_inj).mp h
/-- Contains formal *normalized* test. Only evaluate `late` following differentiation and
linkedness; a test density divided by a prescription at zero would not satisfy this. -/
lemma flare_denominator : late (smoke q (expan f))*late (flare q f t)= late (smoke q (expan f * t)) := by rw [←flare_undo _ _ _ hp,coal_recovers _ _ hp]; unfold late; rw [map_mul]

theorem flare_deriv (s : ∀ i j,q i j=q j i) : shaft Polynomial.derivative' (flare q f t) = cinder q (flare q f t) + 2 * crossHeat q (coal q f) (flare q f t) := by
   let p:=coal q f; let u:=flare q f t
   have he:= rack_law q (expan f*t); rw [←flare_undo _ _ _ hp] at he
   change shaft Polynomial.derivative' (expan p*u) = _ at he
   let Q:= expan p; have h0 := coal_base q f hp
   have h := rack_law q (expan f); rw [←coal_recovers _ _ hp] at h
   change shaft Polynomial.derivative' Q = cinder q Q at h
   apply ((expan_unit h0).mul_right_inj).mp
   rw [Derivation.leibniz,cinder_prod, smul_eq_mul,smul_eq_mul] at he
   change Q*shaft Polynomial.derivative' u+u*(shaft Polynomial.derivative' Q)=Q*(cinder q u)+u*cinder q Q+crossHeat q Q u+crossHeat q u Q at he
   rw [cross_turn q s u Q,h,cross_expan q p u h0] at he
   refine add_right_cancel (b:=u*cinder q Q) ?_
   rw [he]; ring
end

/-- Read through power of coupling first, then through power of heat. -/
def readSlice (p : Heat R V) (m n : ℕ) : Glyphs R V := (coeff m p).coeff n
omit [Algebra ℚ R] [Fintype V] in
lemma read_initial (p : Heat R V) (m) : readSlice p m 0= coeff m (early p) := by simp [early,readSlice,Polynomial.coeff_zero_eq_eval_zero]
omit [Algebra ℚ R] [Fintype V] in
@[simp] lemma read_add (p t : Heat R V) (m n : ℕ) : readSlice (p+t) m n = readSlice p m n + readSlice t m n := by simp [readSlice]
lemma read_track (p : Heat R V) (m n : ℕ) : readSlice (cinder q p) m n= press q (readSlice p m n) := by simp [cinder,readSlice,stove_coeff]
omit [Algebra ℚ R] [Fintype V] in
lemma read_diff (p : Heat R V) (m n : ℕ) : readSlice (shaft Polynomial.derivative' p) m n= readSlice p m (n+1)*(n+1) := by rw [readSlice,coeff_shaft]; exact Polynomial.coeff_derivative ..

def atomProduct (a b : Glyphs R V) := ∑ i,∑ j, MvPolynomial.C (halve (q i j)) * MvPolynomial.pderiv i a * MvPolynomial.pderiv j b

def chartCross (p t : Heat R V) (m n : ℕ) := ∑ r∈Finset.antidiagonal m,∑ u∈ Finset.antidiagonal n, atomProduct q (readSlice p r.1 u.1) (readSlice t r.2 u.2)
lemma read_cross (p t : Heat R V) (m n : ℕ) : readSlice (crossHeat q p t) m n = chartCross q p t m n := by
   unfold chartCross atomProduct crossHeat readSlice; simp_rw [map_sum, mul_assoc,coeff_C_mul,Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,coeff_mul,coeff_shaft,Polynomial.finsetSum_coeff,Polynomial.coeff_mul, grain_coeff,Finset.mul_sum]
   -- sums route
   simp_rw [Finset.sum_comm (s:=(Finset.univ : Finset V)) (t:=Finset.antidiagonal m),Finset.sum_comm (s:=(Finset.univ : Finset V)) (t:=Finset.antidiagonal n)]
section
include hp
theorem arc_vac (m n : ℕ) : readSlice (coal q f) m (n+1) * (n+1) = press q (readSlice (coal q f) m n)+ chartCross q (coal q f) (coal q f) m n := by rw [←read_diff,coal_law q f hp,read_add,read_track,read_cross]
theorem arc_field (s : ∀ i j,q i j=q j i) (m n : ℕ) : readSlice (flare q f t) m (n+1) * (n+1)= press q (readSlice (flare q f t) m n)+2*chartCross q (coal q f) (flare q f t) m n := by simp_rw [←read_diff,flare_deriv q f t hp s,two_mul,read_add,read_track,read_cross]
end
end YM.FormalBulk08.Wick
