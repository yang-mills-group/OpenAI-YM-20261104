import YM.WilsonCoeffUV.Stable.RefundEstimate

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedForwardStep
open WilsonCoeffUV WilsonCoeffUV.Cosmos
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost
open scoped BigOperators Classical
variable {G:Gauge}{h:ℕ}{F:Labels.Frame G h}
def allowance (n:Side)(h:ℕ):ℝ:=(n.val:ℝ)^h
def coupon (n:Side)(h:ℕ):ℝ:=(allowance n h)⁻¹
theorem enough (n:Side)(h:ℕ):1≤allowance n h:=one_le_pow₀ (by exact_mod_cast n.property)
theorem coupon_pos (n:Side)(h:ℕ):0<coupon n h:=inv_pos.mpr (lt_of_lt_of_le zero_lt_one (enough n h))
theorem coupon_le (n:Side)(h:ℕ):coupon n h≤1:=inv_le_one_of_one_le₀ (enough n h)

theorem line (c:ℝ)(M:Coil F)(e:ℕ)(x y:Alma F):
    lineS (c • M) e x y=c*lineS M e x y:=by
  change coeff e (c • M x y) = c*coeff e (M x y)
  rw [map_smul,smul_eq_mul]

theorem spot {n:Side}{M:Wall F}(lease:leaseM n F M)(i j:Alma F)(diff:i≠j)
    (up:highUp F i≤highUp F j):M i j=0:=by
  rcases lt_trichotomy (valence F i) (valence F j) with below | same | above
  · exact False.elim ((not_lt_of_ge up) (rise_slot i j below))
  · have w:weight F i≤weight F j:=by simpa only [highUp,same,Nat.add_le_add_iff_left] using up
    exact (lease.2 i j same w).trans (if_neg diff)
  · exact lease.1 i j (by simpa using above)

theorem step (n:Side)(P Q:Coil F)(a b:Cost)
    (p:leaseM n F (lineS P 0))(q:leaseM n F (lineS Q 0)):
    swan F (lineS (coupon n h • Chars F a P) 0) (lineS (coupon n h • Chars F b Q) 0):=by
  refine ⟨?_,?_,?_,?_⟩
  · intro i j diff up;rw [line,maxStroke,spot p i j diff up,mul_zero]
  · intro i j diff up;rw [line,maxStroke,spot q i j diff up,mul_zero]
  · intro i;rw [line,line,maxStroke,maxStroke,p.2 i i rfl le_rfl,q.2 i i rfl le_rfl]
  · intro i;rw [line,maxStroke,p.2 i i rfl le_rfl,if_pos rfl,Real.norm_of_nonneg
      (mul_nonneg (coupon_pos n h).le (zero_le_one.trans (matPow₁ n i)))]
    have n1:(1:ℝ)≤n.val:=by exact_mod_cast n.property
    have bound:matPow n i≤allowance n h:=pow_le_pow_right₀ n1 (Nat.sub_le ..)
    have positive:0<allowance n h:=lt_of_lt_of_le zero_lt_one (enough n h)
    calc _≤coupon n h*allowance n h:=mul_le_mul_of_nonneg_left bound (coupon_pos n h).le
         _=1:=inv_mul_cancel₀ positive.ne'

theorem agree (P Q:ℕ→Coil F)(n:ℕ)(same:∀i<n,P i=Q i):steepen P n=steepen Q n:=by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [steepen,steepen,same n (by omega),ih (fun i hi=>same i (by omega))]

theorem head (P:ℕ→Coil F)(n:ℕ):hillcrest P (n+1)=P 0*hillcrest (fun j=>P (j+1)) n:=by
  induction n with
  | zero=>simp [hillcrest]
  | succ n ih=>rw [hillcrest,ih,hillcrest,mul_assoc]

theorem reverse (P:ℕ→Coil F)(n:ℕ):
    steepen (fun j=>P (n-1-j)) n=hillcrest P n:=by
  induction n generalizing P with
  | zero=>rfl
  | succ n ih=>
    rw [steepen,head,show n+1-1-n=0 by omega,←ih (fun j=>P (j+1))]
    congr 1
    apply agree
    intro i hi
    dsimp
    congr 1
    omega

theorem restore (a:ℕ→ℝ)(P:ℕ→Coil F)(n:ℕ):
    hillcrest (fun i=>a i • P i) n=(∏i∈Finset.range n,a i) • hillcrest P n:=by
  induction n with
  | zero=>simp [hillcrest]
  | succ n ih=>rw [hillcrest,ih,hillcrest,Finset.prod_range_succ,smul_mul_smul_comm]

end YM.Integration.WilsonIndependentFittedForwardStep
