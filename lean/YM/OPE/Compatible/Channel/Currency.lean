import YM.OPE.Compatible.Channel.Seat
/-! Materialize support and summability. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Set Lattice Laurent MeasureTheory RG Finset Next.Free Bloch Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r n:ℕ} {I J T:Type*}[Fintype T][Fintype I] {L c f:Side}{A:Cross L T I}{η U:ℝ}
namespace Script
open Page
variable (h:A.strip η U) (he:0<η)
include h he
abbrev zest (U:ℝ):=‖U‖
def regionB (I:Type*)[Fintype I](η U:ℝ)(b n m:ℕ):ℝ:= Fintype.card (Ink I n)* (2+8*n+n*b:ℕ)^m*((widthCost η m*zest U)^n) -- T unused
omit [Fintype T] in
lemma merchant (m:ℕ)(a:Cover)(x:Page T r) : soot m (call A a x) (figure m x * regionB I η U (size a) r m):=by
   let p:=xy (slide a x); let z:= parcelY (fun _ :Fin r=>0) L p
   have hh := heft (fun _ : Fin r=>0) (L:=L) (fun i=>by simp [size]) p
   have hx: (size p:ℝ) / L.val ≤ size x.xy + r*size a:=by
       have heq : size p ≤ size x.xy+r*size a:=by have H:= slide_price x a; change 1+size p ≤ 1+size x.xy+_ at H; omega
       apply (div_le_self (by positivity) (by exact_mod_cast L.property)).trans; exact_mod_cast heq
   let Z:=2+8*r+r*size a; have ha : 1≤ notch x.xy:= notch_one x.xy
   have hb : poise m z ≤ (Z:ℝ)^m *figure m x:=by
      unfold poise figure; rw [poise,← mul_pow]; apply pow_le_pow_left₀ (by positivity); have hz : (size z:ℝ)≤(size x.xy:ℝ)+r*8+r*size a:= by linarith only [hh,hx]
      unfold notch Z; push_cast; nlinarith only [hz,Nat.cast_nonneg (α:=ℝ) (size x.xy),Nat.cast_nonneg (α:=ℝ) r,Nat.cast_nonneg (α:=ℝ) (size a), (show 0 ≤ (r:ℝ)*size a*size x.xy by positivity)]
   apply (charges h he x a m).tips; unfold regionB; let n:ℝ:= Fintype.card (Ink I r); let Hp:= widthCost η m; have hg:0≤Hp:= zero_le_one.trans (widthCost_ge he _) -- issue sign U if arrays empty T/I. if T or I empty.
   by_cases ht:IsEmpty I
   · cases r with
     | zero=> simpa [Z,z,p,mul_comm] using hb
     | succ r=>
       have hP : n=0:=by unfold n Ink;simp
       change n * (_*_) ≤ _*(n*_*_); rw [hP]; simp
   by_cases hQ:IsEmpty T
   · cases r with
     | zero=>simpa [Z,z,p,mul_comm] using hb
     | succ r=>exact isEmptyElim (x 0).2
   have hi : Nonempty I:= not_isEmpty_iff.mp ht; have hk: Nonempty T:=not_isEmpty_iff.mp hQ
   let f:=h (0,Classical.arbitrary T) (Classical.arbitrary I)
   have hp:0 ≤ U:= (tsum_nonneg f.1).trans f.2.2
   rw [zest, Real.norm_of_nonneg hp]; change _ ≤ figure m x *(n*((Z:ℕ):ℝ)^m* ((Hp*U)^r)); linarith only [mul_le_mul_of_nonneg_right hb (mul_nonneg (show 0 ≤ n by unfold n; positivity) (pow_nonneg (mul_nonneg hg hp) r))]
-- note Z nat expression target coercion maybe defin.
variable {u:ℝ}{m:ℕ}(p:Script T r)(a:Cover) (hp: soot m p u)
include hp
omit [Fintype T] in
lemma cashmoves : Sack (fun i:Page T r ×Page I r=> figure m i.2) (uncurry fun i j=>p i * call A a i j) (u * regionB I η U (size a) r m):=by
    refine Sack.carried hp (fun i=> merchant h he m a i) ?_; unfold regionB; have hx:0 ≤ widthCost η m:= zero_le_one.trans (widthCost_ge he m); unfold zest;positivity
omit [Fintype T] in
lemma counterflow : soot m (countermove A a p) (u *regionB I η U (size a) r m):=(cashmoves h he p a hp).draw (payer m)
omit [Fintype T] in
lemma valueFlow {n:Side} (q:Fin r→deck I n) (y:Site n): scribe y (countermove A a p) q=∑' i,p i*scribe y (call A a i) q:=by
   unfold scribe countermove
   let f(i j):=p i*call A a i j
   have hs:= ((cashmoves h he p a hp).mass (fun i=>payer m i.2)).2.1
   let F i j:= f i j*render y j q
   have hh :Summable (uncurry F):= by
       apply (hs.mul_right (∏ i,‖q i‖)).of_norm_bounded; intro i; change ‖f i.1 i.2 * _‖≤ _; rw [norm_mul]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); unfold render; rw [norm_prod]; apply prod_le_prod (fun i _=> norm_nonneg _); intro i _; exact norm_le_pi_norm ..
   calc
     _ = ∑' j,∑' i,F i j:= tsum_congr fun j=>by rw [← tsum_mul_right]
     _ = ∑' i, ∑' j, F i j:= hh.tsum_comm
     _ = _:=tsum_congr fun i=> by unfold F f; simp_rw [mul_assoc,tsum_mul_left]
end Script
end YM.OPE.Flume
