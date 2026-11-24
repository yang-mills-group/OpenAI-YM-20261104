import YM.X.Chir.Stereo
/-! # shifted convolution transpose cost, uniform in gravity. + spin mean term. -/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e a b c:ℝ}
local notation "D"=> Interval.mass
local notation "p"=> fund
local notation "S" => Site n
local notation "ε"=>epsilon q
local notation "L"=>(atTop:Filter ℕ)
open Real (sqrt)
variable (x y z:Site n)(i:Axis)
lemma pureM (h:R ≤ D x y) (hx:0<R): p (k+1) x y ≤ R⁻¹*p k x y:= by unfold fund; have he:=pay_pos x y; rw [pow_succ']; gcongr
lemma bind₃ (h:D x z≤ R)(ht: R≤ D x y / 2): p 3 y z ≤ 8 * p 3 x y:= by
   have hx:= tip x z y; rw [comm z y] at hx; convert! justice (k:=3) x y y z 2 (by linarith only [h,hx,ht]) using 1;norm_num
lemma shift_step (f:S→ℝ)(h:Paying x 3 c f)(he:c≥0): Paying x 3 (8*c) (fun y:S=> f (y+step i)):= by
   intro y; refine (h _).trans ?_; rw [mul_comm 8 c, mul_assoc]; gcongr; convert! justice (k:=3) x y x (y+step i) 2 ?_ using 1; norm_num; linarith only [(stride x y i).1,mass_pos x (y+step i)] -- nested
lemma shift_prev (f:S→ℝ)(h:Paying x k c f)(he:c≥0): Paying x k (c*2^k) (fun y:S=> f (y-step i)):= by
   intro y; refine (h _).trans ?_; rw [mul_assoc]; gcongr; apply justice; have hx:= (stride x (y-step i) i).2; rw [sub_add_cancel] at hx; linarith only [hx,mass_pos x (y-step i)]
lemma grow_sqrt (h:4≤ D x y): sqrt (D x y)≤ D x y/2:=by have hz:=Real.sq_sqrt (pay_pos x y|>.le); have he:=Real.sqrt_nonneg (D x y); nlinarith only [h,hz,he]
lemma shrinkF (s:Finset S)(hz:∀ i∈s,D x i ≤ R)(h:R≤ D x y / 2) (he:R≥0): ∑ i∈s,balance x y i≤ 12000 * R * p 3 x y:= by
    let b:=8*p 3 x y; rw [show 12000*R*p 3 x y=1500*R*b from (by unfold b;ring)]; apply le_trans _ (mul_le_mul_of_nonneg_right (head_pay x s hz he) (by have ht:=live (k:=3) x y; unfold b; positivity)); rw [sum_mul]; exact sum_le_sum fun i hi=>mul_le_mul_of_nonneg_left (bind₃ x y i (hz i hi) h) (live _ _|>.le)
lemma friction (fx fy:S→ℝ)(A:Paying x 4 a fx)(B:Paying y 3 b fy) (h:a≥0)(ht:b≥0) (hR:4≤ D x y) (s:Finset S):
   ∑ i ∈ s, ‖fx i*fy i‖ ≤ (a*b) * (152000*p 2 x y/ sqrt (D x y)):= by
    have hk :=pay_pos x y; let R:= sqrt (D x y); have hr: R>0:=Real.sqrt_pos.mpr hk
    have hR1:R≤ D x y/2:= grow_sqrt _ _ hR
    have he(i:S) : ‖fx i*fy i‖ ≤ (a*b)*(p 4 x i * p 3 y i):= by rw [mul_mul_mul_comm,norm_mul]; exact mul_le_mul (A i) (B i) (by positivity) (mul_nonneg h (live _ _|>.le))
    let f(i:S):= p 4 x i*p 3 y i; have hx : ∑ i∈s, f i≤ 152000*p 2 x y/R:= by
       let A:=p 3 x y; let B:=p 2 x y; apply le_trans (binaryF s (fun i=> D x i ≤ R) _ (a:=12000*R * p 3 x y) (b:= R⁻¹*(140000*B)) ?_ ?_); rotate_left
       · refine le_trans (Finset.sum_le_sum (g:=balance x y) fun i hi=> ?_) (shrinkF x y _ (fun i hi=>(mem_filter.mp hi).2) hR1 hr.le); apply mul_le_mul_of_nonneg_right _ (live _ _|>.le); simpa using pureM (k:=3) x i (mass_pos ..) (by norm_num)
       · refine le_trans ?_ (mul_le_mul_of_nonneg_left (bal₀ x y (s.filter (fun i=>¬D x i≤R))) (by positivity : 0 ≤ R⁻¹)); rw [Finset.mul_sum]; apply sum_le_sum; intro i hi; unfold f balance; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (pureM x i (le_of_lt (lt_of_not_ge (mem_filter.mp hi).2)) hr) (live _ _|>.le)
       apply le_of_eq; have hp:R^2=D x y:=Real.sq_sqrt hk.le; unfold B fund; field_simp; rw [←hp]; ring
    exact le_trans (Finset.sum_le_sum fun i _=> he i) ((by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hx (mul_nonneg h ht))) -- parentheses
local notation "o"=> side q k
variable {x' y':Fielding.Walk}(f g: Scaff)(h:Geom q R x' y' x') -- h unused
local notation "X"=> transit q x'
local notation "Y"=>transit q y'
local notation "F₀" => leg q x' y'
lemma friction_s {F G:Scaff}(hx: Clear q R x' y')(hq:1<q.val)(hr:R≥0)(hc:c≥0)(ha:a≥0)
    (H:∀ᶠ i in atTop,Paying (X i) 4 c (F (side q i) (X i)) ∧ Paying (Y i) 3 a (G (side q i) (Y i))):
    Tendsto (fun k=> (ε k)⁻¹^2* ∑ i:Site (side q k), F (side q k) (X k) i *G (side q k) (Y k) i) L (𝓝 0) := by
    let l(k:ℕ):= sqrt (leg q x' y' k); let c':ℝ:=c*a*152000; let r(k:ℕ):= c'*(l k)⁻¹; have hr' : 0≤ c':=by unfold c'; positivity
    have ht:= Real.tendsto_sqrt_atTop.comp (giants hq hx hr); refine rent_cost (k:=2) hq hx hr _ r (by simpa [mul_zero] using! (tendsto_inv_atTop_zero.comp ht).const_mul c') ?_;
    filter_upwards [H,(giants hq hx hr).eventually (eventually_ge_atTop 4)] with k hk ht; let X':=X k; let Y':=Y k; have he:=epsilon_pos q k; have hl:0< l k:=Real.sqrt_pos.mpr plus_leg
    have hz:= friction X' Y' (F (side q k) X') (G (side q k) Y') hk.1 hk.2 hc ha ht Finset.univ
    rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ (ε k)⁻¹^2)]; apply le_trans (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans hz) (by positivity)); unfold r segment; rw [abs_of_nonneg (by positivity:0≤c'*(l k)⁻¹)]; apply le_of_eq; unfold c'; simp_rw [fund,div_eq_mul_inv]; rw [mul_inv,mul_pow]; change _ = c*a*152000 * (Real.sqrt (D X' Y'))⁻¹ * ((ε k)⁻¹^2 * (D X' Y')⁻¹^2); ring
end YM.PositionX.Chir.Imprint
