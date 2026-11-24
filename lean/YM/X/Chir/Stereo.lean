import YM.X.Chir.Flowing
/-!
# common posture magnification scales. mass. punctures quantitative crowd. 
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e a c:ℝ}
local notation "D"=> Interval.mass
local notation "p"=> fund
local notation "o"=> side q k
local notation "ε"=>epsilon q
local notation "L"=>(atTop:Filter ℕ)
variable {x y z:Fielding.Walk} {X Y Z:E4}
abbrev transit (q:ℕ+)(x:Fielding.Walk)(k:ℕ): Site (side q k):= wrap _ (x k)
abbrev leg (q:ℕ+)(x y: Fielding.Walk)(k:ℕ):= D (transit q x k) (transit q y k)
abbrev segment (q:ℕ+)(x y: Fielding.Walk)(k:ℕ):= epsilon q k * leg q x y k
lemma plus_leg : 0 < leg q x y k:= pay_pos ..
lemma rather : 0 < segment q x y k:= mul_pos (epsilon_pos ..) plus_leg
variable (hq:1<q.val) (hx:plot q x X)(hy:plot q y Y)
local notation "H"=> plot q
local notation "T₁"=> ‖X-Y‖
local notation "g"=> segment q x y
include hq hx hy
omit hx hy in
lemma hop_st (hz:H z Z): ∀ᶠ i:ℕ in atTop, ‖spot (ε i) (z i)‖≤ 4*(ε i* pdist (wrap (side q i) (z i))) := by
     filter_upwards [plot_lift hq hz] with i hi; have hp:=epsilon_pos q i; let v:= wrap (side q i) (z i); have he:= round_lift v; rw [hi] at he; exact (spot_cost _).trans (by rw [mul_left_comm]; gcongr; exact_mod_cast he)
lemma lower_leg (hc:c<T₁)(hc':0≤c): ∀ᶠ i in L,c/4 ≤ g i:= by
    let f:=x-y; let Tape (i:ℕ):=spot (ε i) (f i)
    have hg : plot q f (X-Y):= plot.sub hx hy
    filter_upwards [Tendsto.eventually hg.norm (le_mem_nhds hc),hop_st hq hg] with i hi hv
    let u:=transit q x i; let v:=transit q y i; unfold segment leg; rw [mass_eq]; change c/4 ≤ ε i*(1+(pdist (u-v):ℝ)); have hx: u-v=wrap _ (f i):= by exact (map_sub (wrap (side q i)) (x i) (y i)).symm -- transit unfolds?
    rw [hx]; linarith [epsilon_pos q i, show c≤ ‖Tape i‖ from hi, show ‖Tape i‖ ≤ _ from hv]
lemma upper_leg (hc:T₁<c): ∀ᶠ i in L,g i ≤ 4*c+1:= by
    let f:=x-y; let Tape (i:ℕ):=spot (ε i) (f i); have h : plot q f (X-Y):= plot.sub hx hy
    filter_upwards [Tendsto.eventually h.norm (ge_mem_nhds hc), (paths hq).cutoff.eventually (ge_mem_nhds (zero_lt_one (α:=ℝ)))] with i hi he; let u:=transit q x i; let v:=transit q y i; unfold segment leg; rw [mass_eq]; change ε i*(1+(pdist (u-v):ℝ))≤ _;
    let y':= f i; have hh : (u-v)=wrap _ y':= by exact (map_sub (wrap (side q i)) (x i) (y i)).symm
    rw [hh, mul_add, mul_one]; have hx:= (show ε i*(pdist (wrap (side q i) y'):ℝ) ≤ ε i* Next.Rank.Beamer.street y' from mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (wrap_rotate _)) (epsilon_pos q i |>.le)).trans (street_cost y'); linarith only [show ‖spot (ε i) y'‖ ≤ c from hi,show ε i ≤ 1 from he,hx]
lemma giant_leg (h:X ≠ Y): Tendsto (leg q x y) atTop atTop:= by
   let f:= leg q x y; let c:=‖X-Y‖; have hc:0 < c := norm_pos_iff.mpr (sub_ne_zero.mpr h); have hx:=lower_leg hq hx hy (show c/2 < c from by linarith only [hc]) (show 0 ≤ c/2 by positivity)
   apply tendsto_atTop.mpr; intro a; have ha : Tendsto (fun i:ℕ=>ε i*a) atTop (𝓝 0):= by simpa using! (paths hq).cutoff.mul_const a
   filter_upwards [hx, ha.eventually (ge_mem_nhds (show 0 < c/2/4 by positivity))] with i hi he; exact le_of_mul_le_mul_left (a:=ε i) (he.trans hi) (epsilon_pos q i)
omit hx hy in
lemma reserves (h:Clear q R x y)(hr:0≤R): ∃ a:ℝ, a>0 ∧ ∀ᶠ i in L,a ≤ segment q x y i:= by
    obtain ⟨p',b,h,h',hy⟩:=h; let r:= ‖p'-b‖; have hv:0<r:= lt_of_le_of_lt hr hy; refine ⟨r/2/4,by positivity,lower_leg hq h h' ?_ ?_ ⟩; linarith only [hv,show r=‖p'-b‖ from rfl]; positivity
omit hx hy in
lemma giants (h: Clear q R x y)(hr:0≤R): Tendsto (leg q x y) L atTop:= by obtain ⟨p',b,h1,h2,h⟩:=h; exact giant_leg hq h1 h2 (sub_ne_zero.mp (norm_pos_iff.mp (lt_of_le_of_lt hr h)))
-- generic bouy and tends
omit hx hy in
lemma rent_cost (h:Clear q R x y)(hr:0 ≤ R)(f:ℕ→V)[NormedAddCommGroup V](g':ℕ→ℝ)(hg: Tendsto g' L (𝓝 0))(hp:∀ᶠ i in L,‖f i‖ ≤ |g' i| * (segment q x y i)⁻¹ ^ k): Tendsto f L (𝓝 0) := by
    obtain ⟨a,ha,he⟩:= reserves hq h hr; refine squeeze_zero_norm' (a:=fun i=> |g' i| * a⁻¹^k) ?_ (by simpa using hg.abs.mul_const (a⁻¹^k)); filter_upwards [hp,he] with i hi h; refine hi.trans ?_; have ht : 0< segment q x y i:= rather; gcongr
end YM.PositionX.Chir.Imprint
