import YM.X.Reed.Oka
import YM.X.Clear.Dona
import YM.Next.RANK.Walling
/-!
# Fixed physical coordinate frame at arbitrary Cover origin
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Fielding
open Lattice Wilson Next.Rank CellsInt Beamer Interval PertExtension LatticePT Filter Set Function Metric
open scoped Topology BigOperators Classical
variable {q : ℕ+} (hq:1<q.val) (T R:ℝ) {n:Side} {k:ℕ}
local notation "Fℕ"=>(atTop:Filter ℕ)
def spot (r:ℝ): Cover →+ E4 where
   toFun x:= r • mapZ x; map_zero':= by rw [show mapZ 0=0 from PiLp.ext fun _=>Int.cast_zero, smul_zero]
   map_add' x y:= by rw [Wall.sends_map,smul_add]
@[simp] lemma spots (r:ℝ)(x:Cover): spot r x=r • mapZ x:= rfl
lemma fullInc (r:ℝ)(x:Cover): spot r x=Pert.Full.incVec r x:= rfl
abbrev Walk:=ℕ→ Cover
abbrev plot (q:ℕ+)(f:Walk)(x:E4):Prop:= Tendsto (fun k=> spot (epsilon q k) (f k)) atTop (𝓝 x)
-- rooted at fixed height. No clearance implicit.
namespace plot
variable {x y:E4} {f g:Walk}
include hq in
lemma constant (x:Cover): plot q (fun _=>x) 0:= Pert.Align.inc_const (paths hq) x
lemma add (h:plot q f x)(p:plot q g y): plot q (f+g) (x+y):= (Tendsto.add h p).congr (fun k=>(map_add (spot _) ..).symm)
lemma sub (h:plot q f x)(p:plot q g y): plot q (f-g) (x-y):= (Tendsto.sub h p).congr (fun k=>(map_sub (spot _) ..).symm)
lemma released (h:plot q f x): Reed.Released (fun k=> spot (epsilon q k) (f k)):=⟨x,h⟩
end plot
lemma street_height (z:Cover): (street z:ℝ) ≤ 4* ‖mapZ z‖ := by
   unfold street; rw [Nat.cast_sum]; apply le_trans (b:=∑ i:Axis,‖mapZ z‖) ?_ (by simp [Axis]); apply Finset.sum_le_sum; intro i _; have hx:= PiLp.norm_apply_le (mapZ z) i; rw [Real.norm_eq_abs] at hx; change |_root_.Int.cast (R:=ℝ) (z i)| ≤ _ at hx; simpa only [← Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast] using hx
lemma round_lift (z:Site n):(street (lift z))≤ 4*pdist z:= by
   unfold street; apply le_trans (b:=∑ i:Axis,pdist z) (Finset.sum_le_sum fun i _=> component_le ..) (by simp [Axis])
lemma wrap_rotate (z:Cover): pdist (wrap n z) ≤ street z:= by
   refine (Size.round_fee z).trans (Finset.sup_le (fun i _=>?_)); unfold street; exact Finset.single_le_sum (f:=fun i:Axis=>(z i).natAbs) (fun i _=>Nat.zero_le _) (Finset.mem_univ i)
lemma street_triangle(x y:Cover):street (x+y)≤street x+street y:=by unfold street; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _=> Int.natAbs_add_le ..
def gate (q:ℕ+)(R:ℝ)(i:ℕ):ℕ:= ⌊(magnify q i * R)⌋₊
lemma gate_mem (hr:R≥0)(z:Cover): street z≤gate q R k ↔ epsilon q k*(street z:ℝ) ≤ R:= by
    rw [gate,Nat.le_floor_iff (mul_nonneg (amp_pos q k|>.le) hr), eps_eq, inv_mul_eq_div,div_le_iff₀ (amp_pos q k),mul_comm _ R]
lemma spot_cost (z:Cover): ‖spot (epsilon q k) z‖ ≤ epsilon q k*street z:= by rw [spots,norm_smul,Real.norm_of_nonneg (epsilon_pos q k|>.le)]; exact mul_le_mul_of_nonneg_left (Wall.norm_road _) (epsilon_pos q k|>.le)
lemma street_cost (z:Cover): epsilon q k*street z ≤ 4*‖spot (epsilon q k) z‖:= by rw [spots,norm_smul,Real.norm_of_nonneg (epsilon_pos q k|>.le), mul_left_comm]; exact mul_le_mul_of_nonneg_left (street_height z) (epsilon_pos q k|>.le)
lemma gate_range (hr:R≥0)(z:Cover)(hz:street z≤gate q R k): ‖spot (epsilon q k) z‖ ≤ R:= (spot_cost z).trans ((gate_mem _ hr _).mp hz)
include hq
lemma gate_asc (hr:R>0): Tendsto (gate q R) atTop atTop := tendsto_nat_floor_atTop.comp ((giant hq).atTop_mul_const hr)
lemma gate_shift (hr:R>T)(ht:T≥0)(v:Cover): ∀ᶠ i in Fℕ,∀ z:Cover,street z≤gate q T i→ street (z+v)≤gate q R i:= by
    have hx : Tendsto (fun k=>epsilon q k*(street v:ℝ)) Fℕ (𝓝 0):= by simpa using! (paths hq).cutoff.mul_const (street v:ℝ)
    filter_upwards [hx.eventually (ge_mem_nhds (sub_pos.mpr hr))] with k hk z zh; rw [gate_mem _ (le_trans ht hr.le)]
    apply (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (street_triangle z v)) (epsilon_pos q k|>.le)).trans; push_cast; rw [mul_add]; linarith [(gate_mem _ ht _).mp zh]
lemma spot_lift : ∀ᶠ i:ℕ in Fℕ,∀ z:Cover, ‖spot (epsilon q i) z‖≤R→ lift (wrap (side q i) z)=z:= by
    let h:= Pert.Align.large (paths hq); filter_upwards [h.eventually (eventually_gt_atTop (2*R))] with i hi z hz; apply lift_eq_iff.mpr; refine ⟨rfl,fun j=>?_⟩
    have hx : 2*|z j| < ((side q i).val:ℤ):= by
       have hq':= (PiLp.norm_apply_le (spot (epsilon q i) z) j).trans hz; change ‖epsilon q i * ((z j):ℝ)‖ ≤ R at hq'; rw [Real.norm_eq_abs, abs_mul,abs_of_pos (epsilon_pos q i),← Int.cast_abs] at hq'
       change 2*R < epsilon q i*(side q i).val at hi; exact_mod_cast (show (2:ℝ)*((|z j|:ℤ):ℝ)< ((side q i).val:ℝ) from lt_of_mul_lt_mul_left (a:=epsilon q i) (by linarith only [hq',hi]) (epsilon_pos q i|>.le))
    have ht:= le_abs_self (z j); have he:=neg_le_abs (z j); omega
lemma plot_lift {z:E4}{f:Walk}(h:plot q f z) : ∀ᶠ i:ℕ in Fℕ,lift (wrap (side q i) (f i))=f i:= ((spot_lift hq (‖z‖+1)).and (h.norm.eventually (ge_mem_nhds (lt_add_one ‖z‖)))).mono (fun i ⟨hi,h⟩=> hi _ h)
-- choose R for evaluating local crunch against remote marks. room inside height for arbitrary offsets
lemma gate_far (hr:R≥0){x:E4}(hx:R < ‖x‖){f:Walk}(h:plot q f x): ∃ a:ℝ,a>0∧ ∀ᶠ i:ℕ in Fℕ, ∀ z:Cover,street z≤gate q R i→ a≤epsilon q i* mass (wrap (side q i) z) (wrap _ (f i)):= by
    obtain ⟨r,hr',hrp⟩:= exists_between hx; refine ⟨(r-R)/4,by exact div_pos (sub_pos.mpr hr') (by norm_num),?_⟩
    filter_upwards [spot_lift hq (R+‖x‖+1),h.norm.eventually (le_mem_nhds hrp),h.norm.eventually (ge_mem_nhds (lt_add_one ‖x‖))] with k hK hl hu z hz;
    let e:=epsilon q k; let s:= spot e; let j:= wrap (side q k) z-wrap _ (f k); have hp:=epsilon_pos q k; have hg := gate_range R hr z hz
    have hs : s (lift j)=s z-s (f k):= by unfold j; rw [← map_sub,hK,map_sub]; rw [map_sub]; linarith [norm_sub_le (s z) (s (f k))]
    have he : (r-R)≤ ‖s (lift j)‖:= by rw [hs,norm_sub_rev]; apply le_trans _ (norm_sub_norm_le ..); linarith only [hl,hg]
    rw [mass_eq,div_le_iff₀ (by norm_num)]; change r-R≤ e*(1+pdist j)*4; have hl2 : e*street (lift j) ≤ e*(4*pdist j):= mul_le_mul_of_nonneg_left (by exact_mod_cast round_lift j) hp.le; change 0<e at hp; nlinarith only [he.trans (spot_cost _),hl2,hp]
end YM.PositionX.Fielding
