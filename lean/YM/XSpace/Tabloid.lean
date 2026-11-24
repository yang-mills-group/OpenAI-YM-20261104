import YM.XSpace.Musette
/-!
# Extracted limit and all-angle test eligibility
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Angle
open Function Set Filter Relief Season Trace Litter Tide Sail Playpen Lattice Chiral
open scoped Topology BigOperators
variable {ι:Type}{L:Filter ι}{R:ι→ℝ}{v:ι→E4}{b:E4}{G:Gauge} (c:Shade.Cut)(K:c.rOut<1)(M: Motion L R v b)
local notation "P₀" => spoken
local notation "ℓ" => Season.line false
local notation "A" => P₀ b
local notation "B" => atria c
local notation "ε" => liftedSign
local notation "X" => height R v
local notation "Z" => root v
variable (i j k:P)
private abbrev expected:= -(∑ t:P,A i t*(ε j t k*tip))
def limit (b:E4)(i j k:P):=∑ m:P,∑ n:P,P₀ b j m*P₀ b k n*expected (b:=b) i m n
include K M in
lemma beating : Tendsto (fun w=> R w^4 * B i j k (X w) 0 (Z w)) L (𝓝 (expected (b:=b) i j k)) :=by
  have he:= (direct_quiet M i j k).sub (tendsto_finsetSum _ (fun t (_: t∈Finset.univ)=> skylight c M K i j k t)); rw [zero_sub] at he; apply he.congr; intro w; unfold atria; simp_rw [mul_sub, Finset.mul_sum]
include K M in
lemma triplet : Tendsto (fun w=> R w^12* op c i j k (X w) 0 (Z w)) L (𝓝 (limit b i j k)):=by
  unfold op limit; simp_rw [Finset.mul_sum]; refine tendsto_finsetSum _ (fun m hm=> tendsto_finsetSum _ (fun n hn=> ?_)); refine (((costs_shift M (charted true false j m)).mul (from_lip M (charted true false k n))).mul (beating c K M i m n)).congr fun w=> ?_; unfold spoken; ring
lemma onto (h:‖b‖=1): ∑ i:P,∑ j:P,∑ k:P,liftedSign i j k* limit b i j k = tip*6*magnitude:=by
  calc
   _ = (-tip)* cubic (P₀ b):= ?_
   _ = _:=by rw [cadence,decided h]; ring
  unfold cubic; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=>?_ ; unfold limit expected spoken; simp only [mul_neg, neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _=>?_ ; conv_rhs=> rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=>?_ ; ring
include K M in
lemma to_be (G:Gauge): Tendsto (fun w=> R w^12* answer c G (X w) 0 (Z w)) L (𝓝 (6*S_color G*(tip*6*magnitude))) := by
  have ht: Tendsto (fun w=> R w^12 * tens c (X w) 0 (Z w)) L (𝓝 (tip*6*magnitude)):=by
    unfold tens; simp_rw [Finset.mul_sum]; rw [← onto (b:=b) M.unit]; exact tendsto_finsetSum _ (fun i _=> tendsto_finsetSum _ (fun j _=>tendsto_finsetSum _ (fun k _=>((triplet c K M i j k).const_mul _).congr fun a=>mul_left_comm .. )))
  exact (ht.const_mul _).congr fun i=>mul_left_comm ..
include c K in
lemma testable (g:G.Simple): ∀ᶠ P:ℝ in atTop,∀ b:E4, ‖b‖=1 → answer c G (P • b) 0 (θs • b)<0:=by
  by_contra he
  rw [eventually_atTop] at he; push_neg at he; choose T hT v hv H using fun n:ℕ=> he (n:ℝ); have ht:Tendsto T atTop atTop:= tendsto_atTop_mono hT tendsto_natCast_atTop_atTop; obtain ⟨b,hb,q,hq,Q⟩:= (isCompact_sphere (0:E4) 1).tendsto_subseq (fun n=> (Metric.mem_sphere.mpr (by rw [dist_zero_right]; exact hv n) : v n∈Metric.sphere 0 1)); have hh: Motion atTop (T ∘ q) (v ∘ q) b:=⟨ht.comp hq.tendsto_atTop,Q,(fun i=>hv (q i)),by simpa using hb⟩; obtain ⟨n,hn⟩:= ((to_be c K hh G).eventually (gt_mem_nhds (show 6*S_color G* (tip*6*magnitude)<0 from mul_neg_of_pos_of_neg (mul_pos (by norm_num) (color_positive g)) (mul_neg_of_pos_of_neg (mul_pos tip_ok (by norm_num)) negative)))).exists; apply not_le.mpr hn; change 0≤ T (q n)^12 * answer c G _ _ _; exact mul_nonneg (by positivity) (H (q n))
end YM.XSpace.Angle
