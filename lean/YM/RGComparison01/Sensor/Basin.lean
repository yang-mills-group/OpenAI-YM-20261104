import YM.RGComparison01.AuxPackage
import YM.RGComparison01.Marks.Staircase
/-!
# Collect analytic mark cards in a common grade.
 q denominator per insertion, common Q=w*q (or more);
 turn drafts may deliberately forbid some products. Give tests on complete
 Part with simultaneous rank (not separately counting derivatives). -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Deck
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Gauge
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Push.Uniform Fare Sienna Lapis Lotus Pledge Baked Merge Palette Team Pulse
 open AuxFabric AuxPackage AuxConstant Metric WilsonStartup
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- rank-zeros
section general
variable {ι E : Type}[Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {A B C d β:ℝ} {k j q r w:ℕ} {U : Poll.Body ι →ℝ × E →ℝ}
local notation "P"=>ℝ × E
omit [DecidableEq ι]
abbrev spur (E:Type) := fun (_:Poll.Body ι) (x:ℝ×E)=> x.1
lemma perch (h:d≤1): Purchase (ι:=ι) (spur E) k d B 1 1:= by
   refine ⟨zero_le_one, fun x hx=>?_⟩ -- refine
   have ht : ‖x‖≤1:= (mem_ball_zero_iff.mp hx).le.trans h
   refine ⟨Measurable.indicator measurable_const measurableSet_closedBall,fun z=>?_⟩
   by_cases he:z∈ closedBall (0:Poll.Body ι) B
   · have hp:Brush k 1 1 Prod.fst x:= Brush.linearB (ContinuousLinearMap.fst ℝ ℝ E) ((norm_fst_le x).trans ht) (by rw [one_mul]; exact ContinuousLinearMap.norm_fst_le ..) zero_le_one
     exact hp.shimmy (Eventually.of_forall fun i=> Set.indicator_of_mem he _)
   exact Brush.zi (Eventually.of_forall fun y=> Set.indicator_of_notMem he _) zero_le_one zero_le_one
lemma district (h:d≤1): Probe (spur («ι»:=ι) E) k 0 1 d B 1 1:= by
    refine ⟨⟨fun v hv=> ⟨1,Eventually.mono (ball_mem_nhds 0 zero_lt_one) (fun i hi=> (perch le_rfl).toll i hi)⟩⟩, perch h,fun z=>?_,fun z i hi=>?_⟩
    · rw [pow_zero,mul_one]; exact Brush.linearB (ContinuousLinearMap.fst ℝ ℝ E) (by rw [map_zero,norm_zero]; norm_num) (by rw [one_mul]; exact ContinuousLinearMap.norm_fst_le ..) zero_le_one
    apply norm_eq_zero.mp; rw [show i=0 by omega,norm_iteratedFDeriv_zero,show spur E z 0=0 from rfl,norm_zero]
lemma boosts (hQ:q ≤ k+1) (h:Probe U k j q d B A C)(a:ℝ): Probe (a • U) k j q d B (‖a‖*A) (‖a‖*C):=by
    refine ⟨?_,h.stencil.scalar_mul a,fun z=> ?_,fun z i hi=>?_⟩
    · constructor; intro v hv; obtain ⟨C',hc⟩:= h.outer v hv
      have ht y : truncate (a • U) v y= a • truncate U v y:= by ext z; by_cases h:z∈closedBall 0 v <;> simp [truncate,h]
      refine ⟨‖a‖*C',hc.mono fun i hi=>?_⟩; rw [ht]; exact ⟨measurable_const.smul hi.1,fun z=> ((hi.2 z).smul a).shimmy (Eventually.of_forall fun i=> congr_fun (ht i) z)⟩
    · rw [mul_assoc]; exact (h.origin z).smul a
    have hz := h.null z i hi
    -- hi may > k+1; h unknown. scales by nonzero then transport junk.Standard theorem iteratedFDeriv generalized?
    rw [Pi.smul_apply, iteratedFDeriv_const_smul_apply] -- needs smooth; request hi≤ k
    · rw [hz, smul_zero]
    apply (h.origin z|>.smaller ?_).smooth; omega -- extend with new h
variable {p:Type} (X:p→ Poll.Body ι→ℝ×E→ℝ) (s:Finset p) {T U' : ℝ}
lemma family (h:s.card*q≤ k+1)(hp:∀ i∈ s, Probe (X i) k j q d B T U') : Probe (∏ i∈s,X i) k (s.card*j) (s.card*q) d B (T^s.card*(2^k)^s.card) (U'^s.card*(2^k)^s.card):=by
    induction s using Finset.induction with
    | empty => simpa only [card_empty,prod_empty,zero_mul,pow_zero,mul_one] using! (Probe.unit (ι:=ι) (E:=ℝ×E) («k»:=k) («d»:=d) («D»:=B))
    | insert i s hi ih=>
      rw [card_insert_of_notMem hi,Nat.add_mul,one_mul] at h; have he := ih (by omega) fun j hj=> hp j (mem_insert_of_mem hj)
      rw [prod_insert hi, mul_comm, card_insert_of_notMem hi]; have hx := he.productP (hp i (mem_insert_self ..)) h
      rw [Nat.add_mul,Nat.add_mul,one_mul,one_mul]; refine hx.raise (le_of_eq ?_) (le_of_eq ?_) le_rfl le_rfl <;> simp only [pow_succ] <;> ring
-- grow.TINY normalized vertex, to fit any aperture
abbrev chip (k Q:ℕ):= ((2:ℝ)^k)^Q
abbrev wage (k Q:ℕ):= chip k Q*2^k*2^k
lemma seasonal (Q:ℕ) (hZ:s.Nonempty) (h:s.card*q ≤ Q)(he:Q ≤ k+1)(hV: d≤1)(hp:∀ i∈s, Probe (X i) k j q d B (wage k Q)⁻¹ (wage k Q)⁻¹):
    Probe (((∏ i∈s,X i))*(spur E)^(Q-s.card*q)) k (s.card*j) Q d B 1 1 := by
   let f : ℝ:= 2^k; let g:=chip k Q; have hf:1 ≤ f:= one_le_pow₀ one_le_two; have hg: 1≤g:= one_le_pow₀ hf
   have hx:= family X s (h.trans he) hp; let u:= wage k Q; let v:=Q-s.card*q; have he' : 1*v ≤ k+1:= by omega
   have hv:= hx.productP ((district (ι:=ι) (E:=E) hV).powP (k:=k) (D:=B) he') (show _ + 1*v ≤ _ from by omega)
   rw [one_mul v,zero_mul v,show s.card*q+v=Q by omega, Nat.add_zero,one_mul (2^k:ℝ)] at hv -- check powP implicit n. change
   refine hv.raise ?_ ?_ le_rfl le_rfl; all_goals
    change u⁻¹^s.card * f^s.card * (f^v)*f≤ 1
    rw [←mul_pow]
    have hu : 0 < u:=by unfold u wage chip; positivity
    have hz : u⁻¹*f ≤ 1:= by rw [inv_mul_le_iff₀ hu, mul_one]; change f ≤ g*f*f; exact le_mul_of_one_le_left (zero_le_one.trans hf) (one_le_mul_of_one_le_of_one_le hg hf)
    have hl : (u⁻¹*f)^s.card ≤ u⁻¹*f:= (pow_le_pow_of_le_one (mul_nonneg (inv_pos.mpr hu).le (zero_le_one.trans hf)) hz (Finset.card_pos.mpr hZ)).trans_eq (pow_one _)
    calc
       _ ≤ (u⁻¹*f) *g*f:= mul_le_mul_of_nonneg_right (mul_le_mul hl (pow_le_pow_right₀ hf (by omega : v ≤ Q)) (pow_nonneg (zero_le_one.trans hf) _) (mul_nonneg (inv_pos.mpr hu).le (zero_le_one.trans hf))) (zero_le_one.trans hf)
       _ = 1:=by field_simp; unfold u wage f g chip; ring
end general
end YM.RGComparison01.Sensor
