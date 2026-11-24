import YangMills.WilsonProof.NativeSupport.Commissioned259.Horizon.Tax
/-! # Log price on moving two-radius layouts for compact fields AND the packet residual

Use order of operations of Flash259HorizonFork G.4, G.5, shift into packet (even working
throughout on fixed physical polynomial-log currents before applying H). Extends to any
vacant arities, every viewer. Next test of the actual H can expand in these queries.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flash259HorizonFork
open Function Filter Set Asymptotics MeasureTheory Table Extraction Spec Arboreal OPE.Orbits
open scoped Topology Classical BigOperators
open Node Log
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    (Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (hG:G.Simple) (Z:PhysMS.tower S)
    {I J V : Type}[Fintype I][Fintype J] {d:I→ℕ}{e:J→ℕ}{M δ:ℝ} (mn:0≤M)(dp:0<δ)
    {l:Filter V}{r s:V→ℝ}{x:V→ I→E4}{y:V→ J→E4}{o:V→E4}
    (H:LogTrace F Q.port) (u:Labels S d) (v:Labels S e)
    (p:V→Viewers F) (hs:Tendsto s l (𝓝[>] 0))
    (hx:∀ᶠ i in l, Ready (r i) (s i) M δ (x i) (y i))
local notation "phase" i:max => spectator F (p i)
local notation "z" i:max => atPosition (o i) (r i) (x i)
local notation "z'" i:max => atPosition (o i) (s i) (y i)
local notation "massR" i:max => r i^(∑ j,d j)*s i^(∑ j,e j)
local notation "wage" h:max i:max => s i+(r i/s i)^(h+1)

include hs hx
lemma smaller_radius : Tendsto r l (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
  ⟨squeeze_zero' (hx.mono fun i hi=>hi.1.le) (hx.mono fun i hi=> hi.adj) (tendsto_nhdsWithin_iff.mp hs).1, hx.mono fun i hi=>hi.length⟩
lemma smaller_badge : ∀ᶠ i in l,badge (s i)≤ badge (r i) := hx.mono fun i hi=>
  add_le_add le_rfl (neg_le_neg (Real.log_le_log hi.length hi.adj))
lemma wound {p u : V→ℝ} (hp : ∀ᶠ i in l,0<p i) (hu : ∀ᶠ i in l,0 ≤ u i) (n : ℕ) (K:ℝ) (hk:0 ≤ K) {E : Type*} [NormedAddCommGroup E] {f:V→E}
    (V : ∀ᶠ i in l,p i*‖f i‖ ≤ K*(badge (s i)*badge (r i))^n*u i) : Allowance l r (fun i=> u i/p i) f := by
  have hs' := smaller_radius hs hx; refine ⟨2*n, IsBigO.of_bound K ?_⟩
  filter_upwards [hp,hu,V,smaller_badge hs hx,log_pays hs,log_pays hs'] with i hp hu V l sa ra
  apply (le_div_iff₀ hp).mpr (show ‖f i‖*p i ≤ K*(badge (s i)*badge (r i))^n*u i from by rw [mul_comm]; exact V) |>.trans
  rw [Real.norm_of_nonneg (by positivity),pow_mul,pow_two]
  refine le_trans (b:=K * (badge (r i)*badge (r i))^n*u i/p i) ?_ (le_of_eq ?_)
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right l (zero_le_one.trans ra)) n) hk) hu) hp.le
  ring
omit hs
include o in
lemma near_scope : ∀ᶠ i in l, WithinRoom (r i) M δ (z i) (o i) := hx.mono fun i h=> only_room (o i) h.length h.close h.separation
include mn dp o in
lemma outer_scope : ∀ᶠ i in l, WithinRoom (s i) M δ (beside (sole (o i)) (z' i)) (o i) := by
  filter_upwards [hx] with i h
  have hz := only_room (o i) (h.length.trans_le h.adj) h.reaches h.separated
  constructor
  · rintro (k|k); exact (by simpa [sole] using mul_nonneg mn (h.length.le.trans h.adj))
    exact hz.1 k
  rintro (a|a) (b|b) e
  · exact (e (congr_arg Sum.inl (Subsingleton.elim ..))).elim
  · exact middle_far _ h dp.le _ (.same ..) b
  · rw [norm_sub_rev]; exact middle_far _ h dp.le _ (.same ..) a
  exact hz.2 a b (fun h=>e (congr_arg Sum.inr h))
include hs
lemma shorten {p : V→ℝ} {E : Type*}[NormedAddCommGroup E] {f : V→E} (h:Allowance l s p f) : Allowance l r p f := by
  obtain ⟨k,v⟩:=h; refine ⟨k,v.trans (IsBigO.of_bound' ?_)⟩; filter_upwards [log_pays hs,log_pays (smaller_radius hs hx),smaller_badge hs hx] with i h h' l; simp only [norm_mul,norm_pow,Real.norm_of_nonneg (zero_le_one.trans h),Real.norm_of_nonneg (zero_le_one.trans h')]; gcongr

include hG Z H mn dp
lemma prime (q:V→Viewers F) : Allowance l r (fun i=>s i/(massR i)) (fun i=> Orbits.whole (phase i) (z i) u (z' i) v - Orbits.whole (spectator F (q i)) (z i) u (z' i) v) := by
  obtain ⟨k,K⟩:= phases F Q.port u v Z hG H mn dp
  refine wound hs hx ?_ ?_ k 2 (by norm_num) ?_
  · exact hx.mono fun i hi=>mul_pos (pow_pos hi.length _) (pow_pos (hi.length.trans_le hi.adj) _)
  · exact hx.mono fun i hi=>hi.length.le.trans hi.adj
  filter_upwards [hx,hs.eventually K] with i h e; exact (e _ _ _ _ h (p i) (q i)).trans_eq (by ring)
lemma powers (h:ℕ) (u:S.Field h) : Allowance l r (fun i=>(s i^(h+∑ j,e j))⁻¹) (fun i=> upon (phase i) h (o i) (z' i) v u) := by
  have e:=compact_pay F Q hG Z mn dp H.toSingleLog (d:= Sum.elim (fun _=>h) e) (o:=o) (stages (fun (_:Unit)=>u) v) hs (outer_scope mn dp hx) p
  apply (shorten hs hx e).extend
  exact Eventually.of_forall fun i=>by change s i^0/s i^(∑ j:Unit⊕J, Sum.elim (fun _=>h) _ j)=_; rw [Fintype.sum_sum_type]; simp

lemma powers' (h:ℕ) (u:V→S.Field h) (w:V→ℝ) (hu:Allowance l r w u) : Allowance l r (fun i=> w i*(s i^(h+∑ j,e j))⁻¹) (fun i=> upon (phase i) h (o i) (z' i) v (u i)) := by
  let b:= Module.finBasis ℂ (S.Field h)
  have e0 (i : V) : upon (phase i) h (o i) (z' i) v (u i) = ∑ j, LinearMap.toContinuousLinearMap (b.coord j) (u i) • upon (phase i) h (o i) (z' i) v (b j) := by
    nth_rw 1 [← b.sum_repr (u i)]; rw [map_sum]; exact Finset.sum_congr rfl (fun j _=> _root_.map_smul ..)
  simp_rw [e0]; refine Allowance.sum (smaller_radius hs hx) _ _ (fun j (_: j∈(Finset.univ:Finset (Fin _)))=> Allowance.smul (Allowance.linear (LinearMap.toContinuousLinearMap (b.coord j)) hu) (powers F Q hG Z mn dp H v p hs hx h (b j)))

lemma currency (h:ℕ) : Allowance l r (fun i=> (wage h i)/(massR i)) (fun i=> discrepancy (phase i) h (z i) (o i) u (Q.packet h (z i) u (o i)) (z' i) v) := by
  have hr:=smaller_radius hs hx; obtain ⟨A,K,hA,L⟩:=billed F Q.port u v Z hG H mn dp h
  let w(i:V):= (wage h i)/(massR i)
  let U i:= shadowOld Q.port h (z i) (o i) u; let V₀ i:= Q.packet h (z i) u (o i); let Y i:= Orbits.whole (phase i) (z i) u (z' i) v; let P i:=upon (phase i) h (o i) (z' i) v
  have hh: Allowance l r w (fun i=> Y i-P i (U i)) := by
    refine wound hs hx ?_ ?_ K A hA (show ∀ᶠ i in l,(massR i)*‖Y i-P i (U i)‖≤A*(badge (s i)*badge (r i))^K*(wage h i) from
      (hx.and (hs.eventually L)).mono fun i h=> h.2 _ _ _ _ h.1 (p i))
    · exact hx.mono fun i hi=>mul_pos (pow_pos hi.length _) (pow_pos (hi.length.trans_le hi.adj) _)
    exact hx.mono fun i h=>by have v:=h.length.trans_le h.adj; have ze:= h.length; positivity
  have V:= horizon_packet F Q mn dp H.toSingleLog u h hr (near_scope (o:=o) hx)
  have hv:= powers' F Q hG Z mn dp H v p (o:=o) hs hx h (fun i=> V₀ i-U i) _ V
  refine (Allowance.add hr hh (hv.neg.transport (IsBigO.of_bound' ?_))).congr ?_
  · have hs₁: ∀ᶠ i in l,s i ≤ 1 := (tendsto_nhdsWithin_iff.mp hs).1.eventually (ge_mem_nhds zero_lt_one)
    filter_upwards [hx,hs₁] with i ⟨v,e,c,d',away,sep,sep',gap⟩ h'; have p:=v.trans_le e
    unfold w; rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    -- `r^{h+1}/s^h ≤ s` by r ≤ s
    rw [le_div_iff₀ (by positivity)]
    -- algebra
    calc _ = s i*(r i/s i)^(h+1) := by rw [div_pow]; field_simp; ring
         _ ≤ _ := by nlinarith only [h',p,show 0 ≤ (r i/s i)^(h+1) by positivity]
  exact Eventually.of_forall fun i=>by dsimp only; change Y i-P i (U i)+ -(P i _) = Y i - _; rw [map_sub]; abel
end YM.OPE.Flash259HorizonFork
