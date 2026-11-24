import YM.OPE.Compatible.Maestro.Temper
import YM.OPE.Compatible.Month.Goblin
/-! # Double budget: choose a fixed tuning stage challenge. All statements
can meet purchases by contradiction within THAT single stage. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Pill
open Function Filter Set Lattice RG Wilson
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {M J V W:Type*}{l:Filter M}
section
variable {β β' f:M→ℝ}
abbrev Counters (β:M→ℝ):M→ℝ := Real.log ∘ β
abbrev Receipt (β:M→ℝ)(l:Filter M)[Norm V](g:M→V):= Score l (Counters β) g
abbrev Wax (β:M→ℝ)(l:Filter M)[Norm V](g:M→V)(a:ℝ):= RateLE l (Counters β) g a
abbrev Wick (β:M→ℝ)(l:Filter M)[Norm V](g:M→V):=∀ a:ℝ,Wax β l g a
lemma carth (h:Tendsto β l atTop):Tendsto (Counters β) l atTop:= Real.tendsto_log_atTop.comp h
lemma canq (h:Tendsto β l atTop):RateIs l (Counters β) β 1:=by
    refine ⟨h.eventually_gt_atTop 0,tendsto_const_nhds.congr' ?_⟩; filter_upwards [(carth h).eventually_gt_atTop 0] with i hi; change 1=Counters β i/_; rw [div_self hi.ne']
lemma sans (h:Tendsto β l atTop):Receipt β l (Counters β):= Score.time (carth h)
lemma turns (h:Tendsto β l atTop):Wax β l (Counters β) 0:= RateIs.pays ⟨(carth h).eventually_gt_atTop 0,Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (carth h)⟩ (carth h)
lemma waitG [Norm V] {v:M→V}(h:Tendsto β l atTop)(hp:Receipt β l v):Wax β l v 0:=by
    obtain ⟨k,hk⟩:= Score.fitsQ hp (carth h); apply RateLE.of_norm_le ?_ hk; simpa only [mul_zero] using RateLE.pow k (turns h) (carth h)
abbrev Shell (β β':M→ℝ)(l:Filter M):Prop:= ∃ c C:ℝ,0<c ∧ 0<C∧∀ᶠ i in l,c*β i ≤β' i ∧ β' i ≤ C*β i
lemma Shell.track (p: Shell β β' l)(h:Tendsto β l atTop): Tendsto β' l atTop:=by obtain ⟨c,C,hc,hC,H⟩:=p; exact tendsto_atTop_mono' l (H.mono (fun _ hi=>hi.1)) (h.const_mul_atTop hc)
lemma Shell.Ray (p: Shell β β' l)(h:Tendsto β l atTop):RateIs l (Counters β) β' 1:=by
    obtain ⟨c,C,hc,hC,H⟩:=p
    refine RateIs.of_sandwich ?_ (f:=fun i=> c * β i) (f':=fun i=>C * β i) ?_ (H.mono fun i hi=>hi.1) (H.mono fun i hi=>hi.2) (carth h)
    · simpa only [zero_add] using (RateIs.const (carth h) hc).mul (canq h)
    exact (show RateIs l (Counters β) (fun i=>C*β i) 1 by simpa only [zero_add] using (RateIs.const (carth h) hC).mul (canq h)).pays (carth h)
abbrev Sparks (β:M→ℝ)(i:M):=((β i)^((-1:ℝ)/2))
lemma surely (h:Tendsto β l atTop)(hp:Shell β β' l): RateIs l (Counters β) (Sparks β') (-1/2):=by simpa only [mul_one] using (hp.Ray h).rpow ((-1:ℝ)/2)
-- polynomial in B tiers. Large attenuation of radii
noncomputable abbrev Burl (δ:ℝ)(s:M→ℝ)(i:M):=Real.exp (-δ * s i ^2)
lemma Wick_bill (h:Tendsto β l atTop){δ :ℝ}(hp:0<δ):Wick β l (Burl δ (Counters β)):=by
    intro a t _; filter_upwards [(carth h).eventually_gt_atTop 0, ((carth h).const_mul_atTop hp).eventually_ge_atTop (-t)] with i hi hg; unfold Burl; rw [Real.norm_of_nonneg (Real.exp_nonneg _)]; change -t ≤ δ * Counters β i at hg; exact Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_right hg hi.le])
end
end YM.OPE.Pill
