import YM.X.Scheme.Quest
import YM.X.Journey.Bare
/-!
# Stable recalibration modulo near-Jet precritical real H frame (association joins).
Any-order statement, used in FO with singular shape estimates.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX
open Lattice Function Filter Set Pert Pert.Position Pulse Detector Jet
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G}{d n:ℕ}
local notation "B"=> Bank F d
namespace Ribbon
open Reed
local notation "C'"=> pureBank F d
local notation "Fℕ"=>(atTop:Filter ℕ)
lemma weft {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℝ X][NormedSpace ℝ Y](f:X→Y){A:ℕ→Word X}{p:X}(h:Tendsto (fun i=>A i 0) Fℕ (𝓝 p))(ha:Released (fun i=> A i 1))(hx:ContDiffAt ℝ ω f p): Released (fun i=> run f (A i) 1):= by
    obtain ⟨q,hq⟩:= ha; have hp : ContinuousAt (fderiv ℝ f) p := hx.continuousAt_fderiv (by simp); have hg : ContinuousAt (fun (w:X×X)=> fderiv ℝ f w.1 w.2) (p,q):= (hp.comp continuousAt_fst).clm_apply continuousAt_snd; refine ⟨fderiv ℝ f p q,(hg.tendsto.comp (h.prodMk_nhds hq)).congr' ?_⟩; filter_upwards [h.eventually (hx.eventually (by simp))] with i hi; exact (flow_tip _ _ (hi.differentiableAt (by simp))).symm
variable (D:Detector F d) (Y:ℕ→ Word (Bank F d)) (h:∀s:Pert.Position.Section F d,Tendsto (fun i=> lookie F s (Y i 0)) atTop (𝓝 (lookie F s (pureBank F d)))) (t: Test n)(v:Pert.Position.Section F d)
local notation "ℙ" i=> D.report (Y i)
local notation "Ω" i=> predMarket (D.report (Y i)) (Y i)
local notation "e"=> D.solve0
include h
lemma page_sticks : Tendsto (fun i=> D.report (Y i) 0) Fℕ (𝓝 0):= by simp_rw [Detector.report_zero]; exact D.appears_solve0 (q:=fun i=> Y i 0) h
lemma page_head : Tendsto (fun i=>lookie F v (predMarket (D.report (Y i)) (Y i) 0)) Fℕ (𝓝 (lookie F v C')):= by simp_rw [all_tips (s:=v),Jet.run_zero ]; rw [← market_zero F C', cross_leaves]; apply (cross_smooth F v.p|>.continuous.continuousAt.tendsto).comp ((expose_leg F (w:=fun i=> Y i 0) h v.f).prodMk_nhds (page_sticks D Y h))
lemma page_leaves (hl:Released (fun i:ℕ=> D.read (Y i 1))) : Released (fun i=> D.report (Y i) 1):= by
    let f:=pick D.slips; have ht: ContDiffAt ℝ ω f D.parameter:= D.slip_spec.diff.comp (f:=fun x=>(x,0)) D.parameter (by fun_prop); apply weft f (A:=fun i=> D.read ∘ Y i) (D.rail.common_limit (w:=fun i=>Y i 0) h) hl ht
lemma page_race (hl:Released (fun i:ℕ=> D.read (Y i 1)))(hx:Released (fun i=>expose F v.f (Y i 1))): Released (fun i=> lookie F v (predMarket (D.report (Y i)) (Y i) 1)):= by
    let x(i:ℕ):= expose F v.f (Y i 0); let W:= expose F v.f C'; let y(i:ℕ):=expose F v.f (Y i 1); let A(i k:ℕ):=D.report (Y i) k; simp_rw [all_tips (s:=v)]; apply weft (p:=(W,0)) (cross F v.p); exact (expose_leg F (w:=fun i=> Y i 0) h v.f).prodMk_nhds (page_sticks D Y h)
    · obtain ⟨a,ha⟩:= hx; obtain ⟨b,hb⟩:= page_leaves D Y h hl; exact ⟨(a,b),ha.prodMk_nhds hb⟩
    apply (cross_smooth F v.p).contDiffAt
-- open and finite width criterion. `∃ᶠ radius` all d-cost for sectors. independence derivative t
omit h
section
variable (α:ℕ)
lemma region_time {K: Set (Points n)}(hK:IsCompact K)(h:K⊆ conf n): ∀ᶠ r:ℝ in 𝓝[>] 0,K⊆ Pulse.Region n r := by
   let T:= 𝓝[>] (0:ℝ); rcases eq_empty_or_nonempty K with h'|h'; · simp [h']
   have he(i j:Fin n): ∀ᶠ r:ℝ in T, i≠j→∀x∈K,r < ‖x.ofLp i-x.ofLp j‖:= by
       by_cases ht:i=j; · filter_upwards with s hs;exact False.elim (hs ht)
       let f(x:Points n):= ‖x.ofLp i-x.ofLp j‖; have he : Continuous f:= ((PiLp.continuous_apply 2 (fun _:Fin n=>E4) i).sub (PiLp.continuous_apply 2 _ j)).norm; obtain ⟨x,hx,H⟩:= hK.exists_isMinOn h' he.continuousOn; have hx' : f x>0 := norm_pos_iff.mpr (sub_ne_zero.mpr (fun p=> ht (h hx p)))
       filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hx')] with r hr hp z hz; exact lt_of_lt_of_le hr (H hz)
   filter_upwards [eventually_all.mpr (fun i=> eventually_all.mpr (he i))] with r hh; intro t ht i _ j _ he; exact hh i j he t ht
end
end Ribbon
end YM.PositionX
