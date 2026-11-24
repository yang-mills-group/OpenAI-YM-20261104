import YM.LocalLTE.Crafts.Sand
import YM.LocalLTE.Crafts.Skiff
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
open RG.Shoot Averaging
variable (K: Set ℝ) (g:ℝ→ℕ→Pot G n) {x₀:ℝ}(hK:x₀∈K) (hq: ∀ x∈K, (Portrays X d κ j (g x) V ∧ ∃ v, Meadow.Budget p X.reg (g x) v))
local notation "𝒪" => 𝓝[K] x₀
variable (hr : ∀ (e : ℝ), 0 < e → ∀ᶠ y in 𝓝[K] x₀, Meadow.Budget p X.reg (g x₀ - g y) e)
set_option quotPrecheck false
local notation "P" x=> Magnet.seed (g x)
local notation "s'" x => delta (X.read (P x))
include hr hq hK hG
lemma presa : Tendsto (fun x=> (s' x₀)-(s' x)) 𝒪 (𝓝 0):=by
    obtain ⟨hf,v,hv⟩:= hq x₀ hK; apply Metric.tendsto_nhds.mpr; intro z hz
    let i:=p.threshold^2*(z/2)
    filter_upwards [hr i (mul_pos (sq_pos_of_pos p.threshold_pos) (half_pos hz))] with y hy
    rw [Real.dist_eq,sub_zero]; exact (le_of_mul_le_mul_left (Price.levy (g0:=P y) hG X (P x₀) hv hy).1 (sq_pos_of_pos p.threshold_pos)).trans_lt (half_lt_self hz)
omit hG hr in
lemma poring_sub (y:ℝ)(hy:y∈K) : Portrays X d κ j (g x₀-g y) V:= ⟨fun i h=>by rw [Pi.sub_apply,(hq x₀ hK).1.stays i h,(hq y hy).1.stays i h,sub_zero],fun i t h=>rp_sub _ ((hq x₀ hK).1.frame _ _ h) ((hq y hy).1.frame _ _ h)⟩ -- omit
include hR hd hG hn hx ht hC he hb hv hg hk
variable (hp: Merchant G L κ p.order p.power j d t)(hV:Found G L κ p.order p.power j t)(hs:32*d<n.val)
include hp hV hs
set_option maxHeartbeats 500000 in
lemma cred (v : ℝ)(hv':0<v) (α:ℝ): ∀ᶠ y in 𝒪, Stocked p (Price.tubeX R p X) (vane R c p X d V κ α (s' x₀) j (g x₀)-vane R c p X d V κ α (s' y) j (g y)) v:=by
    let s y:= (s' x₀)-(s' y)
    let E:=(betaF G t L)^Urns.dust j; let U:ℝ →ℝ→ℝ:= fun u x=> tH p*regularNeed G p c σ C' 0 x + vest p u 0 E x c G σ C'
    have ht' : Continuous fun x=> U 0 x:= by unfold U vest regularNeed; fun_prop
    have hz : U 0 0<v:= by unfold U vest regularNeed; simpa only [abs_zero,zero_mul,mul_zero,add_zero] using hv' -- edit
    obtain ⟨x, hx',hQ⟩ : ∃ x:ℝ,0<x∧ U 0 x<v := by obtain ⟨r,hR,hx⟩:= Metric.mem_nhds_iff.mp (ht'.continuousAt.eventually (gt_mem_nhds hz)); exact ⟨r/2,half_pos hR,hx (by simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hR)]; exact half_lt_self hR)⟩
    have hP : Continuous fun e => U e x := by unfold U vest regularNeed; fun_prop
    have ht₀ : Tendsto s 𝒪 (𝓝 (0:ℝ)):= Price.presa hG X V K g hK (j:=j) hq hr -- order
    filter_upwards [(hP.continuousAt.tendsto.comp ht₀).eventually (gt_mem_nhds hQ), self_mem_nhdsWithin, hr x hx'] with y hy hY hZ
    have hu:=hq x₀ hK; have hz:=hq y hY; obtain ⟨t₁,h₁⟩:= hu.2; obtain ⟨t₂,h₂⟩:= hz.2
    let g':= (P x₀); let f:= P y; let Q:= Magnet.seed (g x₀-g y)
    have h:vane R c p X d V κ α (s' x₀) j (g x₀)-vane R c p X d V κ α (s' y) j (g y)= Price.vane R c p X d V κ 0 (s y) j Q.logRead:= Price.vane_bill hd X V (Magnet.promoted (X:=X) h₁).regular (Magnet.promoted (X:=X) h₂).regular α _ _ -- edit
    let F:= Price.vane R c p X d V κ 0 (s y) j Q.logRead; let Y:=archive X R c Q 0 (s y)
    have hh : Meadow.Budget p X.reg Q.logRead x:= hZ
    have hc : Portrays X d κ j (g x₀-g y) V:= Price.poring_sub X V K g hK hq _ hY -- order
    have he₁ := Price.dock hR hv hG hn hd X Q 0 (s y) hh (Price.levy (g0:=f) hG X g' h₁ hZ).1
    have he₂:= Price.crown hR hv hG hn hg ht hC he hx hb hk hd X Q V j hp hV hh hc hs 0 (s y)
    rw [h]; change Stocked p _ F v; rw [show F=Y-(Y-F) by abel]; exact (he₁.minus he₂).cheaper (show U (s y) x < v from hy).le
end YM.AnalyticBridge.VerifiedReset.Collection.Price
