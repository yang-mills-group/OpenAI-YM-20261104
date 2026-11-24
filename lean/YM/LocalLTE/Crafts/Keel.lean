import YM.LocalLTE.Pond.Iris
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
-- Variance at PRE for all.Cut.
open RG.Shoot Averaging
variable (K: Set ℝ) (g:ℝ→Source G n) {x₀:ℝ}(hK:x₀∈K){f w:ℝ→ℝ} (hq: ∀ x∈K, Local X p (g x) (f x) (w x)) (hh:Compared X p g K)
local notation "𝒪" => 𝓝[K] x₀
include hq hh hK
lemma viewD (v:ℝ)(he:0<v) : ∀ᶠ y in 𝒪, Meadow.Budget p X.reg ((g x₀).logRead - (g y).logRead) v:=by
    let s (X:Support n):= Real.exp (preExponent p * ↑ (coverNumber p.B X)); let u:= ∑i: Support n,s i; have hw i: 0<s i:= Real.exp_pos _; have ht:0 < u:= Finset.sum_pos (fun i _=>hw _) Finset.univ_nonempty
    let ε:=v/u; have hε:0<ε:= div_pos he ht; filter_upwards [hh.deviation_at hK hε,self_mem_nhdsWithin] with y hy hY
    obtain ⟨a,b,h,hB,hx,hV⟩:=hy; have hz i:= (hq _ hK).smooth i; have hh' i:= (hq _ hY).smooth i
    refine ⟨a,fun i=>budget_loosen (budget_mono (budget_scale ht.le hx) (fun j=>?_) (fun j=>?_)) (?_),fun i=>⟨reg_sub (hz i) (hh' i), (sup_varies (hz i) (hh' i)).1 (h i)⟩⟩ -- order
    · split
      next=>exact mul_nonneg (h _).1 (Real.exp_nonneg _)
      exact le_rfl
    · let z:= (X.reg j).support; split
      next hk=>
         calc
         _≤ u*a j := mul_comm (a j) (s z) |>.trans_le (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i' (_:i'∈univ)=> (hw i').le) (Finset.mem_univ z)) (h j).1)
         _≤ _:=mul_le_mul_of_nonneg_left (p.loMass z _ (h j).1) ht.le
      exact mul_nonneg ht.le (hx.1 _)
    unfold ε; rw [mul_comm u,div_mul_cancel₀ _ ht.ne']

local notation "A"=> tubeX R p X
include hG hR hv hn hd
lemma viewU (v:ℝ)(he:0<v)(α:ℝ) : ∀ᶠ y in 𝒪, Stocked p (tubeX R p X) (archive X R c (g x₀) α (delta (X.read (g x₀))) - archive X R c (g y) α (delta (X.read (g y)))) v:=by
    let a:=(g x₀); let t x:= tH p * regularNeed G p c σ C' 0 x; let u:=1+|t 1|
    let ε:= v/u; have hu:0<u:= by unfold u; positivity
    have ht:=div_pos he hu
    filter_upwards [Price.viewD X K g hK hq hh ε ht,self_mem_nhdsWithin] with y hy hY
    let b:=g y; let Δ:= delta (X.read a); let z:= delta (X.read b); have easy (x:ℝ)(h:x∈K):Meadow.Budget p X.reg ((g x).logRead) (f x):=by obtain ⟨w,h',hv⟩:=(hq x h).cheap; exact ⟨w,hv,fun i=>⟨(hq x h).smooth i,h' i⟩⟩
    let D:=Δ-z; have hd': p.threshold^2*|D| ≤ ε:= (Price.levy hG X a (g0:=b) (easy x₀ hK) hy).1
    have hv: Collection.archive X R c a α Δ-Collection.archive X R c b α z=archive X R c (a-b) 0 D:= funext fun i=> archive_sub (hq _ hK).smooth (hq _ hY).smooth _ _ _ _ _
    change Stocked _ _ (archive X R c a α Δ-archive X R c b α z) v; rw [hv]; apply (Price.dock hR ‹_› hG hn hd X (a-b) 0 D (show Meadow.Budget p X.reg ((a-b).logRead) ε from hy) hd').cheaper
    change t ε≤ _; rw [show t ε = ε * t 1 from by unfold t regularNeed; rw [abs_zero]; ring]; exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) ht.le).trans (div_mul_cancel₀ _ hu.ne'|>.le)
end YM.AnalyticBridge.VerifiedReset.Collection.Price
