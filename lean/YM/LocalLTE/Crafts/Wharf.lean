import YM.LocalLTE.Crafts.Sand
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
include hn hG hR hd hq hh hK hv
variable (α:ℝ)(M:ℕ)(F:ℝ→ ℕ→ EKey n→ Pot G n) (hF:∀ j≤M,∀ x∈K,∀ v:ℝ, 0<v→∀ᶠ y in 𝓝[K] x, Stocked p (Price.tubeX R p X) (F x j-F y j) v)
set_option quotPrecheck false
local notation "T" y=> azures c p R X (g y) M (delta (X.read (g y))) α (F y)
local notation "Z" y=> silt c R X (g y) M (delta (X.read (g y))) α (F y)
local notation "X₀"=> bells p R X M
local notation "V"=> Price.tubeX R p X
include hF
omit hn hG hR hd hq hh hK hv hF
lemma freshly_sub (R:PathData G)(v:Spikes n)(α β z:ℝ) : Price.freshly β α R v - Price.freshly z α R v= Price.freshly (β-z) 0 R v:=by
    unfold freshly; funext i; simp only [Pi.sub_apply, Function.comp_apply, mul_sub, mul_zero]
    exact (congr_fun (High.fresh_sub R v.2 0 _ _ _ _) _).trans (by rw [sub_self])
private lemma maskS (X:Support n)(f g:Config G n→ℝ) (t:ℝ) : masked t X (f-g)=masked t X f-masked t X g:=by
   funext i; simp only [Pi.sub_apply]; by_cases h:Healthy t X i; simp [masked,h]; simp [masked,h]
lemma remise_drift (P:BudgetPoint) (R:PathData G)(a:Spikes n)(α x y:ℝ): Price.remises x α P R a - Price.remises y α P R a= Price.remises (x-y) 0 P R a:=by
    unfold Price.remises; rw [← Price.freshly_sub R a α, Price.maskS, Price.maskS]; abel
lemma issuer (p:BudgetPoint)(R:PathData G)(β:ℝ)(i:Spikes n) : Continuous fun (x:ℝ)=> Price.unitH p R β x i:=by
    unfold Price.unitH; by_cases h: Price.changed p R i
    · simp_rw [if_pos h]; unfold Hret; fun_prop
    simp_rw [if_neg h]; exact continuous_const
include hR hv
lemma tallyH (α x:ℝ) : Summable (Price.unitH p R α x (n:=n)):=by
    let X i:=(Price.ridge (n:=n) R p i).support; let f:=Price.unitH p R α x (n:=n); have hx i:0≤f i:= Price.atop x α p R i
    have ht:= AbsoluteSums.Product.everyone_ne X p.B hx (fun i _=>⟨(Price.ridge R p i).site,(Price.ridge R p i).anchor⟩) (Price.torrid x α p R hR hv)
    refine ht.2.1.of_nonneg_of_le hx fun i=> ?_; change f i ≤ f i * Real.exp ((p.supportExponent+1)*coverNumber p.B (X i)); exact le_mul_of_one_le_right (hx _) (Real.one_le_exp (by have he:= p.exponent_pos; positivity))
include hq hh hK hn hd hG
local notation "J"=>numbering (Price.Fol n)
omit hv in
lemma longitudinal (ε:ℝ)(he:0<ε)(i:ℕ): ∀ᶠ y in 𝒪,∀ U:Config G n, ‖((T x₀)|>.logarithm i U)-((T y)|>.logarithm i U)‖≤ ε:=by -- notation fails
    let z:=J
    let t x:= brew X R c p g α x; let k x:= Price.remises (n:=n) (delta (X.read (g x))) α p R
    change ∀ᶠ y in _, ∀ U, ‖Sum.elim (t x₀|>.logarithm) (k x₀) (z i) U-Sum.elim (t y|>.logarithm) (k y) (z i) U‖≤ε
    cases hv':z i
    next i =>
       let P:=quoteL R p c 0 1 (fun _=>1) (numbering (LKey n) i)
       filter_upwards [hh.quote_at hG hq hR hd α hn x₀ hK (ε/(1+|P|)) (by positivity)] with y hy U
       exact (hy.2 i U).trans ((mul_le_mul_of_nonneg_left (show P≤1+|P| from (le_abs_self P).trans (le_add_of_nonneg_left zero_le_one)) (by positivity)).trans (div_mul_cancel₀ _ (ne_of_gt (by positivity))|>.le))
    next j =>
        let d x:= delta (X.read (g x)); let s y:= d x₀-d y
        have hz : Tendsto s 𝒪 (𝓝 0):= Metric.tendsto_nhds.mpr fun i he=> by filter_upwards [hh.drifting hG hq hK (half_pos he)] with y hy; rw [Real.dist_eq,sub_zero]; exact hy.trans_lt (half_lt_self he)
        have ht : unitH p R 0 0 j<ε:= by unfold unitH Hret; split_ifs <;> simp_all only [add_zero, abs_zero, zero_mul, mul_zero]
        filter_upwards [(((Price.issuer p R 0 j).continuousAt).tendsto.comp hz).eventually (gt_mem_nhds ht)] with y hy U
        have h': k x₀ j-k y j=remises (s y) 0 p R j:= Price.remise_drift p R j α _ _; change ‖(k x₀ j-k y j) U‖≤ ε; rw [h']; exact (Price.tending (s y) 0 p R hR j|>.2.2 U).trans (show unitH p R 0 (s y) j<ε from hy).le
omit hK
variable {w₀ q:ℝ→ℝ}(hD:∀ x∈K, Ingredients (Price.bells p R X M) (azures c p R X (g x) M (delta (X.read (g x))) α (F x)) p (q x) (w₀ x))
include hD hF
open Samples Ovens
-- recover Stocked every label despite additional masks
omit hF hv hR hq hh hG hn hd
include hD
lemma zinc (x:ℝ)(hx:x∈K) : Stocked p (X₀|>.reg) (T x).regular (q x):=by
     obtain ⟨_,_,_,H,_⟩:=(hD _ hx).pays; obtain ⟨g,h,hq⟩:= H.stamp.boundE; exact ⟨g,fun i=> ⟨H.stamp.regular.smooth i,h i⟩, hq⟩
include hF hv hR hq hh hG hn hd
lemma aroma : Flow p (fun x=> T x) (Price.bells p R X M) K:=by
    apply Progress.DirectedRecipe.Flow.mk
    · intro x hx i ε he; filter_upwards [Price.torque hR hv hG hn hd X K g hx hq hh α M F hF ε he,self_mem_nhdsWithin] with y hy hY
      obtain ⟨e,H,h⟩:= hy; obtain ⟨_,hx',_⟩:= Price.zinc X K g α M F hD x hx; obtain ⟨_,hy',_⟩:= Price.zinc X K g α M F hD y hY -- order. binders notation problem.
      apply (sup_varies (hx' i|>.1) (hy' i|>.1)).2; exact sup_le (H i|>.2) ((p.loMass _ _ (H i|>.2.1)).trans (by simpa using budget_single (h ((X₀).reg i|>.site)) i))
    refine Payments.steady (d:=fun x=> T x) (fun x hx i=>?_) (fun x hx i=> ⟨fun ε he=>Price.longitudinal hR hG hn hd X K g hx hq hh α M F ε he i,(hh.values x hx).2 i⟩) p
    let z:= J; let t x:= brew X R c p g α x; let k x:= Price.remises (n:=n) (delta (X.read (g x))) α p R
    change ∃ C,∀ U, ‖Sum.elim (t x|>.logarithm) (k x) (z i) U‖ ≤ C
    cases hz:z i; next i=> obtain ⟨w,he,H⟩:= (hq x hx).cheap; exact ⟨_,fun U=> Collection.Local.quote_soft (v:=g x) (R:=R) (c:=c) hG α _ he (hq x hx).smooth (numbering _ i) U⟩
    next j=> exact ⟨_, (Price.tending _ _ p R hR j|>.2.2)⟩
end YM.AnalyticBridge.VerifiedReset.Collection.Price
