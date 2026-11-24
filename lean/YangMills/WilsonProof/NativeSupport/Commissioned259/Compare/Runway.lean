import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Simultaneous
/-!
# Spend price margin from the prepared quantitative hypotheses. Uniform
version for use on *exact* physical frame/data below.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m h z : ℕ}
variable {V : Arenas G} {B : ℝ→Frames G} {R : ℝ→PowerSeries ℂ}
    {O : Type*} {K : Set (Points n)} {S : Set (Points m)}
    {W U a b c:ℝ}
    {d : Fin n→ℕ} {e : Fin m→ℕ} (hd : ∀ i,d i≤z) (he : ∀ i,e i≤z) (hh : h ≤ z)
    (L : Law V R B) (P : _root_.YM.FVA2.O.Canon.Physical V R B)
    (hK : IsCompact K) (hk : K⊆conf n) (hS : IsCompact S) (hs : S⊆Outside m)
    (hw : 1 ≤ W) (hz : clears W K S) (hU : 0 ≤ U)
    {θ : ℝ→ℝ} (sim : G.Simple) (Hθ : Calibrated G θ) (F:Sweep O G d e) (F' : Probe O G h e)
    {D : Route G} (p : ℕ) (run : Prepared V B θ F F' hd he hh D W a b K S p)
private structure Runway (G : Gauge) (O : Type*) (d : Fin n→ℕ) (e : Fin m →ℕ) (K : Set (Points n)) (S : Set (Points m)) (U W a b : ℝ) where
  length : ℝ
  T : ℝ
  floor : W ≤ T
  limit : T ≤ a*g0 G length^(-b)
  x : K
  y : S
  o : O
  u : Balls U G d
  v : Balls U G e

local notation "g" => g0 G
include L P hK hk hS hs hw hz hU sim Hθ run
lemma M2_first : ∃ M : ℝ, 0<M ∧ ∃ q : ℕ,
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, T ≤ a*(g r)^(-b) →
    ∀ x ∈ K, ∀ y∈S, ∀ o, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      ‖at_far F D o r T x y u v - crop p (θ r) (measurement V B hd he x (T • y) (-Real.log T) u v)‖ +
        opCost (probed F' D o r T y v - predicted V B he hh (T • y) (-Real.log T) v p (θ r)) ≤
        M*(T^(∑ i,e i)*(g r)^(p+1))*(1+Real.log T)^q := by
  let I := Runway G O d e K S U W a b
  let X := comap (Runway.length : I→ℝ) (𝓝[>] (0:ℝ))
  obtain ⟨M,hM,q,H⟩ := estimateFirst hd he hh L P hK hk hS hs hw hz hU sim Hθ F F' p run (I:=I) (X:=X)
    (Eventually.of_forall fun i=> i.x.property) (Eventually.of_forall fun i=> i.y.property) tendsto_comap
    (Eventually.of_forall fun i=> i.floor) (Eventually.of_forall fun i=> i.limit) Runway.o
    (Eventually.of_forall fun i=> i.u.property) (Eventually.of_forall fun i=> i.v.property)
  refine ⟨M,hM,q,(eventually_comap.mp H).mono fun r h T hT hl x hx y hy o u hu v hv=>?_⟩
  exact h (⟨r,T,hT,hl,⟨x,hx⟩,⟨y,hy⟩,o,⟨u,hu⟩,⟨v,hv⟩⟩:I) rfl

lemma M3_band (packet : Comet O G d h) (δ : ℕ) (hseal : Seal F F' packet D U a b W K S δ)
    (reach : ℕ) {φ : ℝ} (hb : 0 < b) (hφ : 0 < φ) (hφ' : φ < 1)
    (hp' : reach+b*((↑(∑ j,e j):ℝ)+h+φ)+1 ≤ p+1) (hδ : (reach:ℝ)+δ+1 ≤ b*(1-φ))
    (hc : 0<c) : ∃ M : ℝ, 0<M ∧
    ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, c*(g r)^(-b) ≤ T → T ≤ a*(g r)^(-b) →
    ∀ x ∈ K, ∀ y∈S, ∀ o, ∀ u ∈ Balls U G d, ∀ v ∈ Balls U G e,
      checkPrice (at_far F D o r T x y u v) (crop p (θ r) (measurement V B hd he x (T • y) (-Real.log T) u v))
        (probed F' D o r T y v) (predicted V B he hh (T • y) (-Real.log T) v p (θ r))
        (packet o r x u) (purchased V u x h p (θ r)) ≤ M*T ^ (-((h:ℝ)+φ)) * g r ^ reach := by
  let I := {i : Runway G O d e K S U W a b // c*(g i.length)^(-b) ≤ i.T}
  let r(i:I) := i.val.length
  let X := comap r (𝓝[>] (0:ℝ))
  obtain ⟨M,hM,H⟩ := estimateCombined hd he hh L P hK hk hS hs hw hz hU sim Hθ F F' p run (X:=X)
    (Eventually.of_forall fun i=> i.val.x.property) (Eventually.of_forall fun i=> i.val.y.property) tendsto_comap
    (Eventually.of_forall fun i=> i.val.floor) (Eventually.of_forall fun i=> i.val.limit) (fun i=>i.val.o)
    (Eventually.of_forall fun i=> i.val.u.property) (Eventually.of_forall fun i=> i.val.v.property)
    packet δ hseal reach hb hφ hφ' hp' hδ hc (Eventually.of_forall fun i=> i.property)
  refine ⟨M,hM,(eventually_comap.mp H).mono fun r h T hT hc hl x hx y hy o u hu v hv=>?_⟩
  exact h (⟨⟨r,T,hT,hl,⟨x,hx⟩,⟨y,hy⟩,o,⟨u,hu⟩,⟨v,hv⟩⟩,hc⟩:I) rfl

omit L P hK hk hS hs hw hz hU sim Hθ run
lemma chooseBudget (D h δ reach : ℕ) {φ : ℝ} (hφ' : φ<1) : ∀ᶠ b : ℝ in atTop,
    0<b ∧ (reach:ℝ)+δ+1 ≤ b*(1-φ) ∧ ∀ᶠ p:ℕ in atTop, reach+b*((D:ℝ)+h+φ)+1 ≤ (p:ℝ)+1 := by
  filter_upwards [eventually_ge_atTop (((reach:ℝ)+δ+1)/(1-φ)), eventually_gt_atTop (0:ℝ)] with x hx hp
  exact ⟨hp, (div_le_iff₀ (by linarith only [hφ'])).mp hx,
    (tendsto_natCast_atTop_atTop (R:=ℝ)|>.eventually_ge_atTop ((reach:ℝ)+x*((D:ℝ)+h+φ))).mono fun i hi=>by exact add_le_add_left hi _⟩

include sim in
lemma ample (a : ℝ) (ha : 0 < a) (W : ℝ) (b : ℝ) (hb : 0 < b) : ∀ᶠ r in 𝓝[>] (0:ℝ), W ≤ a * (g r)^(-b) :=
  ((tendsto_rpow_neg_nhdsGT_zero (by linarith only [hb] : -b < 0)).comp (pace sim)|>.const_mul_atTop ha).eventually_ge_atTop W

end YM.FVA2.GradedFar259.Comparing
