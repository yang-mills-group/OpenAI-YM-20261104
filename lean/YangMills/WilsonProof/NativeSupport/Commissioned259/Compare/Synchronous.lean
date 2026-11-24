import YangMills.WilsonProof.NativeSupport.Commissioned259.Compare.Receipt

/-! # Uniform basis-to-test estimate for the analytic part of NearFarDelta

This is the calculus used on the original operators (obtained from exactly the hypotheses given
in the proof) in the physical file. In particular `Sweep` may have selectors and phases &
placement origins; pay *one* scale and one moving Far crop on every such roster. No newer regulator
is used here, operates at continuum separation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Comparing
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} {n m h z : ℕ} {V : Arenas G} {B : ℝ→Frames G} {R : ℝ→PowerSeries ℂ}
    (L : Law V R B) (P : O.Canon.Physical V R B) {I O : Type*}
    {x : I→ Points n} {y : I→Points m} {K : Set (Points n)} {S : Set (Points m)}
    (hK : IsCompact K) (hk : K⊆conf n) (hS : IsCompact S) (hs : S⊆Outside m)
    {W U a b:ℝ} (hw : 1 ≤ W) (hz : clears W K S)
    {d : Fin n→ℕ} {e : Fin m→ℕ} (hd : ∀ i,d i≤z) (he : ∀ i,e i≤z)
    {θ : ℝ→ℝ} (sim : G.Simple) (Hθ : Calibrated G θ)

/-- Sweeps given by the actual all-at-r Row *at (x,T•y)*. Arguments here use UNSTRETCHED y.
Price called with these hypotheses for both Near cluster and at singleton center. -/
abbrev Sweep (O : Type*) (G : Gauge) (d : Fin n→ℕ) (e : Fin m→ℕ) := O → ℝ → ℝ → Points n → Points m → Response G d e
/-- Exact r-inverse to s Far conversion matrix at any one cap. -/
abbrev Route (G : Gauge) := ℝ→ℝ→(k:ℕ)→Module.End ℂ (Sec G k)

/-- consume T powers variant of (G.1) (numerical field estimates only), on the SAME B & caps. -/
structure Mileage (G : Gauge) (B : ℝ → Frames G) (θ : ℝ→ℝ) (D : Route G) (a b W : ℝ) : Prop where
  grows (k : ℕ) (g g' : Toon G k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, T ≤ a * g0 G r ^ (-b) →
      ‖coord g' (D r (r*T) k (theory g))‖ ≤ C * T^k
  -- for any required p': use any one high order q at each cap; independent of r,T
  fee (p k : ℕ) : ∃ q : ℕ, p+5 ≤ q ∧ ∀ (g g' : Toon G k),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, T ≤ a * g0 G r ^ (-b) →
      ‖coord g' (D r (r*T) k (theory g))-crop q (θ r) (badge B (-Real.log T) (theory g) g')‖ ≤ C * g0 G r ^ (p+2)

/-- Input `G.9`: even enough just on basis requests. -/
def Round (V : Arenas G) (θ : ℝ→ℝ) (O₁ : Sweep O G d e) (hd : ∀ i,d i≤z) (he : ∀ i,e i≤z) (p : ℕ)
    (a b W : ℝ) (K : Set (Points n)) (S : Set (Points m)) : Prop :=
  ∀ u v, ∃ C : ℝ, 0 ≤ C ∧ ∃ j : ℕ, ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ W, T ≤ a * g0 G r ^ (-b) →
    ∀ x ∈ K, ∀ y ∈ S, ∀ o, ‖O₁ o r T x y (word u) (word v) - reading V hd he x (T • y) p (θ r) (word u) (word v)‖ ≤
      C*(g0 G r)^(p+1)*(1+Real.log T)^j

/-- Actual all-at-r map precomposed by the genuine Far matrices only. -/
abbrev at_far (Y : Sweep O G d e) (A : Route G) (o : O) (r T x y) := adjusted (fun j=> A r (r*T) (e j)) (Y o r T x y)

/- Get the NEEDED sector budget even on sweeps. [cc analogue for converting power series in rH]. -/
variable {D : Route G} (mileage : Mileage G B θ D a b W) {X : Filter I}
    (hu : ∀ᶠ i in X,x i∈K) (hv : ∀ᶠ i in X, y i∈S) {T r : I→ℝ}
    (hi : Tendsto r X (𝓝[>] 0)) (hT : ∀ᶠ i in X, W ≤ T i)
    (ha : ∀ᶠ i in X, T i ≤ a*(g0 G (r i)) ^ (-b))
    (o : I→O)
    (Y : Sweep O G d e)
    (p : ℕ) (hR : Round V θ Y hd he p a b W K S)
local notation "μ" => (fun i:I=> g0 G (r i))
local notation "τ" => (fun i:I=> θ (r i))
local notation "γ" => (fun i:I=>-Real.log (T i))

include Hθ L P hK hk hS hs hw hz mileage hu hv hi hT ha hR sim

lemma sweeping {u : I→ Slots G d} {v : I→ Slots G e}
    (qU : ∀ q, Fare T X (fun _=>1) (fun i=> coordinates q (u i)))
    (qV : ∀ q, Fare T X (fun _=>1) (fun i=> coordinates q (v i))) : Fare T X (fun i=>T i^(∑ i,e i)*μ i^(p+1))
    (fun i=> at_far Y D (o i) (r i) (T i) (x i) (y i) (u i) (v i)-
      crop p (τ i) (measurement V B hd he (x i) (T i • y i) (γ i) (u i) (v i))) := by
  have hg : Tendsto μ X (𝓝[>] 0) := (pace sim).comp hi
  have theta := hi.eventually (coupling_payment sim Hθ)
  choose q Hq Hz using mileage.fee p
  let Y' i:= at_far Y D (o i) (r i) (T i) (x i) (y i); let pred i:= expansion V B hd he (x i) (T i • y i) (γ i) p (τ i)
  have heq (u : BasisSlots G d) (v : BasisSlots G e) : Fare T X (fun i=>T i^(∑ i,e i)*μ i^(p+1)) (fun i=> (Y' i - pred i) (word u) (word v)) := by
    refine first_line hd he L P hK hk hS hs hw hz hu hv hT ?_ ?_ ?_ (fun i=> Y (o i) (r i) (T i) (x i) (y i)) (fun i j=>D (r i) (r i*T i) (e j)) p (q ∘ e) (fun i=> le_trans (by omega) (Hq (e i))) ?_ ?_ ?_ u v
    · exact theta.mono fun i h=>h.2.1
    · refine IsBigO.of_bound 2 ?_; filter_upwards [theta,now hg] with i hi hg; exact (hi.2.2).trans_eq (by rw [Real.norm_of_nonneg (by exact hg.le)])
    · filter_upwards [now hg,near hg] with i h hi; exact (abs_of_pos h).trans_le hi
    · intro i b z; obtain ⟨C,hC,H⟩:= mileage.grows _ b z; refine IsBigO.of_bound C ?_; filter_upwards [hi.eventually H,hT,ha] with j h ht hΓ; exact (h _ ht hΓ).trans_eq (by rw [Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans (hw.trans ht)) _)])
    · intro i b z; obtain ⟨C,hC,H⟩:= Hz _ b z; refine IsBigO.of_bound C ?_; filter_upwards [hi.eventually H,hT,ha,now hg] with j h ht hΓ hk; exact (h _ ht hΓ).trans_eq (by rw [Real.norm_of_nonneg (show 0 ≤ μ j ^ (p+2) from pow_nonneg hk.le _)])
    intro u v; obtain ⟨C,hC,j,H⟩ := hR u v; refine Fare.of_le j C hC ?_; filter_upwards [hi.eventually H,hT,ha,hu,hv] with i h ht hΓ hx hy; exact (h _ ht hΓ _ hx _ hy _).trans_eq (mul_assoc ..)
  simp_rw [← expansion_eq]
  exact applying (hT.mono fun i ht=> hw.trans ht) (F:=fun i=> Y' i-pred i) _ heq qU qV
end YM.FVA2.GradedFar259.Comparing
