import YM.GradedFar.Penultimate
import YM.WiderProfiles.Basket
/-!
# On the `Main.Match` of WiderProfiles

Estimates ready for the evaluation parameter (not necessarily nonzero). Strong
T bound: needn't supply a cofinality/moving upper bound. It needs to be above a sufficiently
large *constant* for the indicated `x,y` compacta and other prices. The geometry and the cost
can be taken together.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Dframe O O.Score Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ}
    (N : WilsonPrescription G)
    {hG : G.Simple}
    (Z : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {σ : Prescription (Press.portDeck G)}
    (H : Main.Match N hG Z σ true) (ν : ℝ)
local notation "A" => Scale.Measure.outlook N.scheme N.criterion
local notation "F" => GroupS.gaugeN N.scheme N.criterion Z ν

include H

/-- The remainder on the independent prescription. A norm bound in an **absolute** clock
coordinate, on that very complex subtraction. See `Measured.lean` to use the prescribed
physical evaluation parameter and power error in g at all small positive r. -/
theorem formal (hd : Through l d) (he : Through l e) (hh : h ≤ l)
    (K : Set (Points n)) (S : Set (Points m))
    (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    (p : ℕ) (L : ℝ) (hL : 0 ≤ L) : ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ T : ℝ, T₀ ≤ T → ∀ x ∈ K, ∀ y ∈ S, forest x (T • y) ∈ conf (n+m) ∧
      outgoing (T • y) ∈ conf (1+m) ∧
      ∀ (u : Inputs G d) (v : Inputs G e), Box u L → Box v L → ∀ z : ℝ, |z| ≤ 1 →
        ‖difference A F (-Real.log T) hd he hh x y u v p z‖ ≤ C *
          ((T^(h+1))⁻¹ + |z|^(p+1)) * (1+Real.log T)^k := by
  -- Identical predictor suppliers as in `WiderProfiles.separate_predictor_inputs`;
  -- this chain also uses `H.dilation ν` for the homogeneous column prices.
  obtain ⟨C,hC,k,H0⟩ := log_time_budget hd he hh (H.separatedOPE ν).wilson
    (H.dilation ν).check hK hx hS hy p hL
  have hevent := Real.tendsto_log_atTop.eventually (H0.and (layout_eventually hK hx hS hy))
  obtain ⟨T₀, ht⟩ := eventually_atTop.mp hevent
  refine ⟨C,hC,k,max T₀ 2,le_max_right ..,?_⟩
  intro T hT x hX y hY
  have hp : 0 < T := lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) ((le_max_right ..).trans hT)
  obtain ⟨hk,hk'⟩ := ht T ((le_max_left ..).trans hT)
  obtain ⟨h₁,h₂⟩ := hk' x hX y hY; simp only [squeeze, neg_neg, Real.exp_log hp] at h₁ h₂
  refine ⟨h₁,h₂,?_⟩
  intro u v hu hv z hz
  have hw : Real.exp (-((h:ℝ)+1)*Real.log T) = (T^(h+1))⁻¹ := by
    rw [← Nat.cast_add_one, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hp]
  specialize hk (⟨⟨x,hX⟩,⟨y,hY⟩,u,v,hu,hv,z,hz⟩ : Domain d e G K S L)
  dsimp only at hk; rw [hw] at hk; exact hk

end YM.FVA2.GradedFar
