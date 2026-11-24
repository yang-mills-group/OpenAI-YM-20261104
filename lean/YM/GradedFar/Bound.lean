import YM.GradedFar.Clock
import YM.GradedFar.Evaluation

/-!
# A bound on the moved Far readings in the original FVA2 prescription
-/
namespace YM.FVA2.GradedFar
noncomputable section
open Filter Function Real PowerSeries Set
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m : ℕ} {N : WilsonPrescription G}
  {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
  {simple : G.Simple} {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
variable {K : Set (Points n)} {S : Set (Points m)}
  (hK : IsCompact K) (hx : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ O.Enh.Outside m)
  (d : Fin n → ℕ) (e : Fin m → ℕ) (L R : ℝ) (p h : ℕ)

lemma squeeze_far (y : Points m) {T : ℝ} (ht : 0 < T) : squeeze (-log T) y = T • y := by
  unfold squeeze; rw [neg_neg, exp_log ht]
include H hK hx hS hy

/-- Pure formal estimate. Includes, explicitly, the compact clearance of all the
queried configurations. `price` is not named here; C and a incur no expense in UV
cutoff (these are continuum coefficients). T=physical Far stretch.

All arities. Unit-ball tuples (`L` resp. `R` equal 1, uses *fixed-horizon coord sup
norm*), indeed any fixed ball. Does not require the vectors to be normalized in their
homogeneous component; retains all components. In subscripts like `T^(-h-1)` we write
`T⁻¹^(h+1)` in Lean.
-/
theorem prices : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
    ∀ T ≥ T₀, ∀ x ∈ K, ∀ y ∈ S,
      (forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m)) ∧
      ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
      ∀ t g : ℝ, |t| ≤ 1 → |t| ≤ 2*g →
        ‖crop p t (Yx N M x y u v (log T)) - crop p t (Dx N M y v (log T) (cActual N x u h p t))‖ ≤
          C * (T⁻¹^(h+1) + g^(p+1)) * (1+log T)^a := by
  obtain ⟨C,hC,a,H0⟩ := bound_log d e H hK hx hS hy L R p h
  obtain ⟨T₀,h0⟩ := eventually_atTop.1 (H0.and (eventually_conf hK hx hS hy))
  refine ⟨C,hC,a,max 2 (exp T₀),le_max_left ..,?_⟩
  intro T ht x hk y hs
  have hu := (le_max_right 2 (exp T₀)).trans ht
  have hp : 0<T := lt_of_lt_of_le (exp_pos _) hu
  obtain ⟨P,Px,Py⟩ := h0 (log T) (Real.exp_le_exp.mp (by rwa [Real.exp_log hp]))
  refine ⟨⟨?_,?_⟩, fun u pu v pv t g ht hc => ?_⟩
  · rw [← squeeze_far y hp]; exact Px x hk y hs
  · rw [← squeeze_far y hp]; exact Py y hs
  simpa only [Real.exp_log hp] using P u pu v pv x hk y hs t g ht hc

/-- The second inequality of (M.2) as a strictly formal result; indeed applies to any
`t∼g`, all sufficiently small r. `calibrated` is precisely the t~g result called in the
supplied proof (see `Clock.lean` for reaching it, from PoseFit's hypotheses of the estimate).
See also the entry with the original thermometer. T range *even unbounded above*, as
permitted for this side (stronger than M.1).
-/
theorem paid (t : ℝ → ℝ) (calibrated : Tendsto (fun r => t r / gYM G r) (𝓝[>] (0:ℝ)) (𝓝 1)) :
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∃ T₀ : ℝ, 2 ≤ T₀ ∧
      ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ T ≥ T₀, ∀ x ∈ K, ∀ y ∈ S,
        ∀ u : Inputs G d, Within L u → ∀ v : Inputs G e, Within R v →
          ‖crop p (t r) (Yx N M x y u v (log T)) -
            crop p (t r) (Dx N M y v (log T) (cActual N x u h p (t r)))‖ ≤
            C * (T⁻¹^(h+1) + gYM G r^(p+1)) * (1+log T)^a := by
  obtain ⟨C,hC,a,T0,h0,hA⟩ := prices H hK hx hS hy d e L R p h
  refine ⟨C,hC,a,T0,h0,?_⟩
  filter_upwards [paid_reading simple t calibrated] with r hf T ht x hk y hs u hu v hv
  exact (hA T ht x hk y hs).2 u hu v hv (t r) (gYM G r) hf.2.2.1 hf.2.2.2
end
end YM.FVA2.GradedFar
