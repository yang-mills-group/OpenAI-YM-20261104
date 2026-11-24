import YM.Frontier6.Bouquet.Garland.Open
import YM.GradedFar.Coin
import YM.GradedFar.Increment
import YM.GradedFar.Sunlight
import YM.Integration.WilsonGraphCartesianJetBound

noncomputable section
namespace YM.Integration.WilsonGraphCompactCoordinateJets
open Filter Set
open scoped Topology ContDiff
open WilsonGraphCartesianJetBound (axis)

private theorem lastDirection {n : ℕ}
    (D : List (Fin n × YM.Axis) → (YM.Points n → ℂ) → YM.Points n → ℂ)
    (empty : ∀ f, D [] f = f)
    (step : ∀ c w f, D (c :: w) f = D w (fun y => fderiv ℝ f y (axis c)))
    (w : List (Fin n × YM.Axis)) (c : Fin n × YM.Axis) (f : YM.Points n → ℂ) :
    D (w ++ [c]) f = fun y => fderiv ℝ (D w f) y (axis c) := by
  induction w generalizing f with
  | nil => simp only [List.nil_append, step, empty]
  | cons i w ih => rw [List.cons_append, step, ih, step]

private theorem orderedEntries {n : ℕ}
    (D : List (Fin n × YM.Axis) → (YM.Points n → ℂ) → YM.Points n → ℂ)
    (empty : ∀ f, D [] f = f)
    (step : ∀ c w f, D (c :: w) f = D w (fun y => fderiv ℝ f y (axis c)))
    {U : Set (YM.Points n)} (hU : IsOpen U) {f : YM.Points n → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (l : ℕ) (w : Fin l → Fin n × YM.Axis) :
    EqOn (D (List.ofFn w).reverse f)
      (fun y => iteratedFDeriv ℝ l f y (fun i => axis (w i))) U := by
  induction l with
  | zero =>
    intro x _
    simp only [List.ofFn_zero, List.reverse_nil, empty, iteratedFDeriv_zero_apply]
  | succ l ih =>
    intro x hx
    rw [List.ofFn_succ, List.reverse_cons, lastDirection D empty step]
    have inU : ∀ᶠ y in 𝓝 x, y ∈ U := hU.mem_nhds hx
    have hnear : D (List.ofFn (Fin.tail w)).reverse f =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ l f y (fun i => axis (Fin.tail w i))) :=
      inU.mono fun _ hy => ih (Fin.tail w) hy
    change fderiv ℝ (D (List.ofFn (Fin.tail w)).reverse f) x (axis (w 0)) =
      iteratedFDeriv ℝ (l + 1) f x (fun i => axis (w i))
    have eqDeriv : fderiv ℝ (D (List.ofFn (Fin.tail w)).reverse f) x =
        fderiv ℝ (fun y => iteratedFDeriv ℝ l f y (fun i => axis (Fin.tail w i))) x :=
      hnear.fderiv_eq
    rw [eqDeriv]
    have smooth : DifferentiableAt ℝ (iteratedFDeriv ℝ l f) x :=
      (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top l))
    exact (smooth.iteratedFDeriv_succ_apply_left' (m := fun i => axis (w i))).symm

theorem enteredDirection {n : ℕ} (i : Fin n) (a : YM.Axis) :
    YM.Points.direction i a = axis (i,a) := by rfl

end YM.Integration.WilsonGraphCompactCoordinateJets
namespace YM.Integration.WilsonGraphCompactCoordinateJets
open Filter
open scoped Topology

/-- Two successive filed truncations control each positive heat coefficient uniformly.
The physical bound at a single admitted radius supplies the degree-zero coefficient. -/
theorem finiteCoefficientBounds {α I : Type*} (φ : Filter α) [φ.NeBot]
    (t : α → ℝ) (actual : α → I → ℂ) (row : I → ℕ → ℂ) (trunc : ℕ → α → I → ℂ)
    (ground : ∀ s i, trunc 0 s i = row i 0)
    (next : ∀ k s i, trunc (k+1) s i = trunc k s i + (t s : ℂ)^(k+1) * row i (k+1))
    (positive : ∀ᶠ s in φ, t s ≠ 0)
    (measured : ∀ᶠ s in φ, ∃ B : ℝ, ∀ i, ‖actual s i‖ ≤ B)
    (paid : ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in φ, ∀ i,
      ‖actual s i - trunc k s i‖ ≤ C * |t s|^(k+1)) :
    ∀ k, ∃ B : ℝ, ∀ i, ‖row i k‖ ≤ B := by
  intro k
  cases k with
  | zero =>
    obtain ⟨C, _, cost⟩ := paid 0
    obtain ⟨s, entered, B, bound⟩ := (cost.and measured).exists
    refine ⟨B + C * |t s|^(0+1), fun i => ?_⟩
    rw [← ground s i]
    calc
      ‖trunc 0 s i‖ = ‖actual s i - (actual s i - trunc 0 s i)‖ := by
        congr 1
        abel
      _ ≤ ‖actual s i‖ + ‖actual s i - trunc 0 s i‖ := norm_sub_le _ _
      _ ≤ B + C * |t s|^(0+1) := add_le_add (bound i) (entered i)
  | succ k =>
    obtain ⟨A, _, low⟩ := paid k
    obtain ⟨B, _, high⟩ := paid (k+1)
    obtain ⟨s, lo, hi, nz⟩ := (low.and (high.and positive)).exists
    refine ⟨(A * |t s|^(k+1) + B * |t s|^(k+1+1)) / |t s|^(k+1), fun i => ?_⟩
    apply (le_div_iff₀ (pow_pos (abs_pos.mpr nz) (k+1))).mpr
    calc
      ‖row i (k+1)‖ * |t s|^(k+1) = ‖(t s : ℂ)^(k+1) * row i (k+1)‖ := by
        simp [mul_comm]
      _ = ‖(actual s i - trunc k s i) - (actual s i - trunc (k+1) s i)‖ := by
        rw [next]
        congr 1
        ring
      _ ≤ ‖actual s i - trunc k s i‖ + ‖actual s i - trunc (k+1) s i‖ := norm_sub_le _ _
      _ ≤ A * |t s|^(k+1) + B * |t s|^(k+1+1) := add_le_add (lo i) (hi i)

end YM.Integration.WilsonGraphCompactCoordinateJets

namespace YM.Integration.WilsonGraphCompactCoordinateJets
open Function Filter Set PowerSeries
open GradedFar
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits
open FVA2 XSpace XSpace.Normalize XSpace.Structure1 FVA2.Scale FVA2.Scale.Facets
open FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet
open YM.Integration.GradedFar.Neighbor YM.Integration.GradedFar.Tariff
open Tariff.Sunshine Tariff.Tickets
open scoped Topology BigOperators Classical ContDiff

/-- The filed compact estimate enters the original signed invoice with zero logarithmic power. -/
theorem paidValue {X I : Type*} (p : ℕ) (φ : Filter X) (W : X → I → Prop)
    (B : X → I → ℝ) (t : X → ℝ) (f : X → I → ℂ) (F : X → I → PowerSeries ℂ)
    (terms : Prospects φ W B F)
    (physical : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in φ, ∀ i, W s i →
      ‖f s i - crop p (t s) (F s i)‖ ≤ C * |t s|^(p+1)) :
    WithTax p φ W B t f F := by
  obtain ⟨C, hc, priced⟩ := physical
  refine ⟨terms, 0, C, hc, ?_⟩
  filter_upwards [priced] with s hs
  intro i hi
  simpa using hs i hi

section
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Final C f S) (P : ℝ → tower S) (Z : WilsonPrescription G)
variable (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable {hG : G.Simple} {σ : MS.Land.Prescription (Press.portDeck G)}
variable (H : Main.Match Z hG M σ true)
variable {n p : ℕ} {α I : Type*} (φ : Filter α) (r : α → ℝ) (scale : Tendsto r φ trail)
variable {W : α → I → Prop} (z : α → I → Points n) (view : α → I → Viewers F)
variable {t : ℝ → ℝ} (clock : Coupling G t) (connected : ∀ cap, Included F P cap (cap+1) (Nat.le_succ cap))
local notation "X" => Scale.Measure.outlook Z.scheme Z.criterion
local notation "invoice" => WithTax p φ W (fun _ _ => 1) (t ∘ r)

/-- The stationary #140 series is funded by its scalar compact prices at all orders.
Its lowest row uses the original smooth measured moment, and positive rows use successive prices. -/
theorem stationaryFromValues (h : ℕ) (positive : ∀ᶠ s in trail, t s ≠ 0)
    (values : ∀ K : Set (Points n), IsCompact K → K ⊆ conf n → ∀ v : ListInput G n h,
      ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in trail, ∀ x : K,
        ‖frank F P none h s x.val v - crop j (t s) (sent X h x.val v)‖ ≤ C * |t s|^(j+1)) :
    ClassExpansion F P X t n h := by
  intro K hK separated v
  have measured : ∀ᶠ s in trail, ∃ B : ℝ, ∀ x : K, ‖frank F P none h s x.val v‖ ≤ B := by
    filter_upwards [show ∀ᶠ s in trail, 0 < s from self_mem_nhdsWithin] with s hs
    obtain ⟨B, bounded⟩ := hK.exists_bound_of_continuousOn
      ((true_views F P none hs v).continuousOn.mono separated)
    exact ⟨B, fun x => bounded x.val x.property⟩
  have stock := finiteCoefficientBounds trail t (fun s (x : K) => frank F P none h s x.val v)
    (fun x j => coeff j (sent X h x.val v)) (fun j s x => crop j (t s) (sent X h x.val v))
    (fun s x => by simp [crop_eq])
    (fun j s x => by simp only [crop_eq]; rw [Finset.sum_range_succ])
    positive measured (values K hK separated v)
  exact ⟨fun j => FVA2.GradedFar.Cart.Charge.cap (stock j),
    fun j => ⟨values K hK separated v j⟩⟩

include H clock connected scale in
/-- Original coordinate differentiation with the all-viewer compact base and the actual
stationary rows at the raising and target arities. The current chart and viewer stay fixed. -/
theorem prices {K : Set (Points n)} (separated : K ⊆ conf n)
    (placed : ∀ s i, W s i → z s i ∈ K)
    (two : ∀ cap, ClassExpansion F P X t 2 cap)
    (target : ∀ cap, ClassExpansion F P X t n cap)
    (paid : ∀ cap (v : ListInput G n cap), invoice
      (fun s i => frank F P (view s i) cap (r s) (z s i) v)
      (fun s i => sent X cap (z s i) v))
    (h : ℕ) (L : TraceOrder n) (v : ListInput G n h) : invoice
      (fun s i => δ L (fun x => frank F P (view s i) h (r s) x v) (z s i))
      (fun s i => jetCost L X h v (z s i)) := by
  choose A ha using fun i => futureWins F P Z M H clock (connected i) (two (i+1))
  have coins : Coins φ W (fun _ _ => 1) (t ∘ r) :=
    ⟨Filter.Eventually.of_forall (fun _ _ _ => ⟨le_rfl, zero_le_one⟩),
      (Coupling.conforms hG clock).comp scale⟩
  have site : ∀ᶠ s in φ, ∀ i, W s i → z s i ∈ conf n :=
    Filter.Eventually.of_forall fun s i hi => separated (placed s i hi)
  induction L generalizing h with
  | nil =>
    simp_rw [δ, jetCost_zero]
    exact paid h v
  | cons i L ih =>
    let w := v i.1
    let α := A h i.2 w
    let c (s : ℝ) (j : Toon G (h+1)) := coord j (push F P h i.2 s w)
    let Y (j : Toon G (h+1)) := update (climbing v) i.1 (theory j)
    have hc (j) : invoice (fun s (_ : I) => c (r s) j) (fun _ _ => α j) := by
      have entered := ha h i.2 w j
      refine ⟨fun k => Fork.Sold.closed _, ?_⟩
      obtain ⟨C, hC, hp⟩ := (entered.good p).cost
      exact Fork.Sold.bounded hC ((scale.eventually hp).mono (fun s hs _ _ => hs ()))
    refine (WithTax.sum coins Finset.univ (fun j _ => (hc j).mul coins (ih _ (Y j)))).tran ?_ ?_
    · filter_upwards [scale.eventually (show ∀ᶠ r in trail, 0 < r from self_mem_nhdsWithin), site,
        scale.eventually (show ∀ᶠ r in trail, Going F P h r from connected h)] with s hr hs hg i' hi'
      exact (physical_cons F P (hs i' hi') hr hg (view s i') L i v).symm
    exact site.mono fun s hs i' hi' =>
      (jetCost_cons F P Z M H clock connected target A ha (hs i' hi') L i v).symm
include H clock connected in
/-- Smoothness of the actual appointed formal coefficient from the original two
stationary expansions at the raised two-point and target arities. -/
theorem smoothCoefficients
    (two : ∀ cap, ClassExpansion F P X t 2 cap)
    (target : ∀ cap, ClassExpansion F P X t n cap)
    (h : ℕ) (v : ListInput G n h) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun x => coeff j (sent X h x v)) (conf n) := by
  choose A ha using fun i => futureWins F P Z M H clock (connected i) (two (i+1))
  exact Air F P Z M H clock connected target A ha v j

include H clock connected in
/-- Every actual coefficient is bounded on the selected compact separated chart. -/
theorem formalCosts {K : Set (Points n)} (compact : IsCompact K) (separated : K ⊆ conf n)
    (placed : ∀ s i, W s i → z s i ∈ K)
    (two : ∀ cap, ClassExpansion F P X t 2 cap)
    (target : ∀ cap, ClassExpansion F P X t n cap)
    (h : ℕ) (v : ListInput G n h) :
    Prospects φ W (fun _ _ => 1) (fun s i => sent X h (z s i) v) := by
  intro j
  have smooth := smoothCoefficients F P Z M H clock connected two target h v j
  obtain ⟨C, hC⟩ := compact.bddAbove_image (smooth.continuousOn.norm.mono separated)
  apply Fork.Sold.bounded (c := max 0 C) (le_max_left _ _)
  refine Filter.Eventually.of_forall fun s i hi => ?_
  have bounded := hC (Set.mem_image_of_mem _ (placed s i hi))
  simpa only [mul_one] using bounded.trans (le_max_right 0 C)

include H clock connected in
/-- Coordinate differentiation commutes with the finite, genuinely truncated heat series. -/
theorem cropCoordinates
    (two : ∀ cap, ClassExpansion F P X t 2 cap)
    (target : ∀ cap, ClassExpansion F P X t n cap)
    (h : ℕ) (v : ListInput G n h) (L : TraceOrder n) (p : ℕ) (s : ℝ)
    {x : Points n} (hx : x ∈ conf n) :
    crop p s (jetCost L X h v x) = δ L (fun y => crop p s (sent X h y v)) x := by
  let row (i : ℕ) (y : Points n) := coeff i (sent X h y v)
  have smooth (i : ℕ) : ContDiffOn ℝ ∞ (row i) (conf n) :=
    smoothCoefficients F P Z M H clock connected two target h v i
  simp_rw [crop_eq, jetCost, coeff_mk]
  rw [δ_sum (conf_open n) _ (fun (i : ℕ) y => (s : ℂ)^i * row i y)
    (fun i _ => contDiffOn_const.mul (smooth i)) L hx]
  exact Finset.sum_congr rfl fun i _ => (δ_const_mul (conf_open n) (smooth i) _ L hx).symm

include H clock connected scale in
/-- At fixed compact positions the genuine all-viewer value estimate and the stationary
raising coefficients price every coordinate word on the original scale filter. -/
theorem compact {K : Set (Points n)} (hK : IsCompact K) (separated : K ⊆ conf n)
    (placed : ∀ s i, W s i → z s i ∈ K)
    (two : ∀ cap, ClassExpansion F P X t 2 cap)
    (target : ∀ cap, ClassExpansion F P X t n cap)
    (physical : ∀ cap (v : ListInput G n cap), ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in φ,
      ∀ i, W s i → ‖frank F P (view s i) cap (r s) (z s i) v -
        crop p (t (r s)) (sent X cap (z s i) v)‖ ≤ C * |t (r s)|^(p+1))
    (h : ℕ) (L : TraceOrder n) (v : ListInput G n h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in φ, ∀ i, W s i →
      ‖δ L (fun y => frank F P (view s i) h (r s) y v) (z s i) -
        δ L (fun y => crop p (t (r s)) (sent X h y v)) (z s i)‖ ≤
          C * |t (r s)|^(p+1) := by
  have paid (cap : ℕ) (u : ListInput G n cap) : invoice
      (fun s i => frank F P (view s i) cap (r s) (z s i) u)
      (fun s i => sent X cap (z s i) u) :=
    paidValue p φ W (fun _ _ => 1) (t ∘ r) _ _
      (formalCosts F P Z M H φ z clock connected hK separated placed two target cap u)
      (physical cap u)
  obtain ⟨_, D, hD, entries⟩ :=
    (prices F P Z M H φ r scale z view clock connected separated placed two target paid h L v).error
  refine ⟨D, hD, ?_⟩
  filter_upwards [entries] with s hs
  intro i hi
  rw [← cropCoordinates F P Z M H clock connected two target h v L p (t (r s))
    (separated (placed s i hi))]
  simpa only [Function.comp_apply, one_pow, mul_one] using hs i hi

end

/-- The original nested shape-gradient word in its chronological derivative order. -/
theorem coordinates {n l : ℕ} {U : Set (Points n)} (hU : IsOpen U)
    {f : Points n → ℂ} (hf : ContDiffOn ℝ ∞ f U) (w : Fin l → Fin n × Axis) :
    EqOn (δ (List.ofFn w).reverse f)
      (fun y => iteratedFDeriv ℝ l f y (fun i => WilsonGraphCartesianJetBound.axis (w i))) U :=
  orderedEntries δ (fun _ => rfl) (fun c w f => by
    change δ w (fun y => fderiv ℝ f y (YM.Points.direction c.1 c.2)) = _
    rw [enteredDirection]) hU hf l w

/-- Full public measured jet from the original coordinate invoices at one common scale. -/
theorem original {n : ℕ} {α : Type*} {I : α → Type*} (F : Filter α) (j : ℕ)
    (actual predicted : (s : α) → I s → Points n → ℂ)
    (point : (s : α) → I s → Points n) (err : (s : α) → I s → ℝ)
    (herr : ∀ s u, 0 ≤ err s u)
    (smooth : ∀ᶠ s in F, ∀ u : I s, point s u ∈ conf n ∧
      ContDiffOn ℝ ∞ (actual s u) (conf n) ∧ ContDiffOn ℝ ∞ (predicted s u) (conf n))
    (entered : ∀ L : TraceOrder n, ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ s in F, ∀ u : I s,
      ‖δ L (actual s u) (point s u) - δ L (predicted s u) (point s u)‖ ≤ D * err s u) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ s in F, ∀ u : I s,
      YangMills.Matching.shapeJetEstimateAt j (actual s u) (predicted s u)
        (point s u) (A * err s u) := by
  apply WilsonGraphCartesianJetBound.original F j actual predicted point err herr
  · filter_upwards [smooth] with s hs
    intro u
    obtain ⟨hx, ha, hp⟩ := hs u
    exact ⟨(ha.contDiffAt ((conf_open n).mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤)),
      (hp.contDiffAt ((conf_open n).mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr (le_top : (j : ℕ∞) ≤ ⊤))⟩
  intro l w
  obtain ⟨D, hD, cost⟩ := entered (List.ofFn w).reverse
  refine ⟨D, hD, ?_⟩
  filter_upwards [smooth, cost] with s hs hc
  intro u
  obtain ⟨hx, ha, hp⟩ := hs u
  have left : δ (List.ofFn w).reverse (actual s u) (point s u) =
      iteratedFDeriv ℝ (l : ℕ) (actual s u) (point s u) (fun i => WilsonGraphCartesianJetBound.axis (w i)) :=
    coordinates (conf_open n) ha w hx
  have right : δ (List.ofFn w).reverse (predicted s u) (point s u) =
      iteratedFDeriv ℝ (l : ℕ) (predicted s u) (point s u) (fun i => WilsonGraphCartesianJetBound.axis (w i)) :=
    coordinates (conf_open n) hp w hx
  simpa only [left, right] using hc u
end YM.Integration.WilsonGraphCompactCoordinateJets

