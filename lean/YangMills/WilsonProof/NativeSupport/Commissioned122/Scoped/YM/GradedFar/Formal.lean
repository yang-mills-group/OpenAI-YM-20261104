import YangMills.WilsonProof.NativeSupport.Commissioned122.Scoped.YM.GradedFar.PricedRows
import YM.WiderProfiles.Basket

/-!
# After grade payment, the through-p *evaluation* estimate, before the physical inverse.

Does not assert existence of an expansion of any actually measured physical
observables. Those are later in the comparison. Unbounded T in this estimate;
measure the formal remainder on the **independently prescribed** continuum
position book (same preservation/pins as in `WiderProfiles.separate_predictor_inputs`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set Scale O O.Enh O.Score O.Read O.Canon PowerSeries
open Register MS MS.Book.Program Dframe XSpace XSpace.Normalize
open scoped Topology Classical BigOperators

section
variable {G : Gauge} {n m p k h H : ℕ}
    (V : Arenas G) (B : ℝ → Frames G) {d : Fin n → ℕ} {e : Fin m → ℕ}
    (hd : Covered d H) (he : Covered e H)

/-- (D^X) applied to c, with both through-p. Independent crops. -/
lemma crop_response_vector (x : Points n) (z : Points (1+m)) (h p : ℕ) (η : ℝ) (lh : h ≤ H)
    (t : ℂ) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    filedCrop122 p t (rowsResponse122 V B η z h lh he v (filedVector122 V x h p t u)) = ∑ i : Toon G h,
      filedCrop122 p t (tariff V x u (flash i)) * filedCrop122 p t (rowsResponse122 V B η z h lh he v (theory i)) := by
  rw [filedVector122, response_sum, filedCrop122_sum]; simp_rw [filedCrop122_C_mul]

/-- This is the only product recrop difference for (M.2) second inequality:
Powers above p of the **product of the separately cropped** c and D,
with the converted columns already in D and the whole basis vector c. -/
def overBill (t : ℝ) (x : Points n) (y : Points m) (h p : ℕ) (z : ℂ) (lh : h ≤ H)
    (he : Covered e H) (u : Appointed122Fields G d) (v : Appointed122Fields G e) :=
  ∑ i : Toon G h, bill p z (tariff V x u (flash i))
    (rowsResponse122 V B (-t) (outgoing (squeeze (-t) y)) h lh he v (theory i))

theorem filedSeparate122 (t : ℝ) (x : Points n) (y : Points m) (h p : ℕ) (z : ℂ) (lh : h ≤ H)
    (u : Appointed122Fields G d) (v : Appointed122Fields G e) :
    filedCrop122 p z (series V B (-t) (forest x (squeeze (-t) y)) hd he u v) -
      filedCrop122 p z (rowsResponse122 V B (-t) (outgoing (squeeze (-t) y)) h lh he v (filedVector122 V x h p z u)) =
    filedCrop122 p z (residual V B t x y h hd he lh u v) - overBill V B t x y h p z lh he u v * z^(p+1) := by
  rw [crop_response_vector]; simp_rw [separate_crop_exact, Finset.sum_add_distrib, overBill,
    Finset.sum_mul, residual, filedCrop122_sub, filedCrop122_sum]
  abel
end

-- Estimate those omitted powers **above** p. z varying; the shifted
-- terms remain bounded at log price for every z in the unit ball. No
-- geometric-series estimate.
lemma powers_price {I : Type} (z : I → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) (k : ℕ) :
    Rain 0 (fun (i : I) (_ : ℝ) => z i^k) := Rain.powers (Rain.cash ⟨1,hz⟩) k

lemma price_crop {I : Type} {F : I → ℝ → PowerSeries ℂ} {p : ℕ} {a : ℝ}
    (s : ChargeP (p+1) a F) (z : I → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    Rain a (fun i t => filedCrop122 p (z i) (F i t)) := by
  simp_rw [filedCropEq122]; exact Rain.sum _ (fun j hj => (s j (Finset.mem_range.mp hj)).wig (powers_price z hz j))

lemma price_bill {I : Type} {F G : I → ℝ → PowerSeries ℂ} {p : ℕ} {a : ℝ}
    (s : ChargeP (p+1) 0 F) (g : ChargeP (p+1) a G) (z : I → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    Rain a (fun i t => bill p (z i) (F i t) (G i t)) := by
  unfold bill; apply Rain.sum; intro j hj; obtain ⟨u,v⟩ := (in_rectangle p).mp (Finset.mem_filter.mp hj).1
  exact Rain.wig (Rain.cover (s j.1 (Nat.lt_succ_of_le u)) (g j.2 (Nat.lt_succ_of_le v))) (powers_price z hz _)

variable {G : Gauge} {n m p h H : ℕ} {V : Arenas G} {ψ : ℝ → PowerSeries ℂ} {B : ℝ → Frames G}
    (phys : O.Canon.Physical V ψ B) (law : Law V ψ B)
    {K : Set (Points n)} {S : Set (Points m)}
    (kc : IsCompact K) (hk : K ⊆ conf n) (sc : IsCompact S) (hs : S ⊆ Outside m)
    {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : Covered d H) (he : Covered e H)

include phys law
include kc hk sc hs in
lemma bill_charge {I : Type} (x : I → Points n) (hx : ∀ i, x i ∈ K) (y : I → Points m)
    (hy : ∀ i, y i ∈ S) (u : I → Appointed122Fields G d) (v : I → Appointed122Fields G e) {R L : ℝ}
    (within : ∀ i, FieldBudget (u i) R) (along : ∀ i, FieldBudget (v i) L) (h p : ℕ) (lh : h ≤ H)
    (z : I → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) : Rain 0
      (fun i t => overBill V B t (x i) (y i) h p (z i) lh he (u i) (v i)) := by
  unfold overBill; apply Rain.sum; intro q _
  exact Rain.size (price_bill (fare_charge phys kc hk x hx u within p (flash q))
    (response_charge phys law sc hs y hy he v along p lh q) z hz) (Nat.cast_nonneg _)

abbrev UnitDisk := {z : ℂ // ‖z‖ ≤ 1}

include kc hk sc hs
lemma overEstimate (h p : ℕ) (lh : h ≤ H) (R L : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ T in (atTop : Filter ℝ), ∀ x ∈ K, ∀ y ∈ S, ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e,
    FieldBudget u R → FieldBudget v L → ∀ z : ℂ, ‖z‖ ≤ 1 →
    ‖overBill V B (Real.log T) x y h p z lh he u v‖ ≤ C*(1+Real.log T)^a := by
  let I := (↥K × ↥S) × ({u : Appointed122Fields G d // FieldBudget u R} × {v : Appointed122Fields G e // FieldBudget v L}) × UnitDisk
  have price := bill_charge phys law kc hk sc hs he (I:=I)
    (fun i => i.1.1.val) (fun i => i.1.1.property) (fun i => i.1.2.val) (fun i => i.1.2.property)
    (fun i => i.2.1.1.val) (fun i => i.2.1.2.val) (fun i => i.2.1.1.property) (fun i => i.2.1.2.property)
    h p lh (fun i => i.2.2.val) (fun i => i.2.2.property)
  obtain ⟨C,hC,a,hf⟩ := toSpatial 0 (by rw [Nat.cast_zero]; exact price)
  refine ⟨C,hC,a,?_⟩; filter_upwards [hf] with T hf x hx y hy u v hu hv z hz
  simpa only [pow_zero, inv_one, mul_one] using hf (((⟨x,hx⟩,⟨y,hy⟩), (⟨u,hu⟩,⟨v,hv⟩), ⟨z,hz⟩) : I)

lemma residualEstimate (h p : ℕ) (lh : h ≤ H) (R L : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ T in (atTop : Filter ℝ), ∀ x ∈ K, ∀ y ∈ S, ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e,
    FieldBudget u R → FieldBudget v L → ∀ z : ℂ, ‖z‖ ≤ 1 →
    ‖filedCrop122 p z (residual V B (Real.log T) x y h hd he lh u v)‖ ≤ C*(1+Real.log T)^a * (T^(h+1))⁻¹ := by
  let I := (↥K × ↥S) × ({u : Appointed122Fields G d // FieldBudget u R} × {v : Appointed122Fields G e // FieldBudget v L}) × UnitDisk
  have price := price_crop (residual_charge phys law kc hk sc hs (I:=I)
    (fun i => i.1.1.val) (fun i => i.1.1.property) (fun i => i.1.2.val) (fun i => i.1.2.property) hd he
    (fun i => i.2.1.1.val) (fun i => i.2.1.2.val) (fun i => i.2.1.1.property) (fun i => i.2.1.2.property)
    h p lh) (fun i => i.2.2.val) (fun i => i.2.2.property)
  obtain ⟨C,hC,a,hf⟩ := toSpatial (h+1) (by push_cast; exact price)
  refine ⟨C,hC,a,?_⟩; filter_upwards [hf] with T hf x hx y hy u v hu hv z hz
  exact hf (((⟨x,hx⟩,⟨y,hy⟩), (⟨u,hu⟩,⟨v,hv⟩), ⟨z,hz⟩) : I)

/-- FormalDemand+column+crop estimate. May also work on arbitrary compact sets of fields
using the fixed finite horizon bound in this estimate. Entirely uniform in all THREE of the
unit-ball arguments u,v,z (R,L=1 for input fields; enlarged as needed, e.g., for unit legs).
Actual short-distance coupling currencies are treated separately. -/
theorem formal_ball (h p : ℕ) (lh : h ≤ H) (R L : ℝ) : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ T in (atTop : Filter ℝ), ∀ x ∈ K, ∀ y ∈ S, ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e,
    FieldBudget u R → FieldBudget v L → ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖filedCrop122 p z (series V B (-Real.log T) (forest x (T • y)) hd he u v) -
        filedCrop122 p z (rowsResponse122 V B (-Real.log T) (outgoing (T • y)) h lh he v (filedVector122 V x h p z u))‖ ≤
      C*((T^(h+1))⁻¹ + ‖z‖^(p+1)) * (1+Real.log T)^a := by
  obtain ⟨C,hC,a,E⟩ := residualEstimate phys law kc hk sc hs hd he h p lh R L
  obtain ⟨D,hD,b,E'⟩ := overEstimate (d:=d) phys law kc hk sc hs he h p lh R L
  refine ⟨max C D, lt_max_of_lt_left hC, a+b, ?_⟩
  filter_upwards [E, E', eventually_ge_atTop (1 : ℝ)] with T e f ht x hx y hy u v hu hv z hz
  have pos := zero_lt_one.trans_le ht; have log : 1 ≤ 1+Real.log T := le_add_of_nonneg_right (Real.log_nonneg ht)
  rw [← squeeze_log pos, filedSeparate122]
  apply le_trans (norm_sub_le ..)
  rw [norm_mul, norm_pow]
  apply le_trans (add_le_add (e x hx y hy u v hu hv z hz) (mul_le_mul_of_nonneg_right (f x hx y hy u v hu hv z hz) (by positivity)))
  rw [mul_right_comm (max C D), mul_add]
  gcongr <;> first | omega | simp

omit phys law

/-- Public formal estimate for ANY WilsonPrescription from the independent `Main.Match`.
All grades, truncation and analytic bridge from the formal side discharged. In particular
no physical charges, no assumption about lifting a bounded geometry estimate to growing T. -/
theorem formal_match (N : WilsonPrescription G) {M : MS.Land.MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {Sms : MS.Land.Prescription (Press.portDeck G)} (ν : ℝ)
    {hG : G.Simple} (matchH : Main.Match N hG M Sms true) (h p : ℕ) (lh : h ≤ H) (R L : ℝ) :
    let V := Scale.Measure.outlook N.scheme N.criterion
    let B := GroupS.gaugeN N.scheme N.criterion M ν
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ, ∀ᶠ T in (atTop : Filter ℝ), ∀ x ∈ K, ∀ y ∈ S,
    forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
    ∀ u : Appointed122Fields G d, ∀ v : Appointed122Fields G e, FieldBudget u R → FieldBudget v L → ∀ z : ℂ, ‖z‖ ≤ 1 →
      ‖filedCrop122 p z (series V B (-Real.log T) (forest x (T • y)) hd he u v) -
        filedCrop122 p z (rowsResponse122 V B (-Real.log T) (outgoing (T • y)) h lh he v (filedVector122 V x h p z u))‖ ≤
      C*((T^(h+1))⁻¹ + ‖z‖^(p+1)) * (1+Real.log T)^a := by
  intro V B
  obtain ⟨C,hC,a,E⟩ := formal_ball (matchH.separatedOPE ν).wilson (matchH.dilation ν).check kc hk sc hs hd he h p lh R L
  refine ⟨C,hC,a,?_⟩; filter_upwards [E, configurations kc hk sc hs] with T e h x hx y hy
  exact ⟨(h x hx y hy).1, (h x hx y hy).2, e x hx y hy⟩
end YM.FVA2.GradedFar
