import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Object
import YangMills.WilsonProof.NativeSupport.Commissioned259.ScaleCost.Capital
/-! # Calibration bound & unit-ball conversion of section B's physical comparison

Note `bbcb` states M.1 with Sec inputs per operations, norm conventions per fixed cap
freely interchangeable. Application also to physical form (`MaxwellSlots`);
`display` identifies the labels in this Family. This file doesn't dispose of any hypotheses
about the *election/success* of the physical construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS Climb
open FVA2.Scale Comparing O.Score O.Enh Dframe _root_.YM.Trace.Pilot
open scoped Topology BigOperators Classical
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (sim : G.Simple)
    {n m h : ℕ} {t : ℝ→ℝ}

include sim
lemma continuity (paid : Coupling G t) : Calibrated G t := by
  have h := paid.running.const_mul G.slopeConstant; have hc : 0 < G.slopeConstant := Gauge.slopeConstant_pos sim
  rw [mul_inv_cancel₀ hc.ne'] at h; have H := Real.continuous_sqrt.continuousAt.tendsto.comp h; rw [Real.sqrt_one] at H
  apply Tendsto.congr' ?_ H
  filter_upwards [ScaleCost.holds_cash.eventually_gt_atTop 0,paid.positive] with i l j
  change Real.sqrt (G.slopeConstant * (ScaleCost.cash i * t i ^2))=t i / (Real.sqrt (G.slopeConstant * ScaleCost.cash i))⁻¹
  rw [←mul_assoc,Real.sqrt_mul (mul_pos hc l).le,Real.sqrt_sq j.le,div_inv_eq_mul,mul_comm]
lemma transition (paid : Calibrated G t) : t=O[late] (g0 G) := by
  refine IsBigO.of_bound 2 ?_; filter_upwards [coupling_payment sim paid, g0_pos sim] with i k hi
  rw [Real.norm_of_nonneg hi.le]; exact k.2.2

omit sim
abbrev legal {d:Caps n} (u : MaxwellSlots C d) := ∀ i, ‖u i‖≤1
abbrev display {d:Caps n} (u : MaxwellSlots C d) : Slots G d := fun i=> Free.fields C.labels (d i) (u i)
lemma enrollment (C:Family G) (d : Caps n) : ∃ L:ℝ, 0 < L ∧ ∀ u:MaxwellSlots C d, legal (C:=C) u → display (C:=C) u ∈ Balls L G d := by
  let f (i:Fin n) (j:Toon G (d i)) : (Bel C.book).Field (d i) →L[ℂ] ℂ:= LinearMap.toContinuousLinearMap ((coord j).comp (Free.fields C.labels (d i)).toLinearMap)
  refine ⟨1+∑i,∑j, ‖f i j‖, by positivity, fun u hu i j=>?_⟩
  refine le_trans ((f i j).le_opNorm (u i)) ?_
  calc ‖f i j‖*‖u i‖ ≤ ‖f i j‖ := mul_le_of_le_one_right (ContinuousLinearMap.opNorm_nonneg (f i j)) (hu i)
       _ ≤ ∑i,∑j, ‖f i j‖ := (Finset.single_le_sum (fun j (_:j∈(Finset.univ:Finset (Toon G (d i))))=> norm_nonneg (f i j)) (Finset.mem_univ j)).trans (Finset.single_le_sum (f:=fun (i:Fin n)=> ∑ j, ‖f i j‖) (fun _ _=> by positivity) (Finset.mem_univ i))
       _ ≤ _ := by linarith
-- convenience physical fixed vector fields with norm arbitrary can rescale; BB width constant both arities simultaneously
variable (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool}
    (H : Main.Match N sim M σ dial) {H0 : ℕ}
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion M ν

include H
lemma enrolling (C : Family G) {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H0)
    (he : ∀ i, e i ≤ H0) (hh : h ≤ H0) {K : Set (Points n)} {E : Set (Points m)}
    (hK : IsCompact K) (hc : K ⊆ conf n) (hE : IsCompact E) (hy : E ⊆ Outside m)
    {W : ℝ} (hW : 1 ≤ W) (ha : clears W K E) (paid : Calibrated G t) (p : ℕ) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ a : ℕ,
    ∀ᶠ r in late, ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ E, ∀ u : MaxwellSlots C d, legal (C:=C) u → ∀ v : MaxwellSlots C e, legal (C:=C) v →
      let u' := display (C:=C) u; let v' := display (C:=C) v
      ‖crop p (t r) (measurement Vx Bx hd he x (T • y) (-Real.log T) u' v') -
        crop p (t r) (center Vx Bx he (T • y) hh (-Real.log T) (purchased Vx u' x h p (t r)) v')‖ ≤
        C'*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a := by
  obtain ⟨L,hL,g⟩:= enrollment C d; obtain ⟨U,hU,f⟩:= enrollment C e
  obtain ⟨A,hA,k,h⟩:= M2 N ν M H hd he hh (hL.le.trans (le_max_right U L)) hK hc hE hy hW ha paid p
  exact ⟨A,hA,k,h.mono fun i h T hT x hx y hy u hu v hv=>h T hT x hx y hy _ (fun i j=> (g u hu i j).trans (le_max_right ..)) _ (fun i j=> (f v hv i j).trans (le_max_left ..))⟩
end YM.FVA2.GradedFar259.Original
