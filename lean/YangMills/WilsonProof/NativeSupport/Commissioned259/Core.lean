import YangMills.WilsonProof.NativeSupport.Commissioned259.Matched
import YangMills.WilsonProof.NativeSupport.Commissioned259.Clock
import YangMills.WilsonProof.NativeSupport.Commissioned259.Consistent
import YangMills.WilsonProof.NativeSupport.Commissioned259.Assay.Test

/-!
# Primary theorem, (M.2)(second inequality) independent formal sector

Entry point without the use at `Run` (at `Run` see `Application`). Imports & USES the actual
suppliers from the ORIGINAL project. (The WiderProfiles overlay's Application available in this
import; no need to consume any even-wider prices than the `Match` here). See documentation
for relation with the supplied original proof.

This lemma takes the preceding **real calibration** inputs of bbcb's `NearFarDelta`. Actual
prescribed t, not a formal t. Here write consumer with explicit cost assumptions (F.3 at
that same measured reading, t' of F), to check EXACTLY why it is affordable, also exercise
on a pair of G.1 hypotheses, separately. These uses are conditional; don't infer the real
physics comparisons e.g. from the same names in Match. `Application` for original measured
structures and proof of that cost from earlier physics inputs on U and J already chosen (as in §M);
`Pose` pins its supplier. We do NOT prove *all* those physical inputs. See README on what's
actually discharged.

At the M.1 calculations T≥threshold, T≤C'g^-B (here I omit the upper cutoff; applies
all T≥ ANY W with `clears`, so `Local.always_clear`). Works repeatedly for ANY subsets/masks and
arity costs, all Near/Far mixed caps and any sufficiently prepared common cap H₀. `Balls` sup
of absolute coordinates, L=1 for unit, compare all family members at the SAME coupling. No
Viewer argument to these predictions! Every Viewer/phase in physical comparison uses these
prices. To integrate **same** measure see `Assay.profile` (unrounded x, original y, any finite
signed joint measure even complex-weighted, explicitly retain µ.variation cost, no changing
Far positions between terms). Probe also empty. Full cert here includes all unit padding costs
`Faces`. No claims that C1.w alone pays any of these. Need the (F.O) and (F.1) suppliers;
basis & analytic cost bridge at `same_grade`, `term_charge`, `threshold`.
-/

set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open scoped Topology ContDiff BigOperators Classical
open FVA2.Scale O.Score O.Enh O.Canon Dframe
variable {G : Gauge} (N : WilsonPrescription G) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
variable {n m H0 h : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ H0)
    (he : ∀ i, e i ≤ H0) (hh : h ≤ H0)
    {L : ℝ} {K : Set (Points n)} {S : Set (Points m)}
    (hl : 0 ≤ L) (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact S) (hy : S ⊆ Outside m)
    {W : ℝ} (hW : 1 ≤ W) (ha : clears W K S)
    {t : ℝ→ℝ} (p : ℕ)
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "late" => 𝓝[>] (0:ℝ)
include H hl hK hc hS hy hW ha

/-- Consume PoseFit prices (in (M.1) already). If using §F.3 with exponent `m` on the
error, just take `m≥2`. No claim based solely on the existence of the prescriptions. -/
theorem formalM2 {t':ℝ→ℝ} (q:ℕ)
    (paid : Tendsto (fun r=> t' r/g0 G r) late (𝓝 1))
    (tFit : (fun r=> t r - t' r)=O[late] (fun r=> g0 G r^(q+2))) :
    (∀ᶠ r in late, |t r| ≤ 1 ∧ |t r| ≤ 2*g0 G r) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
      ∀ᶠ r in late, ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ S,
      ∀ u ∈ Balls L G d, ∀ v ∈ Balls L G e,
        ‖crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v) -
          crop p (t r) (center V B he (T • y) hh (-Real.log T)
            (purchased V u x h p (t r)) v)‖ ≤ C*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a := by
   have tBound := poseFit_calibrates sim q paid tFit
   exact ⟨(coupling_payment sim tBound).mono (fun i h=> h.2), M2 N ν M H hd he hh hl hK hc hS hy hW ha tBound p⟩

/-- Alternative analytic price under *only two* of the G.1 prices on the measured
clock. Here no need for an input directly specifying the growth of the measured t. Derive the extra cost used by (M.2) from
those earlier inputs. (Still takes (G.1) as specified, not claiming it from these hypotheses.) -/
theorem formalG (h2 : clockCost N ν M 2 t) (h3 : clockCost N ν M 3 t) : (t=O[late] (g0 G)) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ r in late, ∀ T ≥ W, ∀ x ∈ K, ∀ y ∈ S, ∀ u ∈ Balls L G d, ∀ v ∈ Balls L G e,
      ‖crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v) -
        crop p (t r) (center V B he (T • y) hh (-Real.log T) (purchased V u x h p (t r)) v)‖ ≤
        C*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a := by
   have tBound := measured_cost N ν M H h2 h3
   exact ⟨tBound, unsigned_price N ν M H hd he hh hl hK hc hS hy hW ha tBound p⟩
end YM.FVA2.GradedFar259
