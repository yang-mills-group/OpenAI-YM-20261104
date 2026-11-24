import YM.Integration.FVA1Physical.Marked.BareWallet
import YM.Integration.FVA1Physical.Sources.Round2.PhysicalPrice

/-! Initialize the full mixed native bank from a calibrated physical bare
stencil on its own healthy sector. Every failed marker mode is then exactly
removed and every other one retains the prescribed physical value. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Multi Qlocal Qlocal.Quipu Quipu.Sonnet Tern Moonset MeasureTheory
open MergeProof.Accent Extra.Trajectories LocalLTE.Sail
open scoped Classical BigOperators

variable {I Ω : Type} [Fintype I] [DecidableEq I] {G : Gauge} {H : History G}
    {N n : ℕ} {B : Census I} {b d : ℕ} {ξ : I→ℕ}
    {o : I→Site (H.S.side N n)} {P : Rep G (H.S.side N n)}
    (W : Rooms.Wallet Ω o P B ξ d b) (t : Ω) (cut : ℕ) (g : ℝ) (Y : Batch H N n I)
    (isolated : ∀ s : Senses B, 2 ≤ (essence s).card → W.weight t s=0)
    (dictionary : ∀ j u, Healthy P.p.threshold (Tale.court P.p.B (o j)) u →
      ((bareLeaf W t cut g j u:ℝ):ℂ) = Y.wavelengths j u)
local notation "ok[" j "]" => Healthy P.p.threshold (Tale.court P.p.B (o j))
local notation "base" => fun u => ((H.rep N n N).eval u : ℂ) • Poly.pass (W.render cut g t u)

include isolated dictionary
/-- Exact conditional mask projection on each finite marker subset. Calibration
is required solely where each corresponding native scalar stencil survives. -/
theorem physical_masked_mode (v : Config G (H.S.side N n)) (s : B.Mode) :
    ((base) v).part s = if ∀ j∈s.val, ok[j] v then (Y.raw B v).part s else 0 := by
  rw [Poly.part_smul, singleton_render W t cut g isolated, Mach, pass_fire]
  change _ = if ∀ j∈s.val, ok[j] v then
    (((H.rep N n N).eval v : ℂ) • Poly.pass (Mach B (fun j => Y.wavelengths j v))).part s else 0
  rw [Poly.part_smul, Mach, pass_fire]
  split_ifs with active
  · congr 1
    exact Finset.prod_congr rfl (fun j hj => (if_pos (active j hj)).trans (dictionary j v (active j hj)))
  · push Not at active
    obtain ⟨j,hj,bad⟩ := active
    rw [Finset.prod_eq_zero hj (if_neg bad),mul_zero]

/-- No independent amplitudes or rates on failed stencils. The entire
absolute error is bounded by the price of the unmodified physical mixed
source, simultaneously for every nonnegative system of marker weights. -/
theorem masked_price (w : I→ℝ) (hw : ∀ j,0 ≤ w j) (v : Config G (H.S.side N n)) :
    Poly.price w ((base) v - Y.raw B v) ≤ Poly.price w (Y.raw B v) := by
  apply Finset.sum_le_sum
  intro s _
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j _ => hw j)
  change ‖((base) v).part s - (Y.raw B v).part s‖ ≤ _
  rw [physical_masked_mode W t cut g Y isolated dictionary]
  split <;> simp

theorem masked_norm (v : Config G (H.S.side N n)) :
    ‖(base) v - Y.raw B v‖ ≤ Poly.price (fun _=>1) (Y.raw B v) := by
  let d := (base) v - Y.raw B v
  apply le_trans _ (masked_price W t cut g Y isolated dictionary (fun _=>1) (fun _=>zero_le_one) v)
  change ‖d.part‖ ≤ Poly.price (fun _=>1) d
  apply (pi_norm_le_iff_of_nonneg (Poly.nonnegative (fun _=>zero_lt_one) d)).mpr
  intro s
  simpa only [Poly.toll,Finset.prod_const_one,one_mul] using Poly.member (fun _=>zero_lt_one) s d

/-- Mask projection preserves integrability of the actual complete physical
bare bank, with the original finite Wilson vacuum untouched. -/
theorem masked_integrable (selected : H.Selected) : Integrable (base) (prior G _) := by
  have seed := (integrable_pi_iff).mp (PhysicalNext.Repeat.Legato.Bandage.Harmonics.physicalSeed_integrable H selected B Y)
  refine integrable_pi_iff.mpr fun s => ?_
  let good : Set (Config G (H.S.side N n)) := {v | ∀ j∈s.val, ok[j] v}
  have measurable : MeasurableSet good := by
    change MeasurableSet {v | ∀ j∈s.val, ok[j] v}
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun j => isClosed_iInter fun _ => healthy_closed P.p.threshold (Tale.court P.p.B (o j))).measurableSet
  have eq : (fun v => ((base) v).part s) = good.indicator (fun v => (Y.raw B v).part s) := by
    funext v
    rw [physical_masked_mode W t cut g Y isolated dictionary]
    by_cases ok : v∈good
    · rw [Set.indicator_of_mem ok]
      exact if_pos ok
    · rw [Set.indicator_of_notMem ok]
      exact if_neg ok
  change Integrable (fun v => ((base) v).part s) _
  rw [eq]
  exact (seed s).indicator measurable

end YM.Integration.FVA1Physical.Marked
