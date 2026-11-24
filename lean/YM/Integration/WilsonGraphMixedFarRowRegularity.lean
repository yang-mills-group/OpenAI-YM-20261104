import YM.Integration.WilsonGraphMixedFarFiledBook
import YM.Integration.WilsonGraphSeparatedRegularity

/-! Each coefficient on the submitted near and far word in its own finite public grades. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedMixedFarRow

open Filter Set PowerSeries YangMills YM.Answer.ContinuumLimit YM.Integration
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus O O.Score O.Enh Scale
open scoped Topology BigOperators Classical ContDiff

universe u
variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev scheme := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev perspective := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev conversion := _root_.IssuedBridge.PostedAppointedConversion.filed (scheme g hg)
  (perspective.{u} g hg).MS (perspective.{u} g hg).matching (Teller.logNu 1)

variable {n m : ℕ}

def placement (s : ℝ) (z : YM.Points n × YM.Points m) : YM.Points (n+m) :=
  forest z.1 (squeeze (-s) z.2)

def series (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    (s : ℝ) (z : YM.Points n × YM.Points m) : PowerSeries ℂ :=
  Continuation.row (scheme g hg)
    (d := fun i : Fin n => w (Fin.castAdd m i)) (e := fun i : Fin m => w (Fin.natAdd n i))
    z.1 (fun i => a (Fin.castAdd m i)) z.2 (fun i => a (Fin.natAdd n i)) s

theorem coefficient (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    (s : ℝ) (z : YM.Points n × YM.Points m) (safe : placement s z ∈ YM.conf (n+m)) (j : ℕ) :
    coeff j (series g hg w a s z) =
      WilsonGraphStandaloneCorrelation.converted (conversion.{u} g hg) j
        (publicLetters w a) (placement s z) := by
  let A (k : ℕ) := coeff k (series g hg w a s z)
  let B (k : ℕ) := WilsonGraphStandaloneCorrelation.converted (conversion.{u} g hg) k
    (publicLetters w a) (placement s z)
  have subtotal (q : ℕ) : ∑ k ∈ Finset.range (q+1), A k = ∑ k ∈ Finset.range (q+1), B k := by
    have value := AppointedMixedBook.filedAtPorts.{u} g hg w a z.1 z.2 q s 1 safe
    simpa only [A,B,series,placement,publicTruncation,Complex.ofReal_one,one_pow,one_mul] using value
  change A j = B j
  cases j with
  | zero => simpa using subtotal 0
  | succ j =>
    have joined := subtotal (j+1)
    rw [Finset.sum_range_succ A (j+1),Finset.sum_range_succ B (j+1),subtotal j] at joined
    exact add_left_cancel joined

private theorem locationSmooth (s : ℝ) : ContDiff ℝ ∞ (placement (n := n) (m := m) s) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+m) => E4)
  have projected : ContDiff ℝ ∞ (fun z : YM.Points n × YM.Points m => (placement s z).ofLp) := by
    apply contDiff_pi.mpr
    intro i
    induction i using Fin.addCases with
    | left i =>
      change ContDiff ℝ ∞ (fun z : YM.Points n × YM.Points m => forest z.1 (squeeze (-s) z.2) (Fin.castAdd m i))
      simp only [forest_left]
      exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => E4) i).contDiff.comp contDiff_fst
    | right i =>
      change ContDiff ℝ ∞ (fun z : YM.Points n × YM.Points m => forest z.1 (squeeze (-s) z.2) (Fin.natAdd n i))
      simp only [forest_right,squeeze,PiLp.smul_apply]
      have eval : ContDiff ℝ ∞ (fun z : YM.Points n × YM.Points m => z.2 i) :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => E4) i).contDiff.comp
          (contDiff_snd : ContDiff ℝ ∞ (fun z : YM.Points n × YM.Points m => z.2))
      have scalar : ContDiff ℝ ∞ (fun _ : YM.Points n × YM.Points m => Real.exp (-(-s))) := contDiff_const
      exact scalar.smul eval
  exact L.symm.contDiff.comp projected

theorem shapeRegular (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    (s : ℝ) (j : ℕ) :
    ContDiffOn ℝ ∞ (fun z : YM.Points n × YM.Points m => coeff j (series g hg w a s z))
      (placement s ⁻¹' YM.conf (n+m)) ∧
    ContDiffOn ℝ ∞ (fun z : YM.Points n × YM.Points m =>
      WilsonGraphStandaloneCorrelation.converted (conversion.{u} g hg) j
        (publicLetters w a) (placement s z)) (placement s ⁻¹' YM.conf (n+m)) := by
  have form := WilsonGraphSeparatedRegularity.convertedSmooth
    g (perspective.{u} g hg).MS (conversion.{u} g hg) j (publicLetters w a)
  have both := form.comp (locationSmooth (n := n) (m := m) s).contDiffOn
    (s := placement s ⁻¹' YM.conf (n+m)) (fun z hz => hz)
  refine ⟨both.congr ?_,both⟩
  intro z hz
  exact coefficient.{u} g hg w a s z hz j

theorem onCompact (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i)) (j : ℕ)
    {K : Set (YM.Points (n+m))} (compact : IsCompact K) (safe : K ⊆ YM.conf (n+m)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (s : ℝ) (z : YM.Points n × YM.Points m), placement s z ∈ K →
      ‖coeff j (series g hg w a s z)‖ ≤ D ∧
      ‖WilsonGraphStandaloneCorrelation.converted (conversion.{u} g hg) j
        (publicLetters w a) (placement s z)‖ ≤ D := by
  obtain ⟨D,hD,price⟩ := WilsonGraphSeparatedRegularity.compactBound
    g (perspective.{u} g hg).MS (conversion.{u} g hg) j (publicLetters w a) compact safe
  refine ⟨D,hD,?_⟩
  intro s z hz
  rw [coefficient.{u} g hg w a s z (safe hz) j]
  exact ⟨price _ hz,price _ hz⟩

end YM.FVA2.GradedFar.AppointedMixedFarRow
end

