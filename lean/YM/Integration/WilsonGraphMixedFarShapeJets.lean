import YM.Integration.WilsonGraphMixedFarRowRegularity
import YM.Integration.WilsonGraphSeparatedDerivativePrice
import YM.FVA2.Gen.Flat

/-! Real directions in the actual joined near and far coordinates of the filed scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.FVA2.GradedFar.AppointedMixedFarJets

open Filter Set PowerSeries YangMills YM.Answer.ContinuumLimit YM.Integration
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus O O.Score O.Enh Scale
open AppointedMixedFarRow
open scoped Topology BigOperators Classical ContDiff

universe u
variable {n m : ℕ}

private def coordinate (s : ℝ) (i : Fin (n+m)) : (YM.Points n × YM.Points m) →L[ℝ] E4 :=
  Fin.addCases
    (fun j => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => E4) j).comp
      (ContinuousLinearMap.fst ℝ (YM.Points n) (YM.Points m)))
    (fun j => Real.exp (-(-s)) • ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => E4) j).comp
      (ContinuousLinearMap.snd ℝ (YM.Points n) (YM.Points m)))) i

def directionMap (s : ℝ) : (YM.Points n × YM.Points m) →L[ℝ] YM.Points (n+m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+m) => E4)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (coordinate s))

theorem mapAt (s : ℝ) (z : YM.Points n × YM.Points m) : directionMap s z = placement s z := by
  ext1 i
  induction i using Fin.addCases with
  | left i =>
    change coordinate s (Fin.castAdd m i) z = forest z.1 (squeeze (-s) z.2) (Fin.castAdd m i)
    rw [forest_left]
    simp [coordinate]
  | right i =>
    change coordinate s (Fin.natAdd n i) z = forest z.1 (squeeze (-s) z.2) (Fin.natAdd n i)
    rw [forest_right]
    simp [coordinate,squeeze]

variable (g : GaugeGroup) (hg : g.IsSimple)
private abbrev N := _root_.IssuedMaxwell.ElectedPrescription.issued g hg
private abbrev Q := WilsonGraphPaperPublication.perspective.{u} g hg
private abbrev S := _root_.IssuedBridge.PostedAppointedConversion.filed
  (N g hg) (Q.{u} g hg).MS (Q.{u} g hg).matching (Teller.logNu 1)

theorem jetAt (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    (s : ℝ) (k l : ℕ) (z : YM.Points n × YM.Points m) (safe : placement s z ∈ YM.conf (n+m)) :
    iteratedFDeriv ℝ l (fun v => coeff k (series g hg w a s v)) z =
      (iteratedFDeriv ℝ l (fun x => WilsonGraphStandaloneCorrelation.converted
        (S.{u} g hg) k (publicLetters w a) x) (placement s z)).compContinuousLinearMap
          (fun _ => directionMap s) := by
  let L := directionMap (n := n) (m := m) s
  let F (x : YM.Points (n+m)) := WilsonGraphStandaloneCorrelation.converted
    (S.{u} g hg) k (publicLetters w a) x
  have hx : L z ∈ YM.conf (n+m) := by simpa only [L,mapAt] using safe
  have same : (fun v => coeff k (series g hg w a s v)) =ᶠ[𝓝 z] (fun v => F (L v)) := by
    have near : L ⁻¹' YM.conf (n+m) ∈ 𝓝 z := ((YM.conf_open _).preimage L.continuous).mem_nhds hx
    filter_upwards [near] with v hv
    change L v ∈ YM.conf (n+m) at hv
    rw [show L v = placement s v from mapAt s v] at hv ⊢
    exact coefficient.{u} g hg w a s v hv k
  have smooth := WilsonGraphSeparatedRegularity.convertedSmooth
    g (Q.{u} g hg).MS (S.{u} g hg) k (publicLetters w a)
  have order : ((l : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  have atL : ContDiffAt ℝ (l : ℕ) F (L z) :=
    ((smooth (L z) hx).contDiffAt ((YM.conf_open _).mem_nhds hx)).of_le order
  have pull : iteratedFDeriv ℝ l (fun v => F (L v)) z =
      (iteratedFDeriv ℝ l F (L z)).compContinuousLinearMap (fun _ => L) := by
    simpa only [zero_add] using (Gen.affine (n := l) (p := F) (y := z)
      (z := (0 : YM.Points (n+m))) L (by simpa only [zero_add] using atL))
  rw [← mapAt s z]
  exact (same.iteratedFDeriv ℝ l).eq_of_nhds.trans pull

theorem onCompact (w : Fin (n+m) → ℕ) (a : (i : Fin (n+m)) → Sec g.core (w i))
    (k l : ℕ) {K : Set (YM.Points (n+m))} (compact : IsCompact K) (safe : K ⊆ YM.conf (n+m)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (s : ℝ) (z : YM.Points n × YM.Points m), placement s z ∈ K →
      ∀ (v : Fin l → YM.Points n × YM.Points m) (φ : ℂ →L[ℂ] ℂ),
        ‖φ ((iteratedFDeriv ℝ l (fun t => coeff k (series g hg w a s t)) z) v)‖ ≤
          ‖φ‖*(D*∏ i, ‖placement s (v i)‖) ∧
        ‖φ ((iteratedFDeriv ℝ l (fun x => WilsonGraphStandaloneCorrelation.converted
          (S.{u} g hg) k (publicLetters w a) x) (placement s z)) (fun i => placement s (v i)))‖ ≤
          ‖φ‖*(D*∏ i, ‖placement s (v i)‖) := by
  obtain ⟨D,hD,price⟩ := WilsonGraphSeparatedDerivativePrice.directionsAndDual
    g (Q.{u} g hg).MS (S.{u} g hg) k (publicLetters w a) l compact safe
  refine ⟨D,hD,?_⟩
  intro s z hz v φ
  have bound := price _ hz (fun i => placement s (v i)) φ
  refine ⟨?_,bound⟩
  rw [jetAt.{u} g hg w a s k l z (safe hz)]
  change ‖φ ((iteratedFDeriv ℝ l (fun x => WilsonGraphStandaloneCorrelation.converted
    (S.{u} g hg) k (publicLetters w a) x) (placement s z)) (fun i => directionMap s (v i)))‖ ≤ _
  simp_rw [mapAt]
  exact bound

end YM.FVA2.GradedFar.AppointedMixedFarJets
end

