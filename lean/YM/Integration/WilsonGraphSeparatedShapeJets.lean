import YM.Integration.WilsonGraphStandaloneCorrelation
import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest
import YangMills.WilsonProof.NativeSupport.MeasuredShapeJets

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonGraphSeparatedShapeJets

open YangMills YangMills.Matching
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open YM.MS YM.MS.Land YM.MS.Fleet YM.FVA2
open YM.XSpace YM.XSpace.Normalize
open Filter Set
open scoped BigOperators Classical Topology
open YM.Integration.WilsonGraphStandaloneCorrelation (cutoff within marks converted_read)

variable {g : YangMills.GaugeGroup} {n : ℕ}
local notation "Data" => YM.MS.Land.MS_Data g.core (YM.FVA2.Position.OpenAxis.Plot (YM.FVA2.Press.portDeck g.core))
local notation "Labels" => Fin n → YM.Integration.WilsonGraphStandaloneCorrelation.Label g

/-- The original same-deck coefficient is evaluated after each external field coefficient
has acted in that field's own grade. The coupling power uses the remaining total degree. -/
def nativeConverted (S : Conversion (maxwellReference g)) (T : Data)
    (k : ℕ) (a : Labels) (x : YangMills.Points n) : ℂ :=
  ∑ ν : Fin n → Fin (k+1), ∑ j : Fin (k+1),
    let used := ∑ i, (ν i).val
    if used + j.val ≤ k then
      (couplingPower S.f j.val (k-used) : ℂ) *
        YM.FVA2.Dframe.meteor (YM.FVA2.Teller.logNu 1) T (cutoff a) x j.val
          (fun i => YM.XSpace.Normalize.up (within a i) (S.Z (a i).1 (ν i).val (a i).2))
    else 0

theorem coefficient (S : Conversion (maxwellReference g)) (T : Data) (k : ℕ) (a : Labels)
    (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    YM.Integration.WilsonGraphStandaloneCorrelation.converted S k a x =
      nativeConverted S T k a x := by
  unfold YM.Integration.WilsonGraphStandaloneCorrelation.converted nativeConverted
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun j _ => ?_
  dsimp only
  split_ifs
  · apply congrArg (fun w : ℂ => (couplingPower S.f j.val (k - ∑ i, (ν i).val) : ℂ) * w)
    exact congrArg
      (fun f : YM.XSpace.Structure1.Point g.core (cutoff a) n =>
        f (marks (S.inputs a ν) (within (S.inputs a ν))))
      (YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6PhysicalGraphSumForest.sameBook
        (d := cutoff a) T x hx j.val)
  · rfl

/-- The finite prediction agrees on an open neighborhood of the separated point. -/
theorem prediction (S : Conversion (maxwellReference g)) (T : Data)
    (M : YangMills.MSbar.Coefficients (maxwellReference g))
    (read : M.correlation = YM.Integration.WilsonGraphStandaloneCorrelation.bare g)
    (clock : ℝ) (p : ℕ) (a : Labels) (x : YangMills.Points n) (hx : x ∈ YM.conf n) :
    (fun y => ∑ k : Fin (p+1), (clock : ℂ)^k.val * S.correlation M k.val a y) =ᶠ[𝓝 x]
      fun y => ∑ k : Fin (p+1), (clock : ℂ)^k.val * nativeConverted S T k.val a y := by
  filter_upwards [(YM.conf_open n).mem_nhds hx] with y hy
  exact Finset.sum_congr rfl fun k _ =>
    congrArg (fun z : ℂ => (clock : ℂ)^k.val * z)
      ((converted_read S M read k.val a y).trans (coefficient S T k.val a y hy))

private theorem residual {x : YangMills.Points n}
    {f g : YangMills.Points n → ℂ} (actual : YangMills.Points n → ℂ) (h : f =ᶠ[𝓝 x] g) :
    (fun y => actual y - f y) =ᶠ[𝓝 x] fun y => actual y - g y :=
  h.mono fun y hy => congrArg (fun z : ℂ => actual y - z) hy

theorem derivative (S : Conversion (maxwellReference g)) (T : Data)
    (M : YangMills.MSbar.Coefficients (maxwellReference g))
    (read : M.correlation = YM.Integration.WilsonGraphStandaloneCorrelation.bare g)
    (clock : ℝ) (p : ℕ) (a : Labels) (x : YangMills.Points n) (hx : x ∈ YM.conf n)
    (actual : YangMills.Points n → ℂ) (l : ℕ) :
    iteratedFDeriv ℝ l
      (fun y => actual y - ∑ k : Fin (p+1), (clock : ℂ)^k.val * S.correlation M k.val a y) x =
    iteratedFDeriv ℝ l
      (fun y => actual y - ∑ k : Fin (p+1), (clock : ℂ)^k.val * nativeConverted S T k.val a y) x :=
  ((residual actual (prediction S T M read clock p a x hx)).iteratedFDeriv ℝ l).eq_of_nhds

private theorem estimate {x : YangMills.Points n} {f g : YangMills.Points n → ℂ}
    {actual : YangMills.Points n → ℂ} {j : ℕ} {bound : ℝ} (h : f =ᶠ[𝓝 x] g)
    (paid : shapeJetEstimateAt j actual g x bound) : shapeJetEstimateAt j actual f x bound := by
  refine ⟨paid.1, paid.2.1.congr_of_eventuallyEq h, fun l hl => ?_⟩
  rw [((residual actual h).iteratedFDeriv ℝ l).eq_of_nhds]
  exact paid.2.2 l hl

theorem original (S : Conversion (maxwellReference g)) (T : Data)
    (M : YangMills.MSbar.Coefficients (maxwellReference g))
    (read : M.correlation = YM.Integration.WilsonGraphStandaloneCorrelation.bare g)
    (clock : ℝ) (p : ℕ) (a : Labels) (x : YangMills.Points n) (hx : x ∈ YM.conf n)
    (j : ℕ) (actual : YangMills.Points n → ℂ) (bound : ℝ) :
    shapeJetEstimateAt j actual
      (fun y => ∑ k : Fin (p+1), (clock : ℂ)^k.val * S.correlation M k.val a y) x bound ↔
    shapeJetEstimateAt j actual
      (fun y => ∑ k : Fin (p+1), (clock : ℂ)^k.val * nativeConverted S T k.val a y) x bound := by
  have h := prediction S T M read clock p a x hx
  exact ⟨estimate h.symm, estimate h⟩

/-- The actual hierarchy, measurement, phase, center, signed clock and bound are fixed
while the relative insertion configuration varies. -/
theorem measured {C : YangMills.WilsonFamily g} {W : YangMills.Hierarchy C}
    (H : YangMills.Matching.CorrelationOnly.Measurement (maxwellReference g) W)
    (S : Conversion (maxwellReference g)) (T : Data)
    (M : YangMills.MSbar.Coefficients (maxwellReference g))
    (read : M.correlation = YM.Integration.WilsonGraphStandaloneCorrelation.bare g)
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (phase : Option W.Character) (o : YangMills.Spacetime) (s A : ℝ)
    (x : YangMills.Points n) (hx : x ∈ YM.conf n) (p j : ℕ) :
    let a : Labels := fun i => ⟨d i, v i⟩
    let actual := fun y : YangMills.Points n =>
      W.correlation phase (H.inputs s a) (WithLp.toLp 2 fun i => o + s • y i)
    let bound := A * (∏ i, sectorMass (v i)) * |H.clock s|^(p+1)
    shapeJetEstimateAt j actual
      (fun y => ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * S.correlation M k.val a y) x bound ↔
    shapeJetEstimateAt j actual
      (fun y => ∑ k : Fin (p+1), (H.clock s : ℂ)^k.val * nativeConverted S T k.val a y) x bound := by
  intro a actual bound
  exact original S T M read (H.clock s) p a x hx j actual bound

end YM.Integration.WilsonGraphSeparatedShapeJets
end
