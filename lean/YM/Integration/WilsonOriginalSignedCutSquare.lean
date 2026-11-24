import YM.Integration.WilsonOriginalSignedShutterSquare
import YM.Integration.WilsonOriginalSignedPathCut
import YM.Integration.PhysicalAffineScalarGaussianWeights

/-! The actual flat physical Gram is the cut finite-sampler matrix on its
genuine clear free addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSignedCutSquare
open Function Filter Lattice Laurent Wilson RG RG.Supply RG.Shoot Precision Tree Exterior Matrix
open Pressure Pressure.Tube Pressure.Stores FreeResolvent FreeResolvent.Affine
open Next.SectorChange Next.SectorChange.Rows Next.Fluctuations Next.Fluctuations.Sector
open AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine AnalyticBridge.GaussianFieldAlignment
open PhysicalNext.Repeat PhysicalNext.Repeat.Malachite
open scoped Topology Classical BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S)

theorem chart {P : Teller G} (fund : P.Funds S T) (F : Forest S.ratio) (tag : S.Choices) (x : ℝ) :
    (profileGram T x 1 (bareStores S) F tag 0)⁻¹ =
       ((primary S F tag T.high T.up (shorter (till x)) 0)⁻¹).submatrix
       (Native.lineEquiv (G:=G) F x).symm (Native.lineEquiv (G:=G) F x).symm := by
  obtain ⟨Λ,_,hW,_⟩ := fund.feeds
  have hW₀ : T.up.Bounds T.high P.top.width P.top.paths Λ := by rw [fund.high]; exact hW
  have born := (affine_near (bareStores S) F x T tag (Push.SectorMeasure.funds_branch fund) hW₀).self_of_nhds
  have h0 : represent (decode (0:Vec G c 1)) = 1 := by
    change represent ((plain G c 1) 0) = _
    rw [map_zero,link_one]
  rw [h0] at born
  unfold profileGram
  rw [field_zero,born]
  exact Matrix.inv_submatrix_equiv (primary S F tag T.high T.up (shorter (till x)) 0) (Native.lineEquiv F x).symm (Native.lineEquiv F x).symm

theorem gap {P : Teller G} (fund : P.Funds S T) (geo : Bid.Larger (G:=G) S)
    (F : Forest S.ratio) (tag : S.Choices) (x : ℝ) (i j : In (G:=G) x (bareStores S) F) :
    let atKey := (Native.lineEquiv (G:=G) F x).symm
    |(profileGram T x 1 (bareStores S) F tag 0)⁻¹ i j -
      (primary S F tag T.high T.up all 0)⁻¹ (atKey i) (atKey j)| ≤
      WilsonOriginalSignedPathCut.price G S.patch S.kernel T.high P.top.paths P.top.width *
        Real.exp (-(P.top.width/4)*till x) := by
  intro atKey
  rw [chart T fund F tag x]
  exact WilsonOriginalSignedPathCut.entry T fund geo F tag (till x) (atKey i) (atKey j)

end YM.Integration.WilsonOriginalSignedCutSquare
