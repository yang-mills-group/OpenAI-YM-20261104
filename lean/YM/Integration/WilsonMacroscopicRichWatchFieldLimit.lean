import YM.Integration.WilsonMacroscopicRichWatchPlot
import YM.Integration.FilteredProductLimit

/-! The joint positive Wilson field with every homogeneous input resolved reaches the same macroscopic hearing. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchFieldLimit
open Set Function Filter MeasureTheory Spec OPE OPE.Orbits PhysMS Lattice Cells Wilson
open Next.UVStress StressFlux.Matching WilsonMacroscopicRichWatchReader
open WilsonMacroscopicRichWatchPlot WilsonMacroscopicRichFixedWatchSale FilteredWilsonProduct
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {I:Type}[Fintype I]{d:I→ℕ}

theorem full (F:Final C f S)(fac:Services C f S)
    (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S){a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]S.Field h)
    (fits:∀z,D (fun i=>(W i).tester S h z)=z)
    (v:(i:I)→(Climb.Bel C.book).Field (d i))(r:ℝ)(m:ℕ)(x:I → Cover)
    (sites:∀i,Injective (beside (fun j=>C.S.gridPoint m (x j)) (positions S (exterior S (W i))).ofLp)):
    Tendsto (fun k:ℕ×ℕ=>heard (calibrated S ∘ W) k (field F R J v r m x k))
      f.fuse (𝓝 (current W (fun j=>C.S.gridPoint m (x j)) (Frame.born J r v))):=by
  let E:=detector W D fits
  let pts:=fun j=>C.S.gridPoint m (x j)
  have old:=FilteredProductLimit.difference_tendsto F fac R E J v r m x sites
  apply tendsto_pi_nhds.mpr
  intro i
  let y:=(positions S (exterior S (W i))).ofLp
  let u:=fun j=>(tags S (exterior S (W i)) j).2
  have raw:Tendsto (fun k:ℕ×ℕ=>moment (C.beta k.1 k.2)
    (FilteredProductLimit.raw J v r m x k * listen E i k)) f.fuse
    (𝓝 (whole S pts (Frame.born J r v) y u)):=by
    apply (WilsonWholeLimit.whole_tendsto_actual F fac J r pts v y u (sites i)).congr'
    filter_upwards with k
    apply congrArg (moment (C.beta k.1 k.2))
    funext U
    rw [WilsonWholeLimit.product_split]
    change _=_*(∏j:Fin (exterior S (W i)).length,C.O k.1 k.2
      (detectorRaw S (tags S (exterior S (W i)) j)).2 (ceilSite C k.1 k.2 (y j))) U
    rw [Finset.prod_apply]
    rfl
  have diff:=tendsto_pi_nhds.mp old i
  have resolved:=raw.sub diff
  change Tendsto _ _ (𝓝 (whole S pts (Frame.born J r v) y u - (0:ℂ))) at resolved
  rw [sub_zero] at resolved
  apply resolved.congr'
  filter_upwards [(OPE.Cards.largeMesh f).eventually_ge_atTop (W i).t] with k live
  rw [FilteredProductLimit.difference,sub_sub_cancel]
  rw [show listen E i k=(calibrated S (W i)).plot k.1 k.2 from
    WilsonMacroscopicRichWatchPlot.original W D fits i k.1 k.2 live]
  rfl

end YM.Integration.WilsonMacroscopicRichWatchFieldLimit
