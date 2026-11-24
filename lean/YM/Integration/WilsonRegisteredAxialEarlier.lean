import YM.Integration.WilsonRegisteredAxialSpectator
import YM.Integration.ActualWilsonAbsoluteTransport

/-! The full signed upper test travels through the actual positive
conditional before any lower field is averaged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialEarlier
open MeasureTheory Filter Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonReportingForestAngularReflection WilsonInheritedRegisteredField WilsonRegisteredFrozenReading
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem raw {C:Family G} (made:C.Makes) {N per i:ℕ} (live:i ≤ N)
    {X:Config G (C.side i per)→ℂ} (paid:Integrable X (scene C.path N per i)):
    Integrable (fun U=>(C.path.rep N per i).eval U • X U) (prior G _):=by
  unfold scene at paid
  rw [integrable_withDensity_iff_integrable_smul' (dose_env made.wilson live).meas.ennreal_ofReal
    (ae_of_all _ fun _=>ENNReal.ofReal_lt_top)] at paid
  simp_rw [ENNReal.toReal_ofReal (dose_positive made.wilson live _).le,dose,div_eq_inv_mul,mul_smul] at paid
  let Z:=partition G (C.side N per) (C.path.β N per N)
  have pos:0<Z:=Wilson.partition_pos ..
  refine (paid.smul Z).congr (ae_of_all _ fun U=>?_)
  change Z • (Z⁻¹ • ((C.path.rep N per i).eval U • X U))=_
  rw [smul_smul,mul_inv_cancel₀ pos.ne',one_smul]

theorem measured (simple:G.Simple) (gate:posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m+1 ≤ N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per)) (H:Config G (R.family.side (m+1) per)→ℂ),
      let k:=m+1
      let μ:=scene R.family.path N per k
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      let b:=WilsonDegreeFourInheritedRange.height R p k
      let X U:=H U*previous R live v o b U
      MemLp H 2 μ → ∀u (earlier:u ≤ k),
      let η:=scene R.family.path N per u
      let T:=actualTransport R.family (N:=N) X earlier
      Integrable T η ∧ (∫ V,T V ∂η)=(∫ U,X U ∂μ) ∧
        (∫ V,‖T V‖ ∂η)*(Real.log (β k))^t ≤
          Real.sqrt (∫U,‖H U‖^2 ∂μ)*(ε*L.coeffSize (L.core Z.x)):=by
  filter_upwards [WilsonRegisteredAxialSpectator.tested R simple gate slow J clear a p base t he] with m receipt
  intro N per live d ref v o H k μ Z L b X hH u early η T
  have earned:=receipt N per live d ref v o H hH
  have funded:=raw R.makes live earned.1
  exact ⟨actualScene_integrable_of_weighted R.family R.makes (early.trans live)
      (actualTransport_weighted_integrable_of_integrable R.family R.makes live funded early),
    actualScene_transport R.family R.makes live funded early,
    (mul_le_mul_of_nonneg_right (ActualWilsonAbsoluteTransport.first R.family R.makes live funded early)
      (pow_nonneg (Real.log_nonneg ((A).fits.delayed k).le) t)).trans earned.2.1⟩

end YM.Integration.WilsonRegisteredAxialEarlier
end
