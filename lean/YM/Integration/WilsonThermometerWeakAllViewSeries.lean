import YM.Integration.WilsonThermometerWeakMeasuredSeries

/-! The one unselected signed comparison buys every ordinary physical
phase at once in the genuine measured frame and its calibrated coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakAllViewSeries
open Set Filter Function Spec Trace.Pilot OPE OPE.Orbits Next.UVStress Climb PhysMS PhysMS.Frame
open WilsonThermometerWeakValueRecovery WilsonThermometerWeakCoefficientTail
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U:ℝ→tower S)(H:Leading F U)(simple:G.Simple)(X:Scaling S)(built:Foundation F R)
    {n:ℕ}{d:Caps n}

open WilsonThermometerWeakMeasuredSeries (approximate)
open MeasureTheory
include R H simple X built in
theorem original (v:MaxwellSlots C d)(c:ℕ→Points n→ℂ)(g:ℝ→ℝ)(j p D q:ℕ)(retains:WilsonThermometerWeakSignedJets.high j p≤q)
    (linked:Coupling G g)
    (legal:∀a≤q,ContDiffOn ℝ ∞ (c a) (conf n))
    (posted:WilsonThermometerWeakValueRecovery.Signed trail (conf n)
      (fun r=>measured F none (U r) v r-approximate c q (g r))
      g (WilsonThermometerWeakSignedJets.high j p+1) D):
    ∀L,IsCompact L→L⊆conf n→∀ε:ℝ,0<ε→∀ᶠr in trail,∀x∈L,∀qv:Viewers F,
      ‖iteratedFDeriv ℝ j (measured F qv (U r) v r) x-
        iteratedFDeriv ℝ j (approximate c p (g r)) x‖≤ε*g r^p:=by
  intro L compact inside ε ep
  have e:0<ε/2:=half_pos ep
  have represented:=WilsonThermometerWeakMeasuredSeries.original F R U H simple X built
    v c g j p D q retains (Coupling.conforms simple linked) linked.positive legal posted L compact inside (ε/2) e
  have observers:=Frame.negligible F R U H simple X built j v L compact inside g linked (ε/2) e p
  filter_upwards [represented,observers] with r recv phases x hx qv
  calc _≤‖iteratedFDeriv ℝ j (measured F qv (U r) v r) x-iteratedFDeriv ℝ j (measured F none (U r) v r) x‖+
          ‖iteratedFDeriv ℝ j (measured F none (U r) v r) x-iteratedFDeriv ℝ j (approximate c p (g r)) x‖:=
           norm_sub_le_norm_sub_add_norm_sub ..
       _≤(ε/2)*g r^p+(ε/2)*g r^p:=add_le_add (phases x hx qv none) (recv x hx)
       _=ε*g r^p:=by ring

/-- Restoring the original compact test costs its mass for all perturbative orders. -/
theorem applied {n:ℕ}{Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y]
    (φ:Test n){L:Set (Points n)}(inside:tsupport (φ:Points n→ℂ)⊆L)(H:Points n→Y)
    (b:ℝ)(paid:∀x∈L,‖H x‖≤b):
    ‖∫x,φ x • H x‖ ≤ (∫x,‖φ x‖)*b:=by
  calc _≤∫x,‖φ x • H x‖:=norm_integral_le_integral_norm _
       _≤∫x,‖φ x‖*b:=by
         apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
           ((φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const b)
         apply Filter.Eventually.of_forall
         intro x
         change ‖φ x • H x‖≤‖φ x‖*b
         by_cases hx:x∈L
         · rw [norm_smul];exact mul_le_mul_of_nonneg_left (paid x hx) (norm_nonneg _)
         · have zero:φ x=0:=image_eq_zero_of_notMem_tsupport (fun hy=>hx (inside hy))
           simp [zero]
       _=_:=by rw [integral_mul_const]

end YM.Integration.WilsonThermometerWeakAllViewSeries
end
