import YM.FormalOPE.RG10.StationaryMarks.Rated
/-!
 # polynomial cost schedule for proving gauge-invariance assertions through arbitrary orders
 Needn't assert existence of a convergent/exact smooth param when doing jets.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.StationaryMarks
open Function Filter Topology Set Metric MeasureTheory PertExtension Precision
open BlockGauge Inherit Push.Loops Chart Lattice RG
open YM.PertExtension.Series YM.PertExtension.Series.Tested YM.PertExtension.Series.Radial PowerSeries
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {J:Type}
 def shrink (v: PowerSeries ℝ)(r:ℕ): PowerSeries ℝ:= PowerSeries.mk (fun i=>if i≤r then term v i else 0)
lemma shrink_width (v r): Through r (shrink v r) v:=fun i hi=>by simp [shrink,hi,term]
 def sheet (w:J→ PowerSeries ℝ)(r:ℕ)(t:ℝ)(j:J): ℝ:= peval (term (w j)) r t
lemma photo (w r) (j:J): Tracks (fun t=>sheet w r t j) (shrink (w j) r):= by unfold Tracks shrink; rw [Tracks.asTerm]; exact Aspiration.polynomial (term (w j)) r
lemma Tracks.patch {u v:ℝ→ℝ}{f:PowerSeries ℝ}(T:Tracks u f)(h: u =ᶠ[YM.PertExtension.Series.Tested.germ] v): Tracks v f:= by
 intro n
 obtain ⟨C,hc,H⟩:= T n
 refine ⟨C,hc,?_⟩; filter_upwards [h,H] with t ht he; rw [Pi.sub_apply,← ht]; exact he
lemma Tracks.seam {u v:ℝ→ℝ}{f g:PowerSeries ℝ}(T:Tracks u f)(R:Tracks v g)(h: u =ᶠ[YM.PertExtension.Series.Tested.germ] v): f=g:= by
 apply PowerSeries.ext; exact fun n=> congr_fun ((T.patch h).unique R) n -- existing `WardBin.unique_wilson`? uses `term` Ext.Want `unique` also when literal.G. 
end YM.FormalOPE.RG10.StationaryMarks
