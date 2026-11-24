import YM.FVA2.OffsetClock
/-!
# Independent of raw tags: normalization and likelihood restored
Also compatibility through order.Here full-torus ledger.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.CityHistory
open Function Filter Set Topology MeasureTheory Lattice Gauge RG _root_.YM.Wilson
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested PertExtension.Series.Radial
open FormalOPE.RG10 FormalOPE.RG10.Inherit FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp FormalOPE.RG10.MarkovChain.Router FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Stack FormalOPE.RG10.MultiGauge.Splice
open Precision GaussianScore RGComparison.Core16 RGComparison.Core16.Descent Tree Exterior Push.BetaTransport Tandem Luggage Legacy
open MeasureTheory.Measure (IsAddHaarMeasure)
open PowerSeries
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c f n:Side}
variable (Z:ChartRatio G)(hz:LocalRatio Z)
variable (d:Descent n c)(t u:d.Tags)(b:ℕ→ℝ)(z:ℕ→PowerSeries ℝ)
variable (h:d.OK G)(H:d.Room G)
local notation "κ"=> Legacy.κ d G
include h
lemma contour : jointV d (G:=G) t= jointV d u:= by
   apply Luggage.only_P; apply Quadratic.records; intro x; have he:= GermLaplace.equal_jet (climate d t h 1 u); have ht := congr_fun (congr_fun he (2:ℕ)) x; rw [← progress, ← progress] at ht; linarith
lemma warden : supplyZ d Z t z= supplyZ d Z u z:= by
    induction d generalizing z with
    | nil=> rw [supplyZ,supplyZ]
    | push S T d ih=> rw [supplyZ,supplyZ, ih t.2 u.2 (parentZ z) h.2]; simp_rw [chargeStep,chip,pay,advancing, ExactTower.rise_local (tax_same S T u.1 h.1 t.1) ]

omit h
include H
-- future and W.Health
lemma pure_t : retained d t H= retained d u H:= by unfold retained; congr 1; exact contour d t u (room_ok _ H)
lemma sameFieldDen : μLedger d Z t H z= μLedger d Z u H z:= by unfold μLedger; rw [ warden Z d t u z (room_ok _ H) ]; congr 2; exact contour d t u (room_ok _ H)
lemma sameFieldOut (v:κ): premiere d Z t H z v= premiere d Z u H z v:= by unfold premiere; rw [ warden Z d t u z (room_ok _ H) ]; congr 1; exact contour d t u (room_ok _ H)

-- Projective facts. no uniform cost in n. We never silently change z after increasing order.
omit H
section Th
variable {E F:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]{j:ℕ} {w w':PowerSeries ℝ}
lemma follows (p:E→ℝ)(h:Through (j+1) w w') : Through j (chip w p) (chip w' p) := by
     have ht: Through j (StationaryMarks.Tracks.shadow w) (StationaryMarks.Tracks.shadow w'):= by intro i hi; simp only [StationaryMarks.Tracks.shadow, map_neg,StationaryMarks.Tracks.deduct,coeff_mk,term]; rw [h _ (by omega)]
     have he: term w 0=term w' 0:= h 0 (Nat.zero_le _)
     have hv: Through j ( pay w p ) (pay w' p):= by unfold pay; rw [he]; exact (Through.refl _).add ((show Through j (Stack.carry (E:=E) _) (Stack.carry (E:=E) _) from (fun i hi=> by rw [carry,coeff_map,coeff_map,ht i hi])).mul (Through.refl _)) -- implicit placeholder w etc
     intro i hi; unfold chip exponential; rw [coeff_mk,coeff_mk,map_sum,map_sum]; exact Finset.sum_congr rfl (fun k _=> ( (Through.refl _).mul (hv.pow k) ) i hi)
lemma fundedThrough (t:d.Tags){z z':ℕ→PowerSeries ℝ}(he:∀ i, Through (j+1) (z i) (z' i)): Through j (supplyZ d Z t z) (supplyZ d Z t z'):= by
    induction d generalizing z z' with
    | nil=> rw [supplyZ,supplyZ]; apply Shipment.boost_through; exact follows _ (he 0)
    | push S T d ih=> rw [supplyZ,supplyZ]; apply Through.mul (Shipment.boost_through _ (ih t.2 (z:=parentZ z) (z':=parentZ z') (fun i=> he (i+1)))) (Shipment.boost_through _ ((Through.refl _).mul ( follows _ (he 1))))
include hz H
lemma enough (t:d.Tags){z z':ℕ→PowerSeries ℝ}(he:∀ i,Through (j+1) (z i) (z' i)){A B:κ}(h:Through j A B): Through j (premiere d Z t H z A) (premiere d Z t H z' B):= by
    have hx:=fundedThrough Z d t he; unfold premiere Quadratic.fit; exact Through.mul ( keepsThrough _ ( Through.mul hx h ) ) (Through.invAlready (keepsThrough _ hx) (spend_it (Quadratic.upright (jointV d t) _ _ (clearZ _ Z _ _ hz))) ( spend_it (Quadratic.upright (jointV d t) _ _ (clearZ _ Z _ _ hz)) ))
end Th
end YM.FVA2.CityHistory
