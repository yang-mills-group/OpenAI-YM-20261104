import YM.Integration.WilsonSeparatedPrefixMovingPinProduct
import YM.Integration.WilsonSeparatedPrefixMovingJointTuition

/-! Exact cell normalization of the signed earlier comparison at the common spatial pin. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonSeparatedPrefixMovingPinCanvas
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingPairSector (current)
open WilsonSeparatedPrefixMovingNativeCut (grades step)
open WilsonIndependentMovingRosterCut (parcel)
open WilsonSeparatedPrefixMovingPinHearing (hear)
open WilsonSeparatedPrefixMovingSummedCenter (issued)
open WilsonSeparatedPrefixMovingPinFlow (packet)
open WilsonPositionProgramPinnedHearthHistory (pin)
open Finset MeasureTheory
open scoped BigOperators Topology Classical

variable {G:Gauge}{D e n:ℕ}{E:Credit}

def total (φ:Rarity D)(ε y:ℝ)(o:CellR)(L:Cover→Lounge):ℝ:=
  ∑s∈canvasM φ ε y,ε^4*∫z:CellR,φ.ψ.val (Mer.address ε y o s z.val)*(L s) z ∂dayMeasure

theorem normalized (φ:Rarity D)(ε y:ℝ)(o:CellR)(L:Cover→Lounge)(h:ℕ)(hp:0<ε):
    total φ ε y o L=ε^h*(∑s∈canvasM φ ε y,drumB h ε*∫z:CellR,
      φ.ψ.val (Mer.address ε y o s z.val)*(L s) z ∂dayMeasure):=by
  simp only [total,Finset.mul_sum,drumB];apply Finset.sum_congr rfl;intro s _
  field_simp [hp.ne']

theorem measured (φ:Rarity D)(ε y:ℝ)(o:CellR)(s:Cover)(L:Lounge):
    Integrable (fun z:CellR=>φ.ψ.val (Mer.address ε y o s z.val)*L z) dayMeasure:=by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  exact ((scribble φ.ψ (Nat.zero_le _) |>.continuous).comp
    ((address_cont ε y s).comp (continuous_const.prodMk continuous_id))).mul L.continuous

theorem difference (φ:Rarity D)(ε y:ℝ)(o:CellR)(L M:Cover→Lounge):
    total φ ε y o L-total φ ε y o M=total φ ε y o (fun s=>L s-M s):=by
  unfold total;rw [←Finset.sum_sub_distrib];apply Finset.sum_congr rfl;intro s _
  rw [←mul_sub,←MeasureTheory.integral_sub (measured φ ε y o s (L s)) (measured φ ε y o s (M s))]
  congr 1;apply integral_congr_ae;exact Filter.Eventually.of_forall (fun _=>(mul_sub ..).symm)

theorem original (φ:Rarity D)(ε y:ℝ)(o:CellR)(A B:ℝ)(pA:Amplitude φ A)(Bpos:0≤B)
    (hp:0<ε)(small:ε≤1)(L M:Cover→Lounge)(book:∀s∈canvasM φ ε y,∀z:CellR,‖(L s) z-(M s) z‖≤B):
    ‖total φ ε y o L-total φ ε y o M‖≤(5*radiusH φ ε y)^4*A*B:=by
  rw [difference];unfold total
  have value (p:Point4):‖φ.ψ.val p‖≤A:=by simpa [crease] using (pA.2 0 (Nat.zero_le D) Fin.elim0 p)
  have house:=census φ ε y hp small
  calc
    _≤∑s∈canvasM φ ε y,‖ε^4*∫z:CellR,φ.ψ.val (Mer.address ε y o s z.val)*((L s-M s) z) ∂dayMeasure‖:=norm_sum_le _ _
    _≤∑_s∈canvasM φ ε y,ε^4*(A*B):=Finset.sum_le_sum fun s hs=>by
      rw [norm_mul,Real.norm_of_nonneg (by positivity :0≤ε^4)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have est:=norm_integral_le_of_norm_le_const (μ:=dayMeasure) (C:=A*B)
        (f:=fun z:CellR=>φ.ψ.val (Mer.address ε y o s z.val)*(L s-M s) z)
        (Filter.Eventually.of_forall fun z=>by rw [norm_mul];exact mul_le_mul (value _) (book s hs z) (norm_nonneg _) pA.1)
      simpa using est
    _= (ε^4*(canvasM φ ε y).card)*(A*B):=by simp;ring
    _≤ _ :=by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right house (mul_nonneg pA.1 Bpos)

end YM.Integration.WilsonSeparatedPrefixMovingPinCanvas
