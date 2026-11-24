import YM.Integration.WilsonSeparatedPrefixMovingJointRows

/-! Integrate signed genuine older responses with one original spectral salary. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointIntegral
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonSeparatedPrefixMovingCalendar (epoch window)
open WilsonSeparatedPrefixMovingLateLaw (whole)
open WilsonSeparatedPrefixMovingWages (coupon)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonCoeffUV.Cosmos.Polestar
open WilsonIndependentMovingRosterAllFineSeats (Elected Named)
open scoped BigOperators Topology Classical
local notation "C" => Credit.leanC
variable {G:Gauge}{h D k n height seats:ℕ}{H:Hol G}{F:Labels.Frame G h}{T:SectionData F}{p:h<D}


open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointExpansion (angle)
open WilsonSeparatedPrefixMovingBookedMaster (Paid)
open scoped ContDiff
variable {a u e:ℕ}{v:Rails h k (u+a) e}

open MeasureTheory
open scoped SchwartzMap
open WilsonSeparatedPrefixMovingJointExpansion (coefficient)
open WilsonSeparatedPrefixMovingJointSpectrum (physical)
open WilsonSeparatedPrefixMovingJointRows (bill)
def multiplier:ℝ:=1+2*Real.pi*‖physical.symm.toContinuousLinearMap‖
theorem growth (n:ℕ)(ξ:Euclid):(1+‖angle ξ‖)^n ≤ multiplier^n*(1+‖ξ‖^n):=by
  have L:0 ≤ 2*Real.pi*‖physical.symm.toContinuousLinearMap‖:=by positivity
  have M:0 ≤ multiplier:=by unfold multiplier;linarith
  have z:=WilsonSeparatedPrefixMovingJointExpansion.price ξ
  by_cases small:‖ξ‖ ≤ 1
  · have h:1+‖angle ξ‖ ≤ multiplier:=by
      unfold multiplier
      linarith [mul_le_mul_of_nonneg_left small L]
    exact (pow_le_pow_left₀ (by positivity) h _).trans (le_mul_of_one_le_right (pow_nonneg M _) (by linarith [pow_nonneg (norm_nonneg ξ) n]))
  · have h:1+‖angle ξ‖ ≤ multiplier*‖ξ‖:=by unfold multiplier;rw [add_mul,one_mul];linarith
    calc _ ≤ (multiplier*‖ξ‖)^n:=pow_le_pow_left₀ (by positivity) h _
         _=_:=mul_pow ..
         _ ≤ _:=mul_le_mul_of_nonneg_left (by linarith : ‖ξ‖^n ≤ 1+‖ξ‖^n) (pow_nonneg M _)
def signedRow (Y:CutsP H T p v C C C C)(Q:SealR G)(φ:Rarity D)(χ:Rarity Q.D)(X:Q.Rider)(y:ℝ)
    (o:CellR)(older q:ℕ)(legs:Fin 0→YForest G)(S:Euclid→ℂ)(ξ:Euclid):ℝ:=
  ∑c:Bool,∑d:Bool,coefficient (S ξ) c d*WilsonSeparatedPrefixMovingJointRows.page Y Q φ χ X y o older q legs ξ c d
theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (S:𝓢(Euclid,ℂ))(spectrum:∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)):
    ∃M:ℝ,0 ≤ M ∧ ∀(older:ℕ)(_gate:Y.vesselsC.anchor ≤ older)(_route:older ≤ Y.m)(X:Q.Rider)
      (y gap r:ℝ)(o:CellR)(_clear:ClearDay φ χ gap)(_pos:0<gap)
      (_near:φ.radius+|y|+1 ≤ r)(_far:χ.radius+|y|+1 ≤ r)(legs:Fin 0→YForest G)(q:ℕ)(_grade:q ≤ e),
      let row:=signedRow Y Q φ χ X y o older q legs S
      let ratio:=paceT Y.ax.S Y.m Y.ceilC
      let invoice:=bill Y Q C₀ C₁ C₂ φ χ X y gap r older
      (AEStronglyMeasurable row volume → Integrable row) ∧
        ‖∫ξ:Euclid,row ξ‖ ≤ ratio^h*(abs invoice)*(M*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)):=by
  obtain ⟨M,hM,source⟩:=WilsonSeparatedPrefixMovingJointRows.original Y Q C₀ C₁ C₂ paid φ χ hφ hχ
  let n:=D+Q.D
  have mp:0 ≤ multiplier:=by unfold multiplier;positivity
  refine ⟨4*M*multiplier^n,by positivity,?_⟩
  intro older gate route X y gap r o clear pos nr fr legs q grade row ratio invoice
  let wall:=ratio^h*(abs invoice)*(M*multiplier^n)
  let fat:=fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖
  have rp:0 ≤ ratio:=(pace_pos ..).le
  have wp:0 ≤ wall:=by dsimp [wall];positivity
  have one (ξ:Euclid)(i j:Bool):‖coefficient (S ξ) i j*WilsonSeparatedPrefixMovingJointRows.page Y Q φ χ X y o older q legs ξ i j‖ ≤ wall*fat ξ:=by
    rw [norm_mul,Real.norm_eq_abs (coefficient _ _ _)]
    have paidRow:=source older gate route X y gap r o clear pos nr fr legs ξ i j q grade
    calc _  ≤  ‖S ξ‖*(ratio^h*(abs invoice)*(M*(multiplier^n*(1+‖ξ‖^n)))):=by
            apply mul_le_mul (WilsonSeparatedPrefixMovingJointExpansion.coin _ _ _) _ (norm_nonneg _) (norm_nonneg _)
            apply paidRow.trans
            apply mul_le_mul (mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg rp _)) _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left (growth n ξ) hM
         _=wall*fat ξ:=by dsimp [wall,fat];ring
  have bound (ξ:Euclid):‖row ξ‖ ≤ (4*wall)*fat ξ:=by
    change ‖∑i:Bool,∑j:Bool,_‖ ≤ _
    calc _ ≤ ∑i:Bool,∑j:Bool,wall*fat ξ:=(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _=>
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _=>one ξ i j))
         _=_:=by simp only [Fintype.sum_bool];ring
  have major:Integrable (fun ξ:Euclid=>(4*wall)*fat ξ):=(spectrum n).const_mul _
  refine ⟨fun measurable=>major.mono' measurable (ae_of_all _ bound),?_⟩
  apply (norm_integral_le_of_norm_le major (ae_of_all _ bound)).trans_eq
  rw [integral_const_mul]
  dsimp only [wall,fat,n]
  ring
end YM.Integration.WilsonSeparatedPrefixMovingJointIntegral
