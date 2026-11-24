import YM.Integration.WilsonSeparatedPrefixMovingSpectralSalary
import YM.Integration.WilsonMovingForkSharpGramCap
import YM.Integration.WilsonMovingForkSharpGramLedger

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpGramUniform
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
open WilsonMovingForkSharpMaster (Paid)
open scoped ContDiff
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingJointRows (bill page)
open WilsonMovingForkSharpIncome (gain)
open MeasureTheory
open scoped SchwartzMap
open WilsonSeparatedPrefixMovingJointExpansion (coefficient)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow multiplier growth)
open WilsonMovingForkSharpProjected (amp incoming paired axisRow)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonIndependentMatchedFittedSeat (dose)

open WilsonIndependentMatchedReportedProxy (sectionSeal passport)
open WilsonIndependentMatchedPivotSeat (axis)
open WilsonMovingForkSharpGramBirth (pair)
open WilsonSeparatedPrefixMovingUnformedSector (invoice)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonSeparatedPrefixMovingOwnDate (fee)
open WilsonMovingForkSharpAxisWindow (top wage)
open WilsonMovingForkSharpAxisCash (panel)
open WilsonMovingForkSharpAxisWave (tested)
open WilsonMovingForkSharpAxisCash (mass)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
private theorem support {l:ℕ}(φ:Rarity l)(ℓ:Point4→L[ℝ]ℝ)(c:Bool):
    tsupport (sheet φ ℓ c).ψ.val ⊆ tsupport φ.ψ.val:=by
  apply closure_mono
  intro x hx
  apply left_ne_zero_of_mul (b:=WilsonSeparatedPrefixMovingJointWaves.wave c (ℓ x))
  exact hx

open WilsonMovingForkSharpGramLedger (film)
open WilsonSeparatedPrefixMovingJointIntegral (growth multiplier)
def fare (H:Hol G)(A B:SealR G)(e u target:ℕ)(C₁ C₂:Credit)(X:B.Rider)(Z r gap:ℝ)
    (φ:Rarity A.D)(χ:Rarity B.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)(S:𝓢(Euclid,ℂ)):ℝ:=
  |WilsonMovingForkSharpGramCap.cap H A B e u target C₁ C₂ X Z r gap| * salary φ χ hφ hχ*
    (∫ξ:Euclid,(1+‖ξ‖^(A.D+B.D))*‖S ξ‖)
theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(e u' target:ℕ):
    let toll:=Q.h+h+(u'+target+2)
    ∃C₁ C₂:Credit,∀{a u:ℕ}{v:Rails h k (u+a) e}(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C →
      PassportC H Y.vesselsC Q C C → ∀older:ℕ,Y.vesselsC.anchor ≤ older → older ≤ Y.m →
      ∀(φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
        (X:Q.Rider)(o:CellR)(y gap r:ℝ),0<gap → ClearDay φ χ gap → φ.radius+|y|+1 ≤ r → χ.radius+|y|+1 ≤ r →
      ∀(S:𝓢(Euclid,ℂ)),(∀n:ℕ,Integrable fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖) →
      ∀(j:Alma F)(q:ℕ),q ≤ e → ∀w:Fin 0→YForest G,
        ‖PowerSeries.coeff q (film Y Q φ χ X y o older w S j)‖ ≤
          fare H (sectionSeal T p) Q e u' target C₁ C₂ X (epoch Y.vesselsC older Y.m) r gap φ χ hφ hχ S:=by
  intro toll
  obtain ⟨C₁,C₂,enrolled⟩:=WilsonMovingForkSharpGramCap.original (H:=H) (k:=k) p T Q e u' target
  refine ⟨C₁,C₂,?_⟩
  intro a u v Y spring dorm ticket older gate ear φ χ hφ hχ X o y gap r pos clear nr fr S stock j q hq w
  let A:=WilsonSeparatedPrefixMovingSpectralSalary.wage φ hφ
  let B:=WilsonSeparatedPrefixMovingSpectralSalary.wage χ hχ
  let M:=|WilsonMovingForkSharpGramCap.cap H (sectionSeal T p) Q e u' target C₁ C₂ X (epoch Y.vesselsC older Y.m) r gap|
  let n:=D+Q.D
  let wall:=M*((A*B)*multiplier^n)
  let fat:=fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖
  let sys:=fun ξ c d=>(top Y Q (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y o older j).2 q 0 w
  have near:∀ℓ c,Amplitude (sheet φ ℓ c) (A*(1+‖ℓ‖)^D):=(WilsonSeparatedPrefixMovingJointWaves.original φ hφ).choose_spec.2
  have far:∀ℓ c,Amplitude (sheet χ ℓ c) (B*(1+‖ℓ‖)^Q.D):=(WilsonSeparatedPrefixMovingJointWaves.original χ hχ).choose_spec.2
  have ha:0 ≤ A:=(WilsonSeparatedPrefixMovingJointWaves.original φ hφ).choose_spec.1
  have hb:0 ≤ B:=(WilsonSeparatedPrefixMovingJointWaves.original χ hχ).choose_spec.1
  have hm:0 ≤ M:=abs_nonneg _
  have basis (ξ:Euclid)(c d:Bool): ‖sys ξ c d‖ ≤ M*((A*B)*(1+‖angle ξ‖)^n):=by
    have apart:ClearDay (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) gap:=
      fun l hl j hj=>clear l (support _ _ _ hl) j (support _ _ _ hj)
    have answer:=enrolled Y spring dorm ticket older gate ear (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X o y gap r
      (A*(1+‖angle ξ‖)^D) (B*(1+‖angle ξ‖)^Q.D) pos (near _ _) (far _ _) apart nr fr j q hq w
    refine answer.trans ?_
    rw [show M*((A*B)*(1+‖angle ξ‖)^n)=M*((A*(1+‖angle ξ‖)^D)*(B*(1+‖angle ξ‖)^Q.D)) by
      dsimp only [n];rw [pow_add];ring]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (near (angle ξ) c).1 (far (angle ξ) d).1)
  have one (ξ:Euclid)(c d:Bool):‖coefficient (S ξ) c d*sys ξ c d‖ ≤ wall*fat ξ:=by
    rw [norm_mul]
    calc _ ≤ ‖S ξ‖*(M*((A*B)*(multiplier^n*(1+‖ξ‖^n)))):=by
              apply mul_le_mul (WilsonSeparatedPrefixMovingJointExpansion.coin ..) _ (norm_nonneg _) (norm_nonneg _)
              exact (basis ξ c d).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (growth n ξ) (mul_nonneg ha hb)) hm)
         _=wall*fat ξ:=by dsimp [wall,fat];ring
  have bound (ξ:Euclid):‖WilsonMovingForkSharpGramLedger.page Y Q φ χ X y o older w S j q ξ‖ ≤ (4*wall)*fat ξ:=by
    calc _ ≤ ∑c:Bool,∑d:Bool,wall*fat ξ:=(norm_sum_le _ _).trans (Finset.sum_le_sum fun c _=>
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _=>one ξ c d))
         _=_:=by simp only [Fintype.sum_bool];ring
  have major:Integrable (fun ξ:Euclid=>(4*wall)*fat ξ):=(stock n).const_mul _
  simp only [film,PowerSeries.coeff_mk]
  apply (norm_integral_le_of_norm_le major (ae_of_all _ bound)).trans_eq
  rw [integral_const_mul]
  dsimp only [wall,fat,n,M,A,B,salary,fare,sectionSeal]
  ring
end YM.Integration.WilsonMovingForkSharpGramUniform
