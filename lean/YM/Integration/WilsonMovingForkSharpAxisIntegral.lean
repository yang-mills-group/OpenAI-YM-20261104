import YM.Integration.WilsonMovingForkSharpAxisWave
import YM.Integration.WilsonMovingForkSharpSalary

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpAxisIntegral
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

def fare (Y:CutsP H T p v C C C C)(Q:SealR G)(X:Q.Rider)(C₁:Credit)(m older q u' z:ℕ)
    (r gap:ℝ)(x:Verse F):ℝ:=
  |mass (fun j=>clock Y.ax Y.tx Y.N Y.m older (atFar Y m x j)) q*
     (2*(WilsonMovingForkSharpAxisWindow.wage (h:=h) Q X e u' z r gap 1 1*
         (paceT Y.ax.S Y.m Y.ceilC)^z)*C₁.buy (epoch Y.vesselsC older Y.ceilC))|

theorem original (p:h<D)(T:SectionData F)(Q:SealR G)(e u' z:ℕ):
    let toll:=Q.h+h+(u'+z+2)
    ∃C₁:Credit,∀{a u:ℕ}{v:Rails h k (u+a) e}(Y:CutsP H T p v C C C C),
      SpringD Y.vesselsC (h+Q.h) u' toll C → Dormitory Y.vesselsC (h+Q.h) u' C →
      PassportC H Y.vesselsC Q C C →
      ∀(m older:ℕ),Y.vesselsC.anchor ≤ older → older ≤ Y.m →
      ∀(φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
       (S:𝓢(Euclid,ℂ)),(∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)) →
      ∀(X:Q.Rider)(o:CellR)(y gap r:ℝ),0<gap → ClearDay φ χ gap →
      φ.radius+|y|+1 ≤ r → χ.radius+|y|+1 ≤ r → ∀(x:Verse F)(q:ℕ),q ≤ e → ∀w:Fin 0→YForest G,
        let rows:=tested Y Q φ χ X y o m older q x w S
        Integrable (rows true-rows false) ∧
          ‖∫ξ:Euclid,(rows true ξ-rows false ξ)‖ ≤
            fare Y Q X C₁ m older q u' z r gap x*salary φ χ hφ hχ*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖):=by
  intro toll
  obtain ⟨C₁,payment⟩:=WilsonMovingForkSharpAxisCash.original (H:=H) (k:=k) p T Q e u' z
  refine ⟨C₁,?_⟩
  intro a u v Y spring dorm ticket m older gate route φ χ hφ hχ S spectrum X o y gap r pos clear nr fr x q grade w rows
  let A:=WilsonSeparatedPrefixMovingSpectralSalary.wage φ hφ
  let B:=WilsonSeparatedPrefixMovingSpectralSalary.wage χ hχ
  let n:=D+Q.D
  let M:=fare Y Q X C₁ m older q u' z r gap x
  let wall:=M*(A*B)*multiplier^n
  let fat:=fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖
  have near:∀ℓ c,Amplitude (sheet φ ℓ c) (A*(1+‖ℓ‖)^D):=(WilsonSeparatedPrefixMovingJointWaves.original φ hφ).choose_spec.2
  have far:∀ℓ c,Amplitude (sheet χ ℓ c) (B*(1+‖ℓ‖)^Q.D):=(WilsonSeparatedPrefixMovingJointWaves.original χ hχ).choose_spec.2
  have ha:0≤A:=(WilsonSeparatedPrefixMovingJointWaves.original φ hφ).choose_spec.1
  have hb:0≤B:=(WilsonSeparatedPrefixMovingJointWaves.original χ hχ).choose_spec.1
  have hm:0≤M:=abs_nonneg _
  let sys:=fun ξ c d flag=>panel Y Q (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y o m older q x w flag
  have each (ξ:Euclid)(c d:Bool): ‖sys ξ c d true-sys ξ c d false‖≤M*((A*B)*(1+‖angle ξ‖)^n):=by
    have apart:ClearDay (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) gap:=
      fun l hl j hj=>clear l (support _ _ _ hl) j (support _ _ _ hj)
    let J:=mass (fun j=>clock Y.ax Y.tx Y.N Y.m older (atFar Y m x j)) q
    let P:=J*(2*(WilsonMovingForkSharpAxisWindow.wage (h:=h) Q X e u' z r gap 1 1*
         (paceT Y.ax.S Y.m Y.ceilC)^z)*C₁.buy (epoch Y.vesselsC older Y.ceilC))
    have invoice:=payment Y spring dorm ticket m older gate route (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X o
      y gap r (A*(1+‖angle ξ‖)^D) (B*(1+‖angle ξ‖)^Q.D) pos (near _ _) (far _ _) apart nr fr x q grade w
    calc _ ≤ _:=invoice
         _=P*((A*B)*(1+‖angle ξ‖)^n):=by dsimp only [P,J,WilsonMovingForkSharpAxisWindow.wage,n];rw [pow_add];ring
         _≤_:=mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
  have one (ξ:Euclid)(c d:Bool):‖coefficient (S ξ) c d*(sys ξ c d true-sys ξ c d false)‖≤wall*fat ξ:=by
    rw [norm_mul]
    calc _ ≤ ‖S ξ‖*(M*((A*B)*(multiplier^n*(1+‖ξ‖^n)))):=by
              apply mul_le_mul (WilsonSeparatedPrefixMovingJointExpansion.coin ..) _ (norm_nonneg _) (norm_nonneg _)
              exact (each ξ c d).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (growth n ξ) (mul_nonneg ha hb)) hm)
         _=wall*fat ξ:=by dsimp [wall,fat];ring
  have balance (ξ:Euclid):rows true ξ-rows false ξ=
      ∑c:Bool,∑d:Bool,coefficient (S ξ) c d*(sys ξ c d true-sys ξ c d false):=by
    simp only [mul_sub,Finset.sum_sub_distrib]
    rfl
  have bound (ξ:Euclid):‖rows true ξ-rows false ξ‖≤(4*wall)*fat ξ:=by
    rw [balance]
    calc _≤∑c:Bool,∑d:Bool,wall*fat ξ:=(norm_sum_le _ _).trans (Finset.sum_le_sum fun c _=>
              (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _=>one ξ c d))
         _=_:=by simp only [Fintype.sum_bool];ring
  have major:Integrable (fun ξ:Euclid=>(4*wall)*fat ξ):=(spectrum n).const_mul _
  have seen:=WilsonMovingForkSharpAxisWave.original Y Q ticket φ χ hφ hχ X y o m older q route x w S
  refine ⟨major.mono' ((seen true).sub (seen false)).aestronglyMeasurable (ae_of_all _ bound),?_⟩
  apply (norm_integral_le_of_norm_le major (ae_of_all _ bound)).trans_eq
  rw [integral_const_mul]
  dsimp only [wall,fat,n,M,A,B,salary]
  ring
end YM.Integration.WilsonMovingForkSharpAxisIntegral
