import YM.Integration.WilsonSeparatedPrefixMovingJointReceipt
import YM.Integration.WilsonSeparatedPrefixMovingJointContinuity

/-! Integrate signed genuine older responses with one original spectral salary. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingJointHighTail
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
open WilsonSeparatedPrefixMovingJointIntegral (signedRow)
theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)
    (C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (S:𝓢(Euclid,ℂ))(spectrum:∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)):
    ∃M:ℝ,0≤M ∧ ∀(older:ℕ)(_gate:Y.vesselsC.anchor≤older)(_route:older≤Y.m)(X:Q.Rider)
      (y gap r:ℝ)(o:CellR)(_clear:ClearDay φ χ gap)(_pos:0<gap)
      (_near:φ.radius+|y|+1≤r)(_far:χ.radius+|y|+1≤r)(legs:Fin 0→YForest G)(J:ℕ)(g:ℝ)(_cap:|g|≤1),
      let ages:=Finset.Ioc J e
      let terms:=fun q=>signedRow Y Q φ χ X y o older q legs S
      let tail:=fun ξ:Euclid=>∑q∈ages,g^q*terms q ξ
      let invoice:=bill Y Q C₀ C₁ C₂ φ χ X y gap r older
      let A:=(paceT Y.ax.S Y.m Y.ceilC)^h * (abs invoice) * (M*∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)
      Integrable tail∧(∫ξ,tail ξ)=∑q∈ages,g^q*(∫ξ,terms q ξ)∧
        ‖∫ξ,tail ξ‖≤(ages.card:ℝ)*|g|^(J+1)*A:=by
  obtain ⟨M,hm,buy⟩:=WilsonSeparatedPrefixMovingJointReceipt.original Y Q ticket C₀ C₁ C₂ paid φ χ hφ hχ S spectrum
  refine ⟨M,hm,?_⟩
  intro older gate route X y gap r o clear gp near far w J g gc ages terms tail invoice A
  have entered (q:ℕ)(hq:q∈ages):Integrable (terms q)∧‖∫ξ,terms q ξ‖≤A:=
    buy older gate route X y gap r o clear gp near far w q (Finset.mem_Ioc.mp hq).2
  have joined (q:ℕ)(hq:q∈ages):Integrable (fun ξ:Euclid=>g^q*terms q ξ):=(entered q hq).1.const_mul _
  have credit (q:ℕ)(hq:q∈ages):‖g^q*∫ξ,terms q ξ‖≤|g|^(J+1)*A:=by
    rw [norm_mul,norm_pow,Real.norm_eq_abs]
    exact mul_le_mul (pow_le_pow_of_le_one (abs_nonneg _) gc (Finset.mem_Ioc.mp hq).1)
      (entered q hq).2 (norm_nonneg _) (pow_nonneg (abs_nonneg _) _)
  have read:(∫ξ,tail ξ)=∑q∈ages,g^q*∫ξ,terms q ξ:=by
    rw [show (∫ξ,tail ξ)=∑q∈ages,∫ξ:Euclid,g^q*terms q ξ from integral_finsetSum _ joined]
    simp only [integral_const_mul]
  refine ⟨integrable_finsetSum _ joined,read,?_⟩
  rw [read]
  calc _ ≤ ∑q∈ages,‖g^q*∫ξ,terms q ξ‖:=norm_sum_le ages _
       _ ≤ ∑q∈ages,|g|^(J+1)*A:=Finset.sum_le_sum credit
       _ = (ages.card:ℝ)*|g|^(J+1)*A:=by simp only [Finset.sum_const,nsmul_eq_mul];ring
end YM.Integration.WilsonSeparatedPrefixMovingJointHighTail
