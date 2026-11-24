import YM.Integration.WilsonSeparatedPrefixMovingJointHighTail
import YM.Integration.WilsonSeparatedPrefixMovingJointContinuity

/-! Integrate signed genuine older responses with one original spectral salary. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingSpectralSalary
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

open WilsonSeparatedPrefixMovingJointIntegral (growth multiplier)
open WilsonSeparatedPrefixMovingJointRows (page)
def wage {l:ℕ}(φ:Rarity l)(regular:ContDiff ℝ ∞ φ.ψ.val):ℝ:=(WilsonSeparatedPrefixMovingJointWaves.original φ regular).choose
def salary {l:ℕ}(φ:Rarity D)(χ:Rarity l)(sm:ContDiff ℝ ∞ φ.ψ.val)(hm:ContDiff ℝ ∞ χ.ψ.val):ℝ:=
  4*(wage φ sm*wage χ hm)*multiplier^(D+l)
theorem positive {l:ℕ}(φ:Rarity D)(χ:Rarity l)(sm:ContDiff ℝ ∞ φ.ψ.val)(hm:ContDiff ℝ ∞ χ.ψ.val):0 ≤ salary φ χ sm hm:=by
  have a:0≤wage φ sm:=(WilsonSeparatedPrefixMovingJointWaves.original φ sm).choose_spec.1
  have b:0≤wage χ hm:=(WilsonSeparatedPrefixMovingJointWaves.original χ hm).choose_spec.1
  have mult:0 ≤ multiplier:=by unfold multiplier;positivity
  unfold salary
  positivity
private theorem support {l:ℕ}(φ:Rarity l)(ℓ:Point4→L[ℝ]ℝ)(c:Bool):
    tsupport (sheet φ ℓ c).ψ.val ⊆ tsupport φ.ψ.val:=by
  apply closure_mono
  intro x hx
  apply left_ne_zero_of_mul (b:=WilsonSeparatedPrefixMovingJointWaves.wave c (ℓ x))
  exact hx
private theorem rows (Y:CutsP H T p v C C C C)(Q:SealR G)(C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val):
    ∀(older:ℕ)(_gate:Y.vesselsC.anchor≤older)(_route:older≤Y.m)(X:Q.Rider)
      (y gap r:ℝ)(o:CellR)(_clear:ClearDay φ χ gap)(_pos:0<gap)
      (_near:φ.radius+|y|+1≤r)(_far:χ.radius+|y|+1≤r)(legs:Fin 0→YForest G)(ξ:Euclid)(c d:Bool)
      (q:ℕ)(_grade:q≤e),
      ‖page Y Q φ χ X y o older q legs ξ c d‖≤(paceT Y.ax.S Y.m Y.ceilC)^h*
        bill Y Q C₀ C₁ C₂ φ χ X y gap r older *((wage φ hφ*wage χ hχ)*(1+‖angle ξ‖)^(D+Q.D)):=by
  let A:=wage φ hφ
  let B:=wage χ hχ
  have near:∀ ℓ c,Amplitude (sheet φ ℓ c) (A*(1+‖ℓ‖)^D):=(WilsonSeparatedPrefixMovingJointWaves.original φ hφ).choose_spec.2
  have far:∀ ℓ c,Amplitude (sheet χ ℓ c) (B*(1+‖ℓ‖)^Q.D):=(WilsonSeparatedPrefixMovingJointWaves.original χ hχ).choose_spec.2
  intro older gate route X y gap r o clear pos nr fr legs ξ c d q grade
  have apart:ClearDay (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) gap:=
    fun x hx z hz=>clear x (support _ _ _ hx) z (support _ _ _ hz)
  have line:=(paid older gate route (sheet φ (angle ξ) c) (sheet χ (angle ξ) d) X y gap r
    (A*(1+‖angle ξ‖)^D) (B*(1+‖angle ξ‖)^Q.D) o (near _ _) (far _ _) apart pos nr fr legs).1 q grade
  apply line.trans_eq
  dsimp only [bill,BasePrice,radiusH,WilsonSeparatedPrefixMovingJointWaves.sheet,coupon]
  rw [pow_add]
  dsimp only [A,B]
  ring
theorem received (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)(C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (S:𝓢(Euclid,ℂ))(spectrum:∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)):
    ∀(older:ℕ)(_gate:Y.vesselsC.anchor ≤ older)(_route:older ≤ Y.m)(X:Q.Rider)
      (y gap r:ℝ)(o:CellR)(_clear:ClearDay φ χ gap)(_pos:0<gap)
      (_near:φ.radius+|y|+1 ≤ r)(_far:χ.radius+|y|+1 ≤ r)(legs:Fin 0→YForest G)(q:ℕ)(_grade:q ≤ e),
      let row:=signedRow Y Q φ χ X y o older q legs S
      let ratio:=paceT Y.ax.S Y.m Y.ceilC
      let invoice:=bill Y Q C₀ C₁ C₂ φ χ X y gap r older
      Integrable row ∧
        ‖∫ξ:Euclid,row ξ‖ ≤ ratio^h*(abs invoice)*(salary φ χ hφ hχ*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)):=by
  let M:=wage φ hφ*wage χ hχ
  have hM:0≤M:=mul_nonneg (WilsonSeparatedPrefixMovingJointWaves.original φ hφ).choose_spec.1
    (WilsonSeparatedPrefixMovingJointWaves.original χ hχ).choose_spec.1
  have source:=rows Y Q C₀ C₁ C₂ paid φ χ hφ hχ
  let n:=D+Q.D
  have mp:0 ≤ multiplier:=by unfold multiplier;positivity
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
  refine ⟨major.mono' (WilsonSeparatedPrefixMovingJointReceipt.measured Y Q ticket φ χ hφ hχ X y o older route q legs S).aestronglyMeasurable (ae_of_all _ bound),?_⟩
  apply (norm_integral_le_of_norm_le major (ae_of_all _ bound)).trans_eq
  rw [integral_const_mul]
  dsimp only [wall,fat,n,M,salary]
  ring
theorem original (Y:CutsP H T p v C C C C)(Q:SealR G)(ticket:PassportC H Y.vesselsC Q C C)
    (C₀ C₁ C₂:Credit)(paid:Paid Y Q C₀ C₁ C₂)
    (φ:Rarity D)(χ:Rarity Q.D)(hφ:ContDiff ℝ ∞ φ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (S:𝓢(Euclid,ℂ))(spectrum:∀n:ℕ,Integrable (fun ξ:Euclid=>(1+‖ξ‖^n)*‖S ξ‖)):
    ∀(older:ℕ)(_gate:Y.vesselsC.anchor≤older)(_route:older≤Y.m)(X:Q.Rider)
      (y gap r:ℝ)(o:CellR)(_clear:ClearDay φ χ gap)(_pos:0<gap)
      (_near:φ.radius+|y|+1≤r)(_far:χ.radius+|y|+1≤r)(legs:Fin 0→YForest G)(J:ℕ)(g:ℝ)(_cap:|g|≤1),
      let ages:=Finset.Ioc J e
      let terms:=fun q=>signedRow Y Q φ χ X y o older q legs S
      let tail:=fun ξ:Euclid=>∑q∈ages,g^q*terms q ξ
      let invoice:=bill Y Q C₀ C₁ C₂ φ χ X y gap r older
      let A:=(paceT Y.ax.S Y.m Y.ceilC)^h * (abs invoice) * (salary φ χ hφ hχ*∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖)
      Integrable tail∧(∫ξ,tail ξ)=∑q∈ages,g^q*(∫ξ,terms q ξ)∧
        ‖∫ξ,tail ξ‖≤(ages.card:ℝ)*|g|^(J+1)*A:=by
  have buy:=received Y Q ticket C₀ C₁ C₂ paid φ χ hφ hχ S spectrum
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
end YM.Integration.WilsonSeparatedPrefixMovingSpectralSalary
