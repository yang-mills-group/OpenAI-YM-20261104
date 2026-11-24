import YM.Integration.WilsonMovingForkSharpGrades

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkSharpPhysicalRuler
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

open MeasureTheory
open scoped SchwartzMap ContDiff
open WilsonSeparatedPrefixMovingJointSpectrum (Euclid)
open WilsonSeparatedPrefixMovingJointWaves (sheet)
open WilsonSeparatedPrefixMovingJointExpansion (coefficient angle)
open WilsonSeparatedPrefixMovingJointIntegral (signedRow)
open WilsonSeparatedPrefixMovingJointRows (bill)
open WilsonSeparatedPrefixMovingJointAddress (move)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonMovingForkSharpMaster (Paid)
variable {a u e:ℕ}{v:Rails h k (u+a) e}
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonMovingForkSharpProfile (full projected)
open WilsonMovingForkSharpIncome (gain)
open WilsonMovingForkSharpIntegral (chamber)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
open WilsonMovingForkSharpAxisIntegral (fare)
open WilsonMovingForkSharpAxisWave (tested)

open WilsonMovingForkSharpActualGram (Priced)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonMovingForkSharpAxisCash (mass)
open WilsonMovingForkSharpReportClock (atFar)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonMovingForkSharpBudget (allowance Earned)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonMovingForkSharpGrades (row invoice Audited)

theorem rescale (T L size B d:ℝ)(tpos:0<T)(lpos:0<L)(scale:0 ≤ size)(order:0 ≤ d)
    (fit:L/T  ≤  B):T^(-d)*size^d  ≤  L^(-d)*(B*size)^d:=by
  have bp:0 ≤ B:=(div_nonneg lpos.le tpos.le).trans fit
  have inside:size/T  ≤  L⁻¹*(B*size):=by
    calc _=L⁻¹*((L/T)*size):=by field_simp
         _ ≤ _:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right fit scale) (inv_nonneg.mpr lpos.le)
  have rate:=Real.rpow_le_rpow (div_nonneg scale tpos.le) inside order
  rw [Real.div_rpow scale tpos.le,Real.mul_rpow (inv_nonneg.mpr lpos.le) (mul_nonneg bp scale),
    Real.inv_rpow lpos.le] at rate
  simpa only [Real.rpow_neg lpos.le,Real.rpow_neg tpos.le,div_eq_inv_mul] using rate

def Quoted (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)  →  SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(φ:Rarity D)(ψ χ:Rarity Q.D)
    (S:𝓢(Euclid,ℂ))(x:Verse F)(W:ℝ)(L B:ℝ):Prop:=
  ∀(older:ℕ),Y.vesselsC.anchor  ≤  older  →  older  ≤  Y.m  →  ∀(Z:Q.Rider)(y gap r:ℝ)(o:CellR),
  ClearDay φ χ gap  →  0<gap  →  φ.radius+|y|+1  ≤  r  →  χ.radius+|y|+1  ≤  r  →  ∀w:Fin 0  →  YForest G,
  let size:=paceT Y.ax.S m Y.ceilC
  let gross:=invoice Y Q C₀ C₁ C₂ ledger pay thermal u' φ χ S W Z older y gap r
  let f:=row Y m arms α X Q φ ψ χ S x Z older y o w
  (∀q  ≤  e,‖f q‖  ≤  L^(-((h:ℝ)+1/4))*((B*size)^((h:ℝ)+1/4)*gross)) ∧ Heard e h L ((B*size)^h*gross) f

theorem original (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)  →  SealR G)(α:Wilt arms)(X:Herit arms)
    (Q:SealR G)(C₀ C₁ C₂ ledger pay thermal:Credit)(u':ℕ)(φ:Rarity D)(ψ χ:Rarity Q.D)
    (S:𝓢(Euclid,ℂ))(x:Verse F)(W:ℝ)(L B:ℝ)(physical:0<L)(fit:L/paceT Y.ax.S m Y.m  ≤  B)
    (paid:Audited Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x W):
    Quoted Y m arms α X Q C₀ C₁ C₂ ledger pay thermal u' φ ψ χ S x W L B:=by
  intro older gate age Z y gap r o clear positive nr fr w size gross f
  obtain ⟨low,high⟩:=paid older gate age Z y gap r o clear positive nr fr w
  let T':=paceT Y.ax.S m Y.m
  have tp:0<T':=pace_pos ..
  have sp:0<size:=pace_pos ..
  have group0:0< T'^(-((h:ℝ)+1/4))*size^((h:ℝ)+1/4):=mul_pos (Real.rpow_pos_of_pos tp _) (Real.rpow_pos_of_pos sp _)
  have atZero:=low 0 (Nat.zero_le _)
  change ‖f 0‖  ≤  T'^(-((h:ℝ)+1/4))*(size^((h:ℝ)+1/4)*gross) at atZero
  rw [←mul_assoc] at atZero
  have cash:0  ≤  gross:=nonneg_of_mul_nonneg_right ((norm_nonneg _).trans atZero) group0
  have wide:=rescale T' L size B ((h:ℝ)+1/4) tp physical sp.le (by positivity) fit
  have flat:=rescale T' L size B (h:ℝ) tp physical sp.le (Nat.cast_nonneg _) fit
  simp only [Real.rpow_neg tp.le,Real.rpow_neg physical.le,Real.rpow_natCast] at flat
  constructor
  · intro q bound
    have got:=low q bound
    change ‖f q‖  ≤  T'^(-((h:ℝ)+1/4))*(size^((h:ℝ)+1/4)*gross) at got
    rw [←mul_assoc] at got ⊢
    exact got.trans (mul_le_mul_of_nonneg_right wide cash)
  · apply WilsonSeparatedPrefixMovingBeforeRead.heard e h L _ f physical
    intro q bound
    have got:=high.1 q bound
    change ‖f q‖  ≤  (T'^h)⁻¹*(size^h*gross) at got
    rw [←mul_assoc] at got ⊢
    exact got.trans (mul_le_mul_of_nonneg_right flat cash)

end YM.Integration.WilsonMovingForkSharpPhysicalRuler
