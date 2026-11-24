import YM.Integration.WilsonSeparatedPrefixMovingPinned44
import YM.Integration.WilsonSeparatedPrefixMovingPinnedRuler

/-! Both physical scale laws for the single signed reflected upper against its true full fitted Gram. -/
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingPinnedPhysical
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
open WilsonSeparatedPrefixMovingTested44 (inner ranks)
open WilsonSeparatedPrefixMovingRelativeMaster (Landed)
open WilsonCoeffUV.Mer.Patrol (BayV)
open WilsonIndependentExactPlate (Requests)
open WilsonIndependentEvenPassport (old count)
open RegulatorIR RegulatorIR.Ledger
variable {D' j extra:ℕ}
open WilsonMovingForkSharpUniform (Earned)
open WilsonSeparatedPrefixMovingSpectralSalary (salary)
open WilsonSeparatedPrefixMovingPinnedPupil (Clear frontPrice)
open WilsonSeparatedPrefixMovingPinnedRaw (raw)
open WilsonIndependentMovingRosterAllFineRead (Heard)
open WilsonSeparatedPrefixMovingCalendar (epoch)
open WilsonMovingForkSharpBudget (allowance)
open WilsonMovingForkSharpAxisWave (tested)
open WilsonSeparatedPrefixMovingPinned44 (Tariff)
open WilsonSeparatedPrefixMovingPinnedRuler (tab)

theorem original {G:Gauge}{H:Hol G}{D k u a e n:ℕ}{F:Labels.Frame G 4}{T:SectionData F}{p:4<D}{v:Rails 4 k (u+a) e}
    (Y:CutsP H T p v C C C C)(m:ℕ)(arms:Fin (n+1)→SealR G)(Q:SealR G)(α:Wilt arms)(X:Herit arms)
    (C₀ C₁ C₂ first shape chron middle ledger pay thermal:Credit)(u':ℕ)(x:Verse F)
    (Φ:Rarity D)(ψ χ:Rarity Q.D)(hΦ:ContDiff ℝ ∞ Φ.ψ.val)(hψ:ContDiff ℝ ∞ ψ.ψ.val)(hχ:ContDiff ℝ ∞ χ.ψ.val)
    (sold:Tariff Y m arms α X Q C₀ C₁ C₂ first shape chron middle ledger pay thermal 5 u' x Φ ψ χ hΦ hψ hχ)
    (born:Y.ceilC=m)(older:ℕ)(live:Y.vesselsC.anchor ≤ older)(ear:older ≤ Y.m)(Z:Q.Rider)(r δ₀ δ₁ DF:ℝ)(B:Fin (n+1)→ℝ)
    (clear:Clear Y.vesselsC arms Q α ψ older Y.m Y.ceilC m r δ₀ δ₁ DF B)
    (y gap out A L bound:ℝ)(o:CellR)(w:Fin 0→YForest G)
    (amp:Amplitude Φ A)(sep:ClearDay Φ χ gap)(lo:0<gap)(nearBox:Φ.radius+|y|+1 ≤ out)(farBox:χ.radius+|y|+1 ≤ out)
    (reach:1 ≤ L)(bracket:L/paceT Y.ax.S m Y.m ≤ bound):
    let T':=paceT Y.ax.S m Y.m
    let ρ:=L/T'
    let ε:=paceT Y.ax.S Y.m Y.ceilC
    let S:=WilsonSeparatedPrefixMovingJointSpectrum.transformed ψ hψ
    let early:=(5*radiusH Φ ε y)^4*A*frontPrice Y.vesselsC arms Q X Z first shape chron middle 5 older Y.m Y.ceilC m r δ₀ δ₁ DF B
    let near:=|bill Y Q C₀ C₁ C₂ Φ χ Z y gap out older|
    let cohorts:=allowance Y Q Z ledger pay thermal older u' out gap
    let late:=(near+cohorts)*(salary Φ χ hΦ hχ*(∫ξ:Euclid,(1+‖ξ‖^(D+Q.D))*‖S ξ‖))
    let rows:=fun q=>tested Y Q Φ χ Z y o m older q x w S true
    let paid:=tab bound early late
    let scalar:=fun q=>ρ^4*(raw Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N q 0 w-∫ξ:Euclid,rows q ξ)
    (∀q ≤ e,Integrable (rows q))∧Heard e 0 L (L^(-((4:ℝ)+1/4))*paid) scalar ∧
      ∀g:ℝ,0 ≤ g → g ≤ 1 → ∀J:ℕ,
        ‖WilsonSeparatedPrefixMovingHighGrades.above J e g scalar‖ ≤ (e+1:ℕ)*(g^(J+1)*(L^(-(4:ℝ))*paid)):=by
  intro T' ρ ε S early near cohorts late rows paid scalar
  have date:Y.m ≤ m:=born ▸ show Y.m ≤ Y.ceilC from Nat.le_add_right .. 
  have accepted:=sold older live ear Z r δ₀ δ₁ DF B clear y gap out A o w amp sep lo nearBox farBox
  have ratio:paceT Y.ax.S m Y.ceilC=1:=by rw [born];dsimp [paceT];exact div_self (Y.ax.S.a_pos m).ne'
  have fees:Heard e 0 T' ((T'^5)⁻¹*early+T'^(-((4:ℝ)+1/4))*late) (fun q=>
      raw Y.vesselsC arms Q α ψ X Z Φ y o Y.m m Y.ceilC older Y.N q 0 w-∫ξ:Euclid,rows q ξ):=by
    simpa only [T',early,late,near,cohorts,rows,S,ε,ratio,Real.one_rpow,mul_one,Nat.cast_ofNat] using accepted.2
  exact ⟨accepted.1,WilsonSeparatedPrefixMovingPinnedRuler.original e T' L bound early late _ (pace_ge _ date) reach bracket fees⟩
end YM.Integration.WilsonSeparatedPrefixMovingPinnedPhysical
