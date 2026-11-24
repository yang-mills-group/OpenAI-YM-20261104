import YM.Integration.WilsonReceivedCanonicalSocketSelf
import YM.Integration.WilsonCapturedPrimaryWindingVerseDeposit

/-! All ordinary Wick numerators for the authenticated canonical stock on one fixed torus digit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedCanonicalSocketWick
open Function Filter Finset Lattice Wilson Laurent RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open Comparison.RG02 Comparison.RG02.Cumulants Next.SectorChange AllOrder AllOrder.Floe
open PhysicalNext.Repeat.Legato Further.PhysicalPeriodLimitF933 Macrame Shingle
open FVA1Physical.TwoReset WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Embroider WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds WilsonOriginalThermometerPalette
open WilsonReceivedCanonicalSocketRows WilsonReceivedCanonicalSocketFields WilsonReceivedCanonicalSocketSeed
open Pressure Push Push.AbsoluteSums Precision Tree Exterior Bloch PowerSeries
open PhysicalForestMarkedRay FVA1Physical.TwoReset
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative)
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonOriginalThreePurchasedRays (prescribed)

open LocalComparison Comparison.RG02.Cumulants Comparison.RG02.Assembly Order AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank
open WilsonReceivedCanonicalSocketChannels
open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonCoeffUV.Winding WilsonCoeffUV.Power Next.Rank
open FreeResolvent
open WilsonOriginalChargedForestQ WilsonVacuumPreResetFiniteRegister
open WilsonCapturedPrimaryWindingVerseRoster (coefficient)
variable {G:Gauge}(R:Run G)(d:Fin 3→ℕ){h:Fin 3→ℕ}(pt:Fin 3→Chamber)
  (q:(j:Fin 3)→Choice R d j)(N i per:ℕ)(hi:i<N)
  (F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  (x:Affinity.Wallet disks)(a:Fin 3→Lattice.Cover)
local notation "J" => Stock.census (Fin 3)
local notation "K" => model R N i per hi
local notation "S" => step R i per
local notation "f" => fine R i per
local notation "A" => saddle R N i per F
local notation "ρ" => fderiv ℝ ((K).b F) 0
local notation "κ" => (fun j=>contact (h j))
local notation "φ" => relative R N i per hi F (covered R N i per)
local notation "badge" => (fun j:Fin 3=>(J).fire j)
local notation "c" => (fun j:Fin 3=>probe j x)

def inlet (j:Fin 3):Ink ((Active G F)⊕Woods G (coarse R i per)):=
  SignedMeasuredSourceSeries.probe (S) F (A) (ρ)
    (readO (present h) (WilsonReceivedCanonicalVerseRegister.start R d κ pt q a {j}) (f))

local notation "ins" => inlet (h:=h) R d pt q N i per hi F a

def printed (B:fieldDir G (coarse R i per) 1) (r:ℕ):Grade (J) r:=
  WilsonOriginalMixedGaussianTable.stock (J) r (flatten B)
    (fun s:Finset (Fin 3)=>∏j∈s,coefficient (J) badge (c) j)
    (fun s=>Wick (Woods G (coarse R i per)) ((K).covariance F tag) (raiseE (φ)*∏j∈s,(ins) j))

private def exponent (B:fieldDir G (coarse R i per) 1) (r:ℕ)(s:Hot (Board (J) r)):
    Normal.poly (Precision.Key F G):=
  let t:=Join.left s.val
  let grade:=(Join.right s.val).val.card
  MvPolynomial.C (grade.factorial:ℂ)*
    (if t.val.Nonempty then ∑j:Fin 3,if (J).fire j=t then MvPolynomial.C (probe j x)*
        SignedRegisteredMarkedProgram.register F B (coeff grade ((ins) j)) else 0
     else SignedRegisteredMarkedProgram.register F B (coeff grade (φ)))

local notation "ex" => exponent (h:=h) R d pt q N i per hi F x a

private theorem evaluated (B:fieldDir G (coarse R i per) 1)(z:Precision.Key F G→ℝ)(r:ℕ)
    (s:Hot (Board (J) r)):
    Cloud.paint z ((ex) B r s)=WilsonReceivedCanonicalSocketGaussian.value (h:=h) R d pt q N i per hi F x B z
      (fun _:Fin (Pages (f) (f))=>a) r s:=by
  have page:Pages (f) (f)=1:=by simp [Pages]
  simp only [exponent,WilsonReceivedCanonicalSocketGaussian.value,map_mul,MvPolynomial.aeval_C]
  congr 1
  by_cases hs:(Join.left s.val).val.Nonempty
  · simp only [if_pos hs,map_sum,WilsonReceivedCanonicalSocketChannels.seed,Finset.sum_const,nsmul_eq_mul,Finset.card_univ,Fintype.card_fin,page,Nat.cast_one,one_mul]
    apply sum_congr rfl
    intro j _
    split_ifs
    · simp only [map_mul,MvPolynomial.aeval_C]
      rw [SignedRegisteredMarkedProgram.reading]
      rfl
    · exact map_zero _
  · simp only [if_neg hs]

private theorem direction (B:fieldDir G (coarse R i per) 1)(r:ℕ)(z:Precision.Key F G→ℝ)(s:Hot (Board (J) r)):
    Cloud.paint z ((ex) B r s)=WilsonCapturedPrimaryWindingVerseDeposit.entry (J) r (Sum.elim z (flatten B))
      (φ) badge (c) (ins) (Join.left s.val) (Join.right s.val):=by
  unfold exponent WilsonCapturedPrimaryWindingVerseDeposit.entry
  simp only [map_mul,MvPolynomial.aeval_C]
  congr 1
  by_cases hs:(Join.left s.val).val.Nonempty
  · simp only [if_pos hs,map_sum]
    apply sum_congr rfl
    intro j _
    split_ifs
    · simp only [map_mul,MvPolynomial.aeval_C]
      rw [SignedRegisteredMarkedProgram.reading,WilsonOriginalChargedForestQ.same_axes R i per F B z]
      rfl
    · exact map_zero _
  · simp only [if_neg hs]
    rw [SignedRegisteredMarkedProgram.reading,WilsonOriginalChargedForestQ.same_axes R i per F B z];rfl

private theorem centered {T:Type*} [CommRing T](v:PowerSeries T):
    constantCoeff (v-PowerSeries.C (constantCoeff v))=0:=by simp

private theorem flat_constant:constantCoeff (φ)=0:=centered _

private theorem occupied (j:Fin 3):((J).fire j).val.Nonempty:=by simp [Stock.census,Census.fire]

private theorem expanded (B:fieldDir G (coarse R i per) 1)(r:ℕ)(z:Precision.Key F G→ℝ):
    Marker.Poly.pass (lit (Board (J) r) (fun s=>Cloud.paint z ((ex) B r s)))=
      WilsonOriginalMixedGaussianTable.stock (J) r (Sum.elim z (flatten B))
        (fun t:Finset (Fin 3)=>∏j∈t,coefficient (J) badge (c) j)
        (fun t=>raiseE (φ)*∏j∈t,(ins) j):=by
  exact WilsonCapturedPrimaryWindingVerseDeposit.received (J) r (Sum.elim z (flatten B))
    (φ) badge (c) (ins) (fun s=>Cloud.paint z ((ex) B r s)) (flat_constant R N i per hi F)
    occupied (direction (h:=h) R d pt q N i per hi F x a B r z)

private theorem integrated (B:fieldDir G (coarse R i per) 1)(r:ℕ):
    Cloud.prescription ((K).covariance F tag) ((K).symm F tag) 0 ((ex) B r)=
      printed (h:=h) R d pt q N i per hi F tag x a B r:=by
  exact WilsonOriginalMixedGaussianTable.integrated (J) r (flatten B)
    ((K).covariance F tag) ((K).symm F tag) _ _ ((ex) B r)
    (expanded (h:=h) R d pt q N i per hi F x a B r)

theorem original (B:fieldDir G (coarse R i per) 1)(r:ℕ):
    let Z₀:=fun z=>WilsonReceivedCanonicalSocketGaussian.value (h:=h) R d pt q N i per hi F x B z
      (fun _:Fin (Pages (f) (f))=>a) r
    WilsonOriginalGaussianPaidTable.table (Board (J) r) ((K).covariance F tag) Z₀ =
      printed (h:=h) R d pt q N i per hi F tag x a B r:=by
  intro Z₀
  exact (WilsonOriginalGaussianPaidTable.original (Board (J) r) ((K).covariance F tag) Z₀
    ((K).symm F tag) ((K).positive F tag).posSemidef ((ex) B r)
    (fun z s=>evaluated (h:=h) R d pt q N i per hi F x a B z r s)).1.symm.trans
    (integrated (h:=h) R d pt q N i per hi F tag x a B r)

end YM.Integration.WilsonReceivedCanonicalSocketWick
end
