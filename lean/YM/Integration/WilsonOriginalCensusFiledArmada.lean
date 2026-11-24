import YM.Integration.WilsonOriginalCensusDatedMaterial
import YM.Integration.WilsonIndependentCollarSlateIntensity
import YM.Integration.WilsonOriginalMixedBlockIncome

/-! The original posted row and its authenticated mixed source have the same paid native Armada. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledArmada
open Function Filter Finset Lattice Wilson RG Marker Ac Gauge QuadraticLocal QuadraticLocal.Earn
open Push Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Affinity
open WilsonRootedKioskOccupiedSlip WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet
open WilsonOriginalMixedBlockRows
open scoped Classical BigOperators Topology

open WilsonOriginalCensusDatedMaterial (Material words mounts)
open FundedMarkedPathSelection ActualRunAdmissionScales WilsonOriginalMixedBlockRows
open WilsonRegisteredPairUnaryWallet QuadraticLocal.Earn Org PhysicalNext.Repeat.Legato
variable {G:Gauge}{n N i q:ℕ}{k:Fin n→ℕ}{R:Run G}{σ:ℝ}
  {side:Side}{port:Passport side (Fin n)}{I:Type}[Fintype I]{B:I→Binder port (Stock.census (Fin n))}
  (H:Material R N i q k σ B)
local notation "rows" => fun z:I=>(words H z).rows (WilsonOlderFreshGraphPointWallet.point (B z).center) disk
local notation "cash" => fun z:I=>WilsonIndependentCollarSlateIntensity.amount (words H z) (B z).center

/-- The physical fee uses only its actual mixed native rows at their original rooted distances. -/
def fee (base:Fin n→ℝ):ℝ:=WilsonOriginalMixedBlockIncome.bill B σ (cash) base

theorem original {port':Passport side (Fin n)}{μ:Type}
    (high:μ→Row port' (Stock.census (Fin n)) G (Affinity.Wallet (room (Fin n))))
    (placed:port'=port)(names:μ=((z:I)×(words H z).Roster))(ink:HEq high (mounts H))
    (base:Fin n→ℝ)(positive:∀v,0<base v){order seats shelf:ℕ}
    (through:q ≤ order)(active:1 ≤ seats)(slots:n ≤ seats)(fit:(∑v,k v) ≤ shelf):
    Scene.Armada high base k σ (fee H base) order seats shelf:=by
  subst port'
  subst μ
  cases eq_of_heq ink
  have room₁(z:I):(∑v∈(B z).mode.val,k v)  ≤  ∑v,k v :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _=>Nat.zero_le _
  have offers(z:I):=WilsonGeneralArityCopyAccount.original (words H z) (B z).center H.radius.le
    through active ((room₁ z).trans fit)
  have incomes(z:I):=WilsonIndependentCollarSlateIntensity.original (words H z) (B z).center H.radius.le
    through active ((room₁ z).trans fit)
  exact WilsonOriginalMixedBlockIncome.funded B (rows) (fun z=>(offers z).2.1) k σ (cash) incomes
    base positive (by simpa using slots) fit

omit [Fintype I] in
theorem rebook {K:Material R N i q k σ B}(same:H=K){port':Passport side (Fin n)}{μ:Type}
    (high:μ→Row port' (Stock.census (Fin n)) G (Affinity.Wallet (room (Fin n))))
    (names:μ=((z:I)×(words H z).Roster))(ink:HEq high (mounts H)):
    μ=((z:I)×(words K z).Roster) ∧ HEq high (mounts K):=by
  subst K
  exact ⟨names,ink⟩

end YM.Integration.WilsonOriginalCensusFiledArmada
end
