import YM.Integration.WilsonOriginalAlternativeTrialNet
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAddressedCommonTrialWeights
open Filter Set Finset Wilson Lattice RG Tree Marker Ac QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open FVA1 OriginalForcedAddresses WilsonThermometerCourseIntake
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure Extraction Source ConnectedActivityE6
open WilsonOriginalReceivedChain WilsonReceivedCloseHistory
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonThermometerCourseHearing WilsonSeparatedOriginalThermometerCells
open WilsonOriginalThermometerFineHarvest WilsonOriginalThermometerFineCover WilsonOriginalThermometerFiledCells
open scoped BigOperators Topology ContDiff

variable {V:Type} [Fintype V] [DecidableEq V]
variable {G:Gauge} (R : Run G)
variable (d:V → ℕ) {m b per k : ℕ} (label:∀j,R.family.book.Ref (d j))
    (hk : Burn.horizon k+2   ≤   R.alloy.B.a.clock.J m)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q : D.Tab R.rolls)
    (π : ℕ  →  Layout G) (Γ : ℕ  →  Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
    {φ : ℕ  →  ℕ} (books : Mentor.Offices.Books D R.rolls Q φ)
    (ahead : Mentor.Forecast D R.rolls Q φ books)
    (order shelf seats : ℕ) (mb : m   ≤   b) (o : Positions (V) (R.family.side (b+1) per))

variable (P₀ : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats b mb (WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin))
    {i : ℕ} {floor : m   ≤   i}
    {y : Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))  →  Config G (R.family.side (i+1) per)  →  Poly (Stock.census (V))}
    {P : WilsonOriginalReceivedChain.Post (N:=b+1) R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d
      order shelf seats i floor y}
    (chain : Trail R hk D Q π Γ Ψ books ahead (WilsonOriginalAlternativeFiniteSource.disks (V:=V)) (WilsonOriginalAlternativeFiniteSource.sectors (V:=V)) d order shelf seats mb (WilsonOriginalAlternativeFiniteSource.offer R d (b+1) per label o.origin) P₀ i floor y P)


open WilsonOriginalAlternativeNames WilsonOriginalAlternativePurse WilsonOriginalAlternativeExtraction
open WilsonOriginalAlternativePost WilsonOriginalAlternativeHearing
open WilsonPositionThermometerGradedReading
open scoped Classical
local notation "J_" => Stock.census (V)
local notation "W_" => Ψ (i+1)
local notation "weights_" => wallet J_ P.w

open MergeProof.Accent
local notation "fired_" => (WilsonOriginalAlternativeFiniteSource.fired (V:=V))
open WilsonOriginalAlternativeTelescope


theorem scalar {N p j e:ℕ}(high:j ≤ N)(ear:e ≤ j)(X:Config G (R.family.side j p) → ℂ)(c:ℂ)
    (U:Config G (R.family.side e p)):
    actualTransport R.family (N:=N) (fun W=>c*X W) ear U=c*actualTransport R.family (N:=N) X ear U:=by
  induction ear using Nat.decreasingInduction with
  | self=>rw [actualTransport_base R.family R.makes high,actualTransport_base R.family R.makes high]
  | of_succ h step ih=>
    rw [actualTransport_step R.family R.makes high _ step,actualTransport_step R.family R.makes high _ step]
    rw [show actualTransport R.family (N:=N) (fun W=>c*X W) step=(fun Y=>c*actualTransport R.family (N:=N) X step Y) from funext ih]
    exact actualAverage_complex_mul R.family _ c U

omit [Fintype V] [DecidableEq V] in
theorem roster {N p j e:ℕ}(high:j ≤ N)(ear:e ≤ j)(s:Finset V)(θ:V → ℂ)
    (X:V → Config G (R.family.side j p) → ℂ)(U:Config G (R.family.side e p)):
    actualTransport R.family (N:=N) (fun W=>∏a∈s,θ a*X a W) ear U=
      (∏a∈s,θ a)*actualTransport R.family (N:=N) (fun W=>∏a∈s,X a W) ear U:=by
  simp_rw [Finset.prod_mul_distrib]
  exact scalar R high ear _ _ U

/-- Each proper face weights the old and the aligned trial fields once on the
    same normalized older Wilson kernel, including all previous joint terms. -/
theorem original (high:i+1 ≤ b+1)(v:∀a:V,R.family.label (d a))(z:V → ℂ)
    (issued:WilsonOriginalAlternativeTrialNet.Receipt R d label hk D Q π Γ Ψ books ahead order shelf seats o (P:=P) v z)
    (f:ℕ)(lower:f ≤ i+1)(U:Config G (R.family.side f per))(s:(J_).Mode)(θ:V → ℂ):
    let F:=fun (x:Wallet (WilsonOriginalAlternativeFiniteSource.disks (V:=V))) (Y:Config G (R.family.side (i+1) per)) (a:V)=>
      (x a).val*WilsonOriginalAlternativeTrialSource.arm R d (b+1) per (i+1) P.passport.origin v z a Y
    let weights:=∏a∈s.val,θ a
    let old:=fun (a:V) (Y:Config G (R.family.side (b+1) per))=>R.family.O (b+1) per (label a) (o.origin a) Y
    let trial:=fun a Y=>F fired_ Y a
    let D:=charge R.family (N:=b+1) J_ y F fired_ s lower U
    let diff:=actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,θ a*old a Y) (lower.trans high) U-
      actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,θ a*trial a Y) lower U
    (∀l:List V,l.toFinset=s.val  →  l.Nodup  →  diff=weights*tally D l) ∧
    (∀fee:V → ℝ,(∀j∈s.val,∀X:Finset V,X⊆s.val  →  j∉X  →  ‖D j X‖ ≤ fee j)  → 
      ‖diff‖ ≤ (∏a∈s.val,‖θ a‖)*(∑j∈s.val,fee j)):=by
  rcases issued with ⟨μ,Z,_,_,_,_,heard⟩
  obtain ⟨before,exactLaw,bound⟩:=heard f lower U s
  intro F weights old trial D diff
  let unscaled:=actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,old a Y) before U-
    actualTransport R.family (N:=b+1) (fun Y=>∏a∈s.val,trial a Y) lower U
  have scaled:diff=weights*unscaled:=by
    unfold diff weights unscaled
    rw [roster R (le_refl (b+1)) (lower.trans high) s.val θ old U,roster R high lower s.val θ trial U,mul_sub]
  constructor
  · intro l face once
    exact scaled.trans (congrArg (weights*·) (exactLaw l face once))
  · intro fee payment
    rw [scaled,norm_mul,show ‖weights‖=∏a∈s.val,‖θ a‖ by simp [weights,norm_prod]]
    exact mul_le_mul_of_nonneg_left (bound fee payment) (Finset.prod_nonneg (fun j _=>norm_nonneg (θ j)))

end YM.Integration.WilsonAddressedCommonTrialWeights
end
