import YM.Integration.WilsonPositionProgramTrialPublicJointFourSignedFitted
import YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedIncome

/-! The relative operator bound on a grade-four slot of the original mixed filing. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedFitted
open Function Filter Finset Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace
open WilsonSurveyedEquationFrameInlet (bank master loan price)
open WilsonIndependentMatchedFiledIncome (plate charge)
open WilsonMarkedIndependentNormalizedElection (deck)
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) (W : Initialize G) {h hi D k u e : ℕ}
local notation "L" => R.family.path.levels
local notation "O" => R.metals.O
local notation "CC" => Credit.leanC


open WilsonIndependentMatchedReportedProxy (sectionSeal)
open WilsonIndependentMatchedFreshWhole (projected)
open WilsonPositionProgramTrialReverseLens (received)
open WilsonPositionProgramTrialFittedLens (matrix)
open WilsonPositionProgramTrialPublicJointCapFiling (sectionAt)
open WilsonSurveyedEquationFrameStability (course)

open WilsonPositionProgramTrialPublicJointCapArrival (high own linear)


open PowerSeries Matrix WilsonCoeffUV.Bank.Carp

open WilsonPositionProgramTrialStationHome (age)
open WilsonPositionProgramTrialAccrued (home)
open WilsonPositionProgramTrialPublicJointGroundBirth (accrued)

open WilsonOriginalPhysicalFruitVerse (written)
open WilsonPositionProgramTrialPublicJointGroundPortfolio (amount)
open WilsonOriginalPublicNodalDeployedVote (vector)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramReportedField (entire)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open PhysicalNext.Repeat.Legato Extra.Histories Pert.Asymptotics

open WilsonPositionProgramTrialPublicJointGroundHead (picked)
open WilsonIndependentMatchedPhysicalPeer (reading)

open WilsonPositionProgramTrialPublicJointFourSignedSource (strip)
open WilsonPositionProgramTrialPublicJointFourSignedWage (fieldSize wage)

open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramTrialPublicJointGroundVoted (bid)
open WilsonPositionProgramTrialPublicJointFourSignedInput (income)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (input turned)
open WilsonPositionProgramTrialPublicJointFourSignedFitted (coefficient)
open WilsonOriginalPublicTrialPhaseFourDictionary (seat Kept)
local notation "F₀" => R.family.labels.level 4

def row (fit:4<D)(k:ℕ)(T:SectionData F₀){n K:ℕ}(m N per:ℕ)(d:Fin n→ℕ)(file:Filed R d K)
    (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r s:ℝ)(i:Fin n)(same:d i=4)(q:ℕ)(p:ℂ →L[ℝ] ℝ)
    (j:(F₀).Index):ℝ:=
  let g:=regulatorRun R.family N per K
  let t:=regulatorRun R.family N per m
  let v:=input R d N per file Y turn i same r s
  reading q t (accrued R fit m K N k (Shrine (plate T fit) (written F₀ (vector F₀ g v) p)) (seat F₀ j).val)

def field (fit:4<D)(k:ℕ)(T:SectionData F₀){n K:ℕ}(m N per:ℕ)(d:Fin n→ℕ)(file:Filed R d K)
    (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r s:ℝ)(i:Fin n)(same:d i=4)(q:ℕ):(F₀).Coeff:=
  let phase:=row R fit k T m N per d file Y turn r s i same q
  WilsonPositionProgramTrialPublicJointFourSignedComplex.field F₀ (phase Complex.reCLM) (phase Complex.imCLM)

theorem original (simple:G.Simple)(v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    (fit:4<D)(rails:Rails 4 k u e)(enough:4 ≤ k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>D) (fun _=>fit)) ≤ k)
    (T:SectionData F₀){H:Hol G}(sound:T.Sound H)(pop:Bid.pop T)
    (width η:ℝ)(wide:0≤width)(gain:0<η)(margin:2*η ≤ 1):
    ∃M:ℝ,0 ≤ M ∧ ∀ᶠ j:ℕ in atTop,∀ m K N per:ℕ,j ≤ m → m ≤ K → K ≤ N →
    let t:=regulatorRun R.family N per m
    let g:=regulatorRun R.family N per K
    0<t → t≤1 → g≠0 → (L).S.a m/(L).S.a K ≤ t^(-width) → (L).S.a K/(L).S.a m ≤ t^(8*η) →
    ∀q:ℕ,2 ≤ q → q ≤ e → ∀{n:ℕ}(d:Fin n→ℕ)(file:Filed R d K)
      (Y:∀i,R.family.label (d i))(turn:Fin n→Motion)(r s:ℝ),0<r → 0 ≤ s → ∀(i:Fin n)(same:d i=4),
      let b:=field R fit k T m N per d file Y turn r s i same q
      let w:=turned R d N per file Y turn i same
      let x:=(coefficient R m K N per r s:ℂ) • (F₀).core w
      (F₀).coeffSize (b-x) ≤ M*t^η*(F₀).coeffSize x:=by
  obtain ⟨M,M₀,hear⟩:=WilsonPositionProgramTrialPublicJointFourSignedCollar.original R simple v₀ funded
    fit rails enough capacity T sound pop width η wide gain margin
  refine ⟨2*(Fintype.card (F₀).Index:ℝ)*M,by positivity,?_⟩
  filter_upwards [hear] with j paid
  intro m K N per late before top t g hot small real thick thin q floor depth n d file Y turn r s radius ss i same b w x
  let v:=input R d N per file Y turn i same r s
  let τ:=(R.family.path.rep N per K).p.threshold
  let α:=income (K:=K) R N per r s
  let β:=coefficient R m K N per r s
  let phase:=row R fit k T m N per d file Y turn r s i same q
  have apos:0≤α:=by dsimp [α,WilsonPositionProgramTrialPublicJointFourSignedInput.income];positivity
  have bpos:0≤β:=by dsimp [β,coefficient];positivity
  have clock:(t/g)^2*(g/τ)^2=(t/τ)^2:=by
    rw [←mul_pow]
    congr 1
    by_cases zeroτ:τ=0
    · simp [zeroτ]
    · field_simp
  have conversion:(t/g)^2*α=β:=calc
    _=(r^4)⁻¹*s*((t/g)^2*(g/τ)^2):=by dsimp [α,WilsonPositionProgramTrialPublicJointFourSignedInput.income,g,τ];ring
    _=β:=by rw [clock];rfl
  have heard (p:ℂ→L[ℝ]ℝ)(z:(F₀).Index)(active:z≠0):
      |phase p z-β*p (w z)|≤β*(M*t^η)*fieldSize w p:=by
    let a:Alma F₀:=(seat F₀ z).val
    have named:sheet F₀ a=z:=rfl
    have nonunit:sheet F₀ a≠0:=named ▸ active
    have cost:=paid m K N per late before top hot small real thick thin q floor depth v p a nonunit
    change |phase p z-(t/g)^2*amount v p a|≤(t/g)^2*M*t^η*fieldSize v p at cost
    have charge:amount v p a=α*p (w z):=WilsonPositionProgramTrialPublicJointFourMixedIncome.active R d N per
      file Y turn i same simple r radius s p a nonunit
    have total:fieldSize v p=α*fieldSize w p:=by
      rw [show fieldSize v p=|α| * fieldSize w p from WilsonPositionProgramTrialPublicJointFourMixedIncome.size
        R d N per file Y turn i same simple r radius s p,abs_of_nonneg apos]
    rw [charge,←mul_assoc,conversion,total] at cost
    calc
      _ ≤ _:=cost
      _=β*(M*t^η)*fieldSize w p:=by rw [←conversion];ring
  have co:=WilsonPositionProgramTrialPublicJointFourSignedComplex.original F₀ simple w (phase Complex.reCLM)
    (phase Complex.imCLM) β (M*t^η) bpos (mul_nonneg M₀ (Real.rpow_nonneg hot.le _)) (heard _) (heard _)
  calc
    _ ≤ _:=co
    _=_:=by ring

end YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedFitted
