import YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedGate
import YM.Integration.WilsonPositionProgramTrialPublicJointFourMixedFitted

/-! The complete measured grade-four field on the booked mixed physical timeline. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedFitted
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS


open WilsonOriginalPublicRelativeGramKineticMesh (thermal)

open RG.Supply Precision Next.Foundations WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Power WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops Labels XSpace Extra.Histories Pert.Asymptotics
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonPositionProgramTrialPublicJointFourMixedFitted (field)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (turned)
open WilsonPositionProgramTrialPublicJointFourSignedFitted (coefficient)
local notation "F₄" => R.family.labels.level 4

omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3) ≤ τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    {cap k u e:ℕ}(fit:4<cap)(rails:Rails 4 k u e)(enough:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>cap) (fun _=>fit))≤k)
    (T₄:SectionData F₄){Hol₀:Hol G}(sound:T₄.Sound Hol₀)(pop:Bid.pop T₄):
    ∃M:ℝ,0≤M ∧ ∀ᶠ r in trail,∀ρ:I→{s:ℝ // 0<s ∧ s<δ},
      (∀i,r ≤ (ρ i).val ∧ (ρ i).val ≤ outer z h r) → (∃i,(ρ i).val=r) →
      let m:=Γ.date r
      let l₀:=univ.sup fun i=>max (books (ρ i)).stock.j (books (ρ i)).W.k
      let f:=berth R 5 l₀
      let K:=berth R τ f
      ∀N per:ℕ,K≤N → ∀q:ℕ,2≤q → q≤e → ∀{n:ℕ}(grade:Fin n→ℕ)(file:Filed R grade K)
        (Y:∀j,R.family.label (grade j))(turn:Fin n→Motion)(rr gain:ℝ),0 < rr → 0 ≤ gain →
        ∀(i:Fin n)(same:grade i=4),
        let b:=field R fit k T₄ m N per grade file Y turn rr gain i same q
        let w:=turned R grade N per file Y turn i same
        let x:=(coefficient R m K N per rr gain:ℂ) • (F₄).core w
        (F₄).coeffSize (b-x)≤M*(wilson z r)^(1/8:ℝ)*(F₄).coeffSize x:=by
  obtain ⟨_,_,gate⟩:=WilsonPositionProgramTrialPublicJointFourBookedGate.original F simple bliss slow Γ D T h τ deep d books
  let B:=2*T+11+2*h+(τ+1)
  obtain ⟨M,M₀,ready⟩:=WilsonPositionProgramTrialPublicJointFourMixedFitted.original R simple v₀ funded
    fit rails enough capacity T₄ sound pop (2*(B:ℝ)+1) (1/8:ℝ) (by positivity) (by norm_num) (by norm_num)
  obtain ⟨j,hj⟩:=eventually_atTop.1 ready
  let heat:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have cold:∀ᶠr in trail,wilson z r≤1:=(heat.conforms simple).eventually_le_const zero_lt_one
  have gp:∀ᶠr in trail,0<wilson z r:=heat.positive
  have rp:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  have fine:∀ᶠr:ℝ in trail,r<a j:=(gt_mem_nhds ((C).S.a_pos j)).filter_mono nhdsWithin_le_nhds
  refine ⟨M*4^(1/8:ℝ),by positivity,?_⟩
  filter_upwards [gate,Γ.upper,fine,cold,gp,rp] with r grid upper later frozen positive real
  have small:(a (Γ.date r))/r≤1:=upper.trans (pow_le_one₀ positive.le frozen)
  have scale:a (Γ.date r)≤r:=by simpa only [one_mul] using (div_le_iff₀ real).1 small
  have entered:j≤Γ.date r:=by
    by_contra! bad
    exact (not_lt_of_ge ((C).S.strictAnti.antitone bad.le)) (scale.trans_lt later)
  intro ρ placed near m l₀ f K N per top q floor depth n grade file Y turn radius s radiusPos salary i same b w x
  let t:=regulatorRun R.family N per m
  obtain ⟨before,hot,smallT,realK,comp,_,thick,thin⟩:=grid ρ placed near N per top
  have thin':a K/a m≤t^(8*(1/8:ℝ)):=by norm_num;exact thin
  have receipt:=hj j le_rfl m K N per entered before top hot smallT realK.ne' thick thin'
    q floor depth grade file Y turn radius s radiusPos salary i same
  have transfer:t^(1/8:ℝ)≤4^(1/8:ℝ)*(wilson z r)^(1/8:ℝ):=by
    rw [←Real.mul_rpow (by norm_num:0≤(4:ℝ)) positive.le]
    exact Real.rpow_le_rpow hot.le comp (by norm_num)
  calc
    _ ≤ M*t^(1/8:ℝ)*(F₄).coeffSize x:=receipt
    _ ≤ (M*(4^(1/8:ℝ)*(wilson z r)^(1/8:ℝ)))*(F₄).coeffSize x:=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left transfer M₀)
        (show 0≤(F₄).coeffSize x from Finset.sum_nonneg (fun j _=>norm_nonneg (x j)))
    _=(M*4^(1/8:ℝ))*(wilson z r)^(1/8:ℝ)*(F₄).coeffSize x:=by ring

end YM.Integration.WilsonPositionProgramTrialPublicJointFourBookedFitted
end
