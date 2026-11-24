import YM.Integration.WilsonMeasuredSignedActionPacket
import YM.Integration.WilsonMeasuredSignedActionBookLimits

/-! Pass the paid mixed physical field to an arbitrary common ordered
pretest limit at its chosen reporting scale. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionBookedReturn
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



open WilsonMeasuredSignedActionPacket (Packet top)
open WilsonMeasuredSignedActionAverage (pool)
open WilsonMeasuredSignedActionCourse (axis)
open WilsonMeasuredSignedActionProjected (posted)
open WilsonPhysicalPositionAdmissible (Native)
open TraceExtension Next.UVStress
abbrev Address:=ℕ×(ℕ×ℕ)

theorem first (L:Filter (ℕ×ℕ)):Tendsto (Prod.fst:Address→ℕ) (atTop.curry L) atTop:=by
  intro a belongs
  exact eventually_curry_iff.mpr ((show ∀ᶠx:ℕ in atTop,x∈a from belongs).mono
    (fun _ seen=>Eventually.of_forall (fun _=>seen)))

omit [DecidableEq I] [Nonempty I] in
theorem after {D T:ℕ}{δ:ℝ}(books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (τ:ℕ)(ρ:I→{s:ℝ // 0<s ∧ s<δ})(i:I):(books (ρ i)).W.k<top F books τ ρ:=by
  let names:=fun j=>max (books (ρ j)).stock.j (books (ρ j)).W.k
  have live:(books (ρ i)).W.k≤names i:=le_max_right _ _
  exact (live.trans (Finset.le_sup (f:=names) (Finset.mem_univ i))).trans_lt
    ((WilsonInvariantActionPosition.arrival R 5 _).1.trans (WilsonInvariantActionPosition.arrival R τ _).1)

set_option maxHeartbeats 500000 in
omit [DecidableEq I] in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    {base:ℕ}(Γ:WilsonViewerReportingGrid.Grid (ℓ:=l) F base (wilson z))
    (D T h τ:ℕ)(deep:2*(2*(2*Γ.stage+2)+3)≤τ)(d:I→Fin (D+1)){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (v₀:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v₀ R.kit)
    {cap k u e:ℕ}(fit:4<cap)(rails:Rails 4 k u e)(enough:4≤k)
    (capacity:capP (deck (G:=G) (fun _:Fin 1=>4) (fun _=>cap) (fun _=>fit))≤k)
    (T₄:SectionData F₄){Hol₀:Hol G}(sound:T₄.Sound Hol₀)(pop:Bid.pop T₄)
    (X:Zoom)(ρ:ℕ→I→{s:ℝ // 0<s ∧ s<δ})
    (placed:∀m i,X.r m≤(ρ m i).val ∧ (ρ m i).val≤outer z h (X.r m))(near:∀m,∃i,(ρ m i).val=X.r m)
    {n:ℕ}{grade:Fin n→ℕ}(E:∀m,Packet R grade (top F books τ (ρ m)))(i:Fin n)(four:grade i=4)
    (q:ℕ)(low:2≤q)(high:q≤e)(unit:Address→ℂ){ω:Filter Address}[NeBot ω](orderly:ω≤atTop.curry order.fuse)
    (enrolled:∀ᶠp:Address in atTop.curry order.fuse,
      ∃s:ℝ,0 ≤ s ∧ (F₄).core (pool F₄ ((E p.1).vote p.2 i four))=(s:ℂ) • axis F₄)
    {v:(F₄).Coeff}(observed:Tendsto (fun p:Address=>(E p.1).measured fit k T₄ (Γ.date (X.r p.1))
      p.2 i four q (unit p)) ω (𝓝 v))
    {A:Module.End ℂ ((Bel (C).book).Field 4)}(native:Native C A)(ident:posted C v=A (stepField C)):
    ∃s:ℝ,0 ≤ s ∧ ∃c:ℂ,A (stepField C)=(s:ℂ) • stepField C+c • (Bel (C).book).unit 4:=by
  obtain ⟨M,nonnegative,meter⟩:=WilsonMeasuredSignedActionPacket.original F simple bliss slow Γ D T h τ deep d books
    v₀ funded fit rails enough capacity T₄ sound pop
  have home:Tendsto X.r atTop trail:=tendsto_nhdsWithin_iff.mpr ⟨X.limits,Eventually.of_forall X.positive⟩
  have locations:Tendsto (fun p:Address=>X.r p.1) ω trail:=(home.comp (first order.fuse)).mono_left orderly
  let heat:=wilson_link F simple bliss.budgets bliss.keen bliss.lies
  have vanishes:Tendsto (fun p:Address=>wilson z (X.r p.1)) ω (𝓝 0):=(heat.conforms simple).comp locations
  have temp:∀ᶠp:Address in ω,0<wilson z (X.r p.1):=locations.eventually heat.positive
  let η:=fun p:Address=>M*(wilson z (X.r p.1))^(1/8:ℝ)
  have continuousPower:Continuous (fun a:ℝ=>a^(1/8:ℝ)):=Real.continuous_rpow_const (by norm_num)
  have rate:Tendsto η ω (𝓝 0):=by
    simpa only [η,Function.comp_apply,Real.zero_rpow (show (1/8:ℝ)≠0 by norm_num),mul_zero] using
      (continuousPower.continuousAt.tendsto.comp vanishes).const_mul M
  have paidCut:∀ᶠp:Address in atTop.curry order.fuse,top F books τ (ρ p.1)≤p.2.1:=by
    apply eventually_curry_iff.mpr
    apply Eventually.of_forall
    intro m
    change ∀ᶠb:ℕ×ℕ in order.fuse,top F books τ (ρ m)≤b.1
    exact (Push.RelayDifference.cutoff_grows order).eventually_ge_atTop (top F books τ (ρ m))
  let raw:Address→(F₄).Coeff:=fun p=>(E p.1).vote p.2 i four
  let value:Address→(F₄).Coeff:=fun p=>(E p.1).measured fit k T₄ (Γ.date (X.r p.1)) p.2 i four q (unit p)
  let scale:=fun p:Address=>(E p.1).scale (Γ.date (X.r p.1)) p.2
  have small:∀ᶠp in ω,0≤η p:=temp.mono (fun p v=>mul_nonneg nonnegative (Real.rpow_nonneg v.le _))
  have paid:∀ᶠp in ω,let x:=(scale p:ℂ) • (F₄).core (raw p)
      (F₄).coeffSize (x-(F₄).core (value p))≤η p*(F₄).coeffSize x:=by
    filter_upwards [locations.eventually meter,paidCut.filter_mono orderly] with p quoted entered
    exact quoted (ρ p.1) (placed p.1) (near p.1) grade (E p.1) p.2 entered q low high i four (unit p)
  exact WilsonMeasuredSignedActionMeasuredLimit.original C (l:=ω) (w:=raw) (b:=value) (a:=scale) (η:=η)
    (y:=v) (T:=A) (Eventually.of_forall (fun p=>(E p.1).scale_nonneg _ _))
    (enrolled.filter_mono orderly) observed rate small paid native ident

end YM.Integration.WilsonMeasuredSignedActionBookedReturn
end
