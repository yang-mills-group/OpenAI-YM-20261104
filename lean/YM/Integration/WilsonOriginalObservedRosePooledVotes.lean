import YM.Integration.WilsonOriginalObservedRosePooledFilms
import YM.Integration.WilsonOriginalObservedRosePooledPurse
import YM.Integration.WilsonOriginalObservedRosePublicCurrency

/-! Sector-wise budgets on the actual pooled filed directions, including their original deposited terminal mass. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRosePooledVotes
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
  {n:ℕ}[Nonempty (Fin n)]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicHeard (Heard)
open WilsonThermometerUnitFilingFourPoolClock (outer longer)
open WilsonInvariantActionPosition (berth)
open PhysMS
open MS MS.Land FVA2 FVA2.Register


open WilsonOriginalTwoFlatPublicNamedFare (chosen)
open WilsonThermometerUnitFilingFourSquare WilsonThermometerUnitFilingCoarse
variable (Jr:ℝ→tower S)(Z:WilsonPrescription G)


open WilsonMovingForkSlotDate (slot)
open WilsonMovingForkOpticalBook (reporter)
open WilsonPositionHomogeneousFrame (homogeneous)
open WilsonOriginalObservedRosePooledWrap (allowance)
open WilsonOriginalObservedRoseMeshHeight (variation)
open Extra.Histories.Motion (orbitCost orbitCost_one_le)

open WilsonOriginalObservedRosePooledPurse (reading)
open WilsonOriginalObservedRoseMeshHeight (tilt)
open WilsonOriginalObservedRoseCorrectedWords (votes)
open WilsonReceivedCanonicalVersePortfolio (weight Selection wallet)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOlderFreshSoftSocketMeasuredCash (packet)
open WilsonThermometerPositionTunedSlope (Columns)
open ActualRunPhysicalPages Pert.Asymptotics

def rank {n:ℕ}(d E:Fin n→ℕ):ℕ:=n*univ.sup (fun i=>E i+WilsonOriginalPublicFigureIncome.height R (d i))

private theorem limit {n:ℕ}(d E:Fin n→ℕ)(s:Finset (Fin n)):
    (∑i:s,E i)≤rank (R:=R) d E ∧ (∑i:s,(E i+WilsonOriginalPublicFigureIncome.height R (d i)))≤rank (R:=R) d E:=by
  let top:=univ.sup (fun i=>E i+WilsonOriginalPublicFigureIncome.height R (d i))
  have hi(i:Fin n):E i+WilsonOriginalPublicFigureIncome.height R (d i)≤top:=le_sup (f:=fun k=>E k+WilsonOriginalPublicFigureIncome.height R (d k)) (mem_univ i)
  have c:s.card≤n:=by simpa using s.card_le_univ
  have cap:(∑i:s,(E i+WilsonOriginalPublicFigureIncome.height R (d i)))≤n*top:=calc
    _≤∑_i:s,top:=sum_le_sum fun i _=>hi i
    _=s.card*top:=by simp
    _≤n*top:=Nat.mul_le_mul_right top c
  exact ⟨(sum_le_sum (fun i (_:i∈(univ:Finset s))=>Nat.le_add_right (E i) _)).trans cap,cap⟩

def charge {n:ℕ}(d:Fin n→ℕ)(M:Fin n→ℝ)(E:ℕ)(s:Finset (Fin n)):ℝ:=
  max (wallet R d M s) (∏i:s,M i)*(4:ℝ)^E

private theorem common {p:ℝ→Prop}(issued:∀ᶠr in trail,p r):∃U:Set ℝ,U∈trail ∧ ∀r∈U,p r:=
  ⟨{r|p r},issued,fun _ h=>h⟩

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (lead:Leading F Jr)(paid:∀g:ℕ,∀ᶠr in trail,Frame.obedient F H (Jr r) g)
    (shop:RG05Preconstruction.ReadoutPurchase R.b)(lo:∀j,1≤((P).budget j).supportExponent)
    (hi:∀j,((P).budget j).supportExponent≤100)(D T h:ℕ)(d:Fin n→Fin (D+1))
    (x:∀i,RG17.Free (C) (d i).val){δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (window:∀s,WilsonMovingForkWindowBooks.Priced F (books s)):
    let k:=fun i=>(d i).val
    ∃(M:Fin n→ℝ)(E:ℕ),(∀i,0≤M i) ∧ ∀mesh:ℕ,∃U:Set ℝ,U∈trail ∧ ∀width:ℕ,∀ᶠv:ℕ in atTop,∀r∈U,
      ∀ρ:Fin n→{t:ℝ // 0<t ∧ t<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let L:=fun i=>reading F Jr Z (books (ρ i)) (d i) (x i)
      ∀(N per b K requested power tag:ℕ)(credit:ℝ)(bk:b≤K)(kn:K≤N),b<N→v≤K → reporter F books ρ≤K→
      (C).S.scale K-(C).S.scale v≤width*Real.log (β v)→let θ:=regulatorRun (C) N per v
      ∀P₀:Panel R k N per b K bk kn requested power tag credit,∀file:Filed R k K,
      P₀.slot=file.station→P₀.axis=file.A N per→(∀i,P₀.slot i=(L i).j)→(∀i,P₀.names i=(L i).arm.source (N,per))→
      1≤θ⁻¹→∀s:Finset (Fin n),(∀i∈s,(C).S.a (P₀.slot i)/(C).S.a K≤(θ⁻¹)^mesh)→
      let w:=votes R k (N:=N) (per:=per) file P₀.names P₀.turn
      let due:=charge (R:=R) k M E s*(θ⁻¹)^(2*E)*(θ⁻¹)^(mesh*WilsonOriginalObservedRoseMeshHeight.height k s+1)
      r^(WilsonOriginalObservedRoseMeshHeight.height k s)*(∑q:Selection R k s,‖weight R k N per K w s q‖)≤due ∧
      r^(WilsonOriginalObservedRoseMeshHeight.height k s)*(∑b:Columns R (fun i:s=>k i),‖packet R k s w N per K b‖)≤due:=by
  intro k
  obtain ⟨M,e,mp,raw⟩:=WilsonOriginalObservedRosePooledPurse.original F Jr Z simple bliss slow lead paid hi D T h d x books window
  let E:=rank (R:=R) k e
  refine ⟨M,E,mp,?_⟩
  intro mesh
  have ep:0<tilt n mesh:=by unfold WilsonOriginalObservedRoseMeshHeight.tilt;positivity
  obtain ⟨gate,fit⟩:=WilsonOriginalObservedRoseMeshPurse.original R k simple shop lo ep
  have left:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  have right:∀ᶠr:ℝ in trail,r<1:=(gt_mem_nhds (by norm_num:0<(1:ℝ))).filter_mono nhdsWithin_le_nhds
  obtain ⟨U,u,receipt⟩:=common ((raw gate).and (left.and right))
  refine ⟨U,u,?_⟩
  intro width
  filter_upwards [WilsonOriginalObservedRosePublicCurrency.clock R simple width E] with v grant
  intro r hr
  obtain ⟨home,rp,small⟩:=receipt r hr
  intro ρ span near L N per b K requested power tag credit bk kn deep vk top corridor θ P₀ file stations axes dates names huge s sizes w due
  have opening(i:Fin n):gate≤P₀.slot i:=(home ρ span near i).1.trans_eq (dates i).symm
  have cash:=fit N per b K bk kn requested power tag credit P₀ file stations axes opening deep
  have earns(i:Fin n):variation R k (P₀.slot i) N per i (P₀.names i)≤M i*(β K)^(e i):=by
    have live:(L i).j<N:=(dates i) ▸ (P₀.before i).trans_lt deep
    rw [dates i,names i]
    exact (home ρ span near i).2.2.2.2 N per K live top
  have film:=WilsonOriginalObservedRosePooledFilms.original R k P₀.slot N per K mesh kn P₀.names w cash.1 M e mp earns s huge sizes
  have cap:1≤β K:=((P).fits.delayed K).le
  have budget:=grant N per K vk kn corridor
  have rates:=limit (R:=R) k e s
  have bill{p:ℕ}{X Y:ℝ}(xp:0≤X)(amount:X ≤ max (wallet R k M s) (∏i:s,M i))(bounded:p≤E)
      (yp:0≤Y)(yield:Y≤X*(β K)^p*(θ⁻¹)^(mesh*WilsonOriginalObservedRoseMeshHeight.height k s+1)):
      r^(WilsonOriginalObservedRoseMeshHeight.height k s)*Y≤due:=by
    have ease:r^(WilsonOriginalObservedRoseMeshHeight.height k s)≤1:=pow_le_one₀ rp.le small.le
    apply (mul_le_of_le_one_left yp ease).trans (yield.trans ?_)
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans huge) _)
    calc
      X*(β K)^p ≤ max (wallet R k M s) (∏i:s,M i)*((4:ℝ)^E*(θ⁻¹)^(2*E)):=
        mul_le_mul amount ((pow_le_pow_right₀ cap bounded).trans budget) (pow_nonneg (zero_le_one.trans cap) _) (xp.trans amount)
      _ = charge (R:=R) k M E s*(θ⁻¹)^(2*E):=by rw [charge,mul_assoc]
  exact ⟨bill (X:=wallet R k M s) (prod_nonneg fun i _=>mul_nonneg (sum_nonneg fun _ _=>WilsonReceivedCanonicalVersePortfolio.nonneg R k i _) (mp i))
     (le_max_left ..) rates.1 (sum_nonneg fun _ _=>norm_nonneg _) film.1,
    bill (X:=∏i:s,M i) (prod_nonneg fun i _=>mp i) (le_max_right ..) rates.2 (sum_nonneg fun _ _=>norm_nonneg _) film.2⟩

end YM.Integration.WilsonOriginalObservedRosePooledVotes
end
