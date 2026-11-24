import YM.Integration.WilsonPhysicalStationBasisOwnedPosts
import YM.Integration.WilsonPhysicalStationPureReleased
/-! The actual homogeneous physical voter on the elected two-report cutoff and its original regulator limit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationBasisBallot
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open PhysicalNext.Repeat.Legato Climb Next.UVStress Trace.Pilot PhysMS Cells
open GapsContact OPE.Levy Stamps Seams Ascent Trace MergeProof.East Maxwell XSpace XSpace.Normalize
open Trace.Terrace Trace.Over FVA2 FVA2.Register WilsonThermometerUnitFilingFourSquare
open scoped Topology Classical BigOperators
open WilsonPhysicalStationSubtractedPair (lower)
open WilsonMovingForkReporterBothArms (Filed)
open PhysicalNext.Repeat Lotus MergeProof PhysicalNext.Repeat.Legato Bandage Campaign
open Next.Foundations Work.G08 Trace.Physical.GermGraph Next.Rank.Price
open WilsonPhysicalStationKineticLimit (transit)
open WilsonPhysicalStationRawReading (err)
open WilsonPhysicalStationSubtractedPosts (heard)
variable {G:Gauge}(R:Run G){T:Campaign R}(L:Pillars R T){f:Extraction.Order}{S:Table R.family.book}
  (fac:Facilities R.family f S)(F:Spec.Final R.family f S){ℓ:Ultrafilter (ℕ×ℕ)}
  (J₀:ℝ→tower S)(J:Scaling S)(V:∀i,Vane R.family i)
  {H:(Bel R.family.book).Hierarchy}{I:Type*}[Fintype I]{m k h e:ℕ}
local notation "rows" => R.family.labels.level h

open WilsonPhysicalStationElectedEars (Reads ready)
open WilsonPhysicalStationFullVote (Head)
open WilsonMovingForkReporterFixedRanks (Axes)
open WilsonPhysicalStationKineticLimit (coupling)
variable (hm:h   ≤   m)(hk:h   ≤   k)(ca:(V m).checked f H m)(cb:(V k).checked f H k)
local notation "idx" => Head R.family h
local notation "A₀" => V m
local notation "B₀" => V k
open WilsonPhysicalStationBasisWallet (vote)
open WilsonPhysicalStationThermalBasisOffice (rank)
open WilsonPhysicalStationThermalRanks (probe)
open WilsonPhysicalStationFullVote (principal)
open WilsonPhysicalStationObservedEntry (born)
open WilsonPhysicalStationRestoredEntry (signal)
open WilsonPhysicalStationPureReceipt (signed coefficients)
open Next.Rank.Station
open Next.Rank.Tapes.West MergeProof.Accent
open Next.Rank.Configuration
open MergeProof MergeProof.East MergeProof.Accent Next.Rank.Tapes Next.Rank.Price
open Next.Rank Next.Rank.East
variable (q:ℕ)
abbrev Seats (C:Family G)(h q:ℕ):Type := {a:Head C h // rank C h a.val=q}
def respondent (z:(standard R.family).Field h):(standard R.family).Field h:=
  (J₀ (A₀).wheel.r h).symm (J.U m h z)
theorem restrict (u:(standard R.family).Field h)(D:(idx)→ℂ):
    ∑a:(idx),coefficients R J₀ J V (k:=k) q u a*D a =
    ∑j:Seats R.family h q,vote R J₀ J V h k u j.val.val*D j.val:=by
  rw [←Fintype.sum_subtype_add_sum_subtype (fun a:(idx)=>rank R.family h a.val=q)
    (fun a=>coefficients R J₀ J V (k:=k) q u a*D a)]
  have yes (j:Seats R.family h q):coefficients R J₀ J V (k:=k) q u j.val=vote R J₀ J V h k u j.val.val:=by
    rw [WilsonPhysicalStationPureReceipt.supported]
    exact if_pos j.property
  have no (j:{a:(idx) // ¬rank R.family h a.val=q}):coefficients R J₀ J V (k:=k) q u j.val=0:=by
    rw [WilsonPhysicalStationPureReceipt.supported]
    exact if_neg j.property
  simp only [yes,no,zero_mul,Finset.sum_const_zero,add_zero]

variable (w:WilsonPhysicalStationFullVote.Head R.family h→(ℕ×ℕ)→R.family.label h)(z:(standard R.family).Field h)
local notation "AX₀" => R.family.path.levels
local notation "E₀" => fun (p:ℕ×ℕ) n=>(signal R p.1 p.2 (A₀).k (B₀).k h n
    (Next.Rank.Station.mag (AX₀) (A₀).b (A₀).k) (Next.Rank.Station.mag (AX₀) (B₀).b (B₀).k):ℂ)
local notation "point" => fun (ξ:Points 2)=>tested (AX₀) (A₀).b (A₀).k ξ
local notation "layout" => fun (ξ:Points 2)=>Next.Rank.Station.choose (AX₀) (A₀).b (A₀).k ξ
local notation "Γ₀" => fun (ξ:Points 2)=>born R h ((point) ξ) z
local notation "μ₀" => fun u (j:Seats R.family h q)=>vote R J₀ J V h k u j.val.val

def Record (K:Set (Points 2))(Z ε:ℝ):Prop:=
  ∀ᶠp:ℕ×ℕ in (ℓ:Filter _),∀ξ:Points 2,(point) ξ∈K→FitSky (AX₀) (A₀).b (A₀).k ξ→
    ∀u:(standard R.family).Field h,‖u‖ ≤ Z→
    ‖WilsonPhysicalStationPureReleased.ink R J₀ J V hm hk cb q w u z ξ p-
      WilsonPhysicalStationPureReleased.bill R J₀ J V (k:=k) (m:=m) q u z ξ p‖ ≤ ε

theorem original (below:(ℓ:Filter _) ≤ f.fuse)(K:Set (Points 2))(Z ε:ℝ)
    (paid:∀ᶠN:ℕ in atTop,∀p:ℕ,∀top:(B₀).k < N,∀ξ:Points 2,(point) ξ∈K→FitSky (AX₀) (A₀).b (A₀).k ξ→
      ∀u:(standard R.family).Field h,‖u‖ ≤ Z→
      let right:=(A₀).wheel.atCut (N,p) ⟨h,Nat.lt_succ_of_le hm⟩ z
      ‖(∑j:Seats R.family h q,(μ₀) u j*WilsonPhysicalStationFullVote.principal R (B₀) (Nat.lt_succ_of_le hk) (per:=p) cb top w (A₀).k (Next.Rank.Station.choose R.family.path.levels (V m).b (V m).k ξ) right j.val)-
        ∑j:Seats R.family h q,(μ₀) u j*((E₀) (N,p) (rank R.family h j.val.val)*(Γ₀) ξ j.val.val)‖ ≤ ε):
    Record R (ℓ:=ℓ) J₀ J V hm hk cb q w z K Z ε:=by
  obtain ⟨n,atN⟩:=eventually_atTop.mp paid
  filter_upwards [ready below (max n (B₀).k)] with p high
  intro ξ inside fit u small
  obtain ⟨N,per⟩:=p
  have top:(B₀).k < N:=(le_max_right ..).trans_lt high
  have rate:=atN N ((le_max_left ..).trans high.le) per top ξ inside fit u small
  rw [WilsonPhysicalStationPureReleased.ink,WilsonPhysicalStationPureReleased.bill,signed,dif_pos top]
  simp only [LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]
  rw [restrict R J₀ J V q u,restrict R J₀ J V q u,Finset.mul_sum]
  convert rate using 1
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [j.property]
  ring
end YM.Integration.WilsonPhysicalStationBasisBallot
end
