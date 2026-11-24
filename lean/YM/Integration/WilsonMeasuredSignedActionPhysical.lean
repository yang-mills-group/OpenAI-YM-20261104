import YM.Integration.WilsonMeasuredSignedActionNamed
import YM.Integration.WilsonMeasuredSignedActionFiledUnit

/-! The positioned Wilson action on its actual issued weak books and the one
filed axis purchased before inputs and tests. The radius goes to zero after
the cutoff filter, whose inner limit is UV at fixed period. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionPhysical
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalTwoFlatPublicBooks
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open WilsonOriginalMicroscopicGuardedReporters MergeProof Campaign
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
    {T:Campaign R}(L:Pillars R T)
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l Z H)
    {J:ℝ→PhysMS.tower S}{P:ℝ→Spin.change S 4}{δ g:ℝ→ℝ}
    (frame:∀ᶠ r in trail,J r 4=P r)(cal:TendC F P δ)(heat:Coupling G g)
    (X:Zoom){D T:ℕ→ℕ}(B:∀m,Book F (l:=l) H Z (D m) (T m) (X.r m))
    (roof:∀m,m≤(B m).k)(stages:Tendsto (fun m=>(B m).W.k) atTop atTop):
    ∀ᶠ m:ℕ in atTop,∀ h:4≤D m,∀ᶠ z:ℕ×ℕ in f.fuse,
    let i:Fin (D m+1):=⟨4,Nat.lt_succ_of_le h⟩
    let j:=(B m).W.k
    let y:=(((B m).rows i).arm true (J (X.r m) 4 (stepField C))).source z
    let e:=fitted R 4 j z.1 z.2 y
    ∀{n target:ℕ} (_old:0<n)(top:j+n≤z.1){η:ℝ}
    (A:(C).label 4 ≃ₗ[ℂ] (C).label 4)(_width:1≤((C).path.levels.budget j).supportExponent)
    (_sale:∀x,Arrived R 4 j (j+n) z.1 z.2 target (by omega) top η A x),
      ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ (A.symm e))=(s:ℂ) • axis F₀:=by
  obtain ⟨_,_,J₀,_,V₀,cause⟩:=bliss.picks X.r X.limits X.positive
  obtain ⟨raw,inv⟩:=WilsonMeasuredSignedActionNamed.symbol R F simple cause
  have live:=WilsonMeasuredPublicEntranceActionPremium.positive simple F₀
  have core:=WilsonMeasuredSignedActionNamed.original R F (H:=H) (l:=l) (Z:=Z) L simple raw inv live
  have axes:=WilsonMeasuredSignedActionBooked.original F simple bliss frame cal heat X B roof stages
  filter_upwards [axes,stages.eventually core,stages.eventually (WilsonMeasuredSignedActionUnit.original R L simple),
    stages.eventually (open_late C simple 4)] with m anchor admitted exactUnit homes
  intro fits
  obtain ⟨s,c,positive,heading⟩:=anchor fits
  filter_upwards [admitted] with z leg
  intro i j y e n target old top η A width sale
  have h:=homes z.2
  have early:(C).ref 4≤j:=h.post
  have strict:j<z.1:=by omega
  have sy:=WilsonMeasuredSignedActionFiledUnit.source R F (B m) fits z strict _ s c
    (by simpa only [Complex.coe_smul] using heading)
  let primitive:=(((B m).rows i).arm true ((B m).V i (stepField C))).source z
  let b:=fitted R 4 j z.1 z.2 primitive
  have paid:e=(s:ℂ) • b+c • unitVec F₀ (C).path j:=
    WilsonMeasuredSignedActionFiledUnit.deposited R h strict.le y primitive s c sy
  have unit:=exactUnit top A h (sale (A (unitVec F₀ (C).path (j+n))))
  obtain ⟨k,hk,step⟩:=leg (B m) fits rfl old top A early early width (sale b)
  exact WilsonMeasuredSignedActionFiledUnit.voted R A unit e b s k c positive.le hk paid step

end YM.Integration.WilsonMeasuredSignedActionPhysical
end
