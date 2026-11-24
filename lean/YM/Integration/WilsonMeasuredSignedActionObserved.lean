import YM.Integration.WilsonMeasuredSignedActionPacket
import YM.Integration.WilsonMeasuredSignedActionBookLimits
/-! The signed Ward observable occupies its nominated slot throughout
the original ordered cutoff and period passage. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionObserved
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift
open WilsonMeasuredPublicEntranceGridDebit WilsonOriginalTwoFlatPublicBooks
open WilsonPositionThermometerCapStation WilsonOriginalThermometerPalette
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open WilsonOriginalMicroscopicGuardedReporters MergeProof Campaign
open WilsonMovingForkHeterogeneousCut (Filed)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
    {T:Campaign R}(L:Pillars R T)
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4


open WilsonMeasuredSignedActionPacket (Packet)
open WilsonMeasuredSignedActionRegistry (weak HeardAt)
open WilsonPositionProgramTrialPublicJointFourMixedIncome (castField turned)
open WilsonReflectedPublicGuardedMotion

theorem filing {n K N per:ℕ}{d:Fin n→ℕ}(E:Packet R d K)(i:Fin n)(four:d i=4)
    (turn:E.turns i=(1,false))(past:E.file.station i<K)(top:K<N)
    (wide:1≤((C).path.levels.budget (E.file.station i)).supportExponent)
    (hears:HeardAt R (E.file.station i) N per (castField R four (E.words (N,per) i))):
    ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ (E.vote (N,per) i four))=(s:ℂ) • axis F₀:=by
  unfold Packet.vote turned
  rw [turn,WilsonOriginalPublicTrialPhaseMotion.plain]
  exact WilsonMeasuredSignedActionRegistry.raised R four (E.words (N,per) i) (E.file.A N per i) past top.le wide
    (fun x=>E.file.arrived N per top i x) hears

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l Z H)
    {J:ℝ→PhysMS.tower S}{P:ℝ→Spin.change S 4}{δ g:ℝ→ℝ}
    (frame:∀ᶠ r in trail,J r 4=P r)(cal:TendC F P δ)(heat:Coupling G g)
    (X:Zoom){D T:ℕ}(B:∀m,Book F (l:=l) H Z D T (X.r m))
    (grows:Tendsto (fun m=>(B m).k) atTop atTop)(stages:Tendsto (fun m=>(B m).W.k) atTop atTop)(fits:4≤D)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent){K:ℕ→ℕ}
    {n:ℕ}{d:Fin n→ℕ}(E:∀m,Packet R d (K m))(i:Fin n)(four:d i=4)
    (home:∀m,(E m).file.station i=(B m).W.k)(later:∀m,(B m).W.k<K m)
    (turn:∀m,(E m).turns i=(1,false))(source:∀m b,castField R four ((E m).words b i)=
      weak R F (B m) fits (J (X.r m)) b):
    ∀ᶠ p:ℕ×(ℕ×ℕ) in atTop.curry f.fuse,
      ∃s:ℝ,0 ≤ s ∧ (F₀).core (pool F₀ ((E p.1).vote p.2 i four))=(s:ℂ) • axis F₀:=by
  have offered:=WilsonMeasuredSignedActionBookLimits.original R F L simple bliss frame cal heat X B grows stages
  apply eventually_curry_iff.mpr
  refine offered.mono (fun m ready=>?_ )
  have window:∀ᶠ b:ℕ×ℕ in f.fuse,K m<b.1:=(Push.RelayDifference.cutoff_grows f).eventually_ge_atTop (K m+1)
  filter_upwards [ready fits,window] with b heard beyond
  have placed:HeardAt R ((E m).file.station i) b.1 b.2 (castField R four ((E m).words b i)):=by
    rw [home m,source m b]
    exact heard
  have past:(E m).file.station i<K m:=by rw [home m];exact later m
  exact filing R (E m) i four (turn m) past beyond (wide _) placed
end YM.Integration.WilsonMeasuredSignedActionObserved
end
