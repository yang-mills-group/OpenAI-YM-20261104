import YM.Integration.WilsonMeasuredSignedActionPrice
import YM.Integration.WilsonMeasuredPublicEntranceActionLadder
import YM.Integration.WilsonMeasuredPublicEntranceActionPremium
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionNamed
open Function Filter Set Finset Extraction Table Spec Climb Maxwell Maxwell.Free Lattice RG Wilson
open Trace Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph Source Labels
open Trace.Over Trace.Terrace Trace.Pilot TraceExtension MergeProof.East Next.Rank Next.UVStress
open PhysicalNext.Repeat.Legato Further.CorrectedLift RG05Readout.Address Next.Rank.Atlas
open Next.Rank.Price Next.Rank.Station WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMeasuredPublicEntranceGridDebit WilsonMaxwellThermometerMaximalHead
open WilsonMaxwellThermometerStationHeads WilsonPhysicalChiralNonfreeStationMoney
open WilsonOriginalTwoFlatPublicBooks WilsonOriginalMicroscopicGuardedReporters
open WilsonMeasuredSignedActionCourse WilsonMeasuredSignedActionAverage
open MergeProof Campaign
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {H:(Bel R.family.book).Hierarchy}{l:Ultrafilter (ℕ×ℕ)}{Z:Arch R.family}
local notation "C" => R.family
local notation "F₀" => R.family.labels.level 4
local notation "road" => R.family.path.levels

private theorem entire (B:Labels.Frame G 4)(simple:G.Simple)(s a:ℝ)(e p:B.Coeff):
    B.coeffSize (((s*a:ℝ):ℂ) • B.core e-B.core p)=error B s ((a:ℂ) • e) p:=by
  unfold Frame.coeffSize error
  apply Finset.sum_congr rfl
  intro i _
  by_cases z:i=0
  · subst i;simp [Frame.core,B.zero_degree]
  · rw [WilsonOriginalPublicTrialPhaseFourDictionary.weight B simple i z]
    simp [Frame.core,z,mul_assoc]

theorem symbol (simple:G.Simple){J:Scaling S}{V:∀i,Vane C i}
    (cause:Scribe f J V Z F.sector l F.room.kernel H):
    ladder C 4 (stepField C)=(F₀).coords (Trace.square4 G) ∧ fixed F₀ (axis F₀):=by
  have id:=WilsonMeasuredPublicEntranceActionLadder.original F simple cause
  refine ⟨id,?_⟩
  obtain ⟨bar,turns⟩:=WilsonMeasuredPublicEntranceActionPremium.symmetries F₀
  rintro ⟨s,b⟩
  rw [axis,Extra.Histories.Motion.core_patch]
  cases b <;> simp [Extra.Histories.Motion.patch,turns,bar]

variable {T:Campaign R}(L:Pillars R T)
include L in
theorem original (simple:G.Simple)(raw:ladder C 4 (stepField C)=(F₀).coords (Trace.square4 G))
    (invariant:fixed F₀ (axis F₀))(alive:0<(F₀).coeffSize (axis F₀)):
    ∀ᶠ j:ℕ in atTop,∀ᶠ z:ℕ×ℕ in f.fuse,∀{D T:ℕ}{r:ℝ}
    (B:Book F (l:=l) H Z D T r) (fits:4≤D) (_site:B.W.k=j),
    let i:Fin (D+1):=⟨4,Nat.lt_succ_of_le fits⟩
    let y:=((B.rows i).arm true (B.V i (stepField C))).source z
    let e:=fitted R 4 j z.1 z.2 y
    ∀{n target:ℕ}(_old:0<n)(top:j+n≤z.1){η:ℝ}
    (A:(C).label 4 ≃ₗ[ℂ] (C).label 4)
    (_before:R.t 4≤j)(_ref:(C).ref 4≤j)(_width:1≤((C).path.levels.budget j).supportExponent)
    (_incoming:Arrived R 4 j (j+n) z.1 z.2 target (by omega) top η A e),
    ∃c:ℝ,0≤c ∧ (F₀).core (pool F₀ (A.symm e))=(c:ℂ) • axis F₀:=by
  let p:=(F₀).coords (Trace.square4 G)
  filter_upwards [WilsonMeasuredSignedActionVote.original R L simple,
    WilsonMeasuredSignedActionStation.original R F simple,
    WilsonMeasuredSignedActionPrice.original R simple f ((F₀).coeffSize p) alive,
    clock R simple,open_late C simple 4] with j issued rated fees clk opened
  filter_upwards [fees] with z budget
  intro D T r B fits site i y e n target old top η A before ref width incoming
  let v:=B.V i (stepField C)
  have read:=rated B i v site z.1 z.2 (j+n) target (by omega) top before ref width A incoming
  obtain ⟨_,h⟩:=read
  let χ:=(shrink C j z.1 z.2)^2/(Station.mag road B.W.b j)^4
  let a:=((C).S.a j^4)⁻¹
  have rawv:ladder C 4 ((B.V i).symm v)=p:=by rw [show (B.V i).symm v=stepField C from (B.V i).symm_apply_apply _,raw]
  have enrolled:error F₀ χ ((a:ℂ) • e) p≤WilsonMeasuredSignedActionPrice.fare R j z ((F₀).coeffSize p):=by
    have h':=h
    rw [LinearEquiv.apply_symm_apply,rawv] at h'
    simpa only [i,χ,a,e,y,v,WilsonMeasuredSignedActionPrice.fare,Complex.ofReal_inv,Complex.ofReal_pow, Nat.reduceDiv] using h'
  have ep:=entire F₀ simple χ a e p
  have tol:(F₀).coeffSize (((χ*a:ℝ):ℂ) • (F₀).core e-axis F₀)≤_:=ep.trans_le enrolled
  have mag:0<Station.mag road B.W.b j:=Real.rpow_pos_of_pos
    ((by norm_num:(0:ℝ)<2).trans_le clk.2.1) _
  have pos:0<χ*a:=mul_pos (div_pos (pow_pos (clk.2.2 z.1 z.2 ((Nat.le_add_right ..).trans top)).1 _) (pow_pos mag _))
    (inv_pos.mpr (pow_pos ((C).S.a_pos j) _))
  exact issued top A e (opened z.2) incoming invariant _ _ pos tol budget
end YM.Integration.WilsonMeasuredSignedActionNamed
end
