import YM.Integration.WilsonPositionScaleLawJacobian
import YM.Integration.WilsonPositionProgramDilation
import Mathlib.Analysis.RCLike.Extend

/-! The independent position (before homogeneous adjustment) scale matrix,
on the determining store and the original kinetic units. Every coefficient
comes from the one fixed MS match. Its graded inclusions hold before all
observables and the positive coefficients are uniformly small on a ratio sweep. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawIndependent
open Function Filter Set Finset PowerSeries Maxwell XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawNative (positive)
open scoped Topology BigOperators Classical
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

abbrev B (s:ℝ)(d:ℕ):Guard G d:=GroupS.gaugeB Z.criterion M ν s d
abbrev ψ (s:ℝ):Cn:=GroupS.ψ Z.criterion M ν s
abbrev normalized (d:ℕ):Reports G d:=Reg.Faith.reports ν Z.criterion M d

def scaleRows (d:ℕ)(s:ℝ):Reports G d:=realm (mirror (B Z M ν s d)) (substitute (ψ Z M ν s) (normalized Z M ν d))

def time (t:Ratio):ℝ:= -Real.log t.val

theorem continuousTime:Continuous time:=(continuous_subtype_val.log (fun t=>(positive t).ne')).neg

theorem geometry (t:Ratio):Real.exp (-(time t))=t.val:=by rw [time,neg_neg,Real.exp_log (positive t)]

include H in
theorem original (d:ℕ)(s:ℝ):Jury.Orders (Facets.scaling s (Measure.start Z.scheme Z.criterion d)) (scaleRows Z M ν d s):=by
  let input:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  let law:=(H.details.normative ν).first
  have normalizedRow:=Jury.enrolled ν M Z.scheme Z.criterion σ hG input.Taylor input.still input.base (d:=d)
  have shift:Facets.scaling s (Measure.start Z.scheme Z.criterion d) =
      Facets.actMark (mirror (B Z M ν s d)) (Facets.couple (ψ Z M ν s) (Measure.start Z.scheme Z.criterion d)):=by
    rw [←law.reads s d,Facets.acts,(law.paid s d).turn',Facets.acts_h]
  rw [shift]
  exact (normalizedRow.glance (ψ Z M ν s)).specify _

include H in
theorem solved (d k:ℕ)(s:ℝ): (Z.store.measure d).D (realm (B Z M ν s d) (scaleRows Z M ν d s) k)=
    if k=0 then (Z.store.measure d).D (reference G d) else 0:=by
  let input:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  let law:=(H.details.normative ν).first
  rw [scaleRows,Normalize.parlance,(law.paid s d).turn,Normalize.author]
  have sol:=Jury.solved ν M Z.scheme Z.criterion σ hG input.Taylor input.still input.base
    (d:=d) (law.led s).start (law.led s).real k
  rwa [deck0,Normalize.author] at sol

/-- Allowed positive coefficient, independent of physical radii and comparison order. -/
def letter (d k:ℕ)(s:ℝ):Change G d:=if h:coeff (k+1) (B Z M ν s d)∈Change G d then ⟨_,h⟩ else 0

include H in
theorem filled (d k:ℕ)(s:ℝ):(letter Z M ν d k s).val=coeff (k+1) (B Z M ν s d):=by
  rw [letter,dif_pos (((H.details.normative ν).first.paid s d).high (k+1) (Nat.succ_ne_zero _))]

def trial (d q:ℕ)(s g:ℝ):MoveSpace G d:=∑k∈range q,g^(k+1) • guide G d (letter Z M ν d k s)

private theorem charted {U:Type*}[AddCommGroup U][Module ℝ U][Module ℂ U][IsScalarTower ℝ ℂ U]
    {n:ℕ}(R:(Fin n→ℝ)→ₗ[ℝ]U)(hi:Injective R)(a:ℝ→Fin n→ℝ)(A:ℝ→U)
    (row:∀s,R (a s)=A s)(ready:∀u:Module.Dual ℂ U,Continuous (fun s=>u (A s))):Continuous a:=by
  obtain ⟨L,hL⟩:=LinearMap.exists_leftInverse_of_injective (K:=ℝ) R (show LinearMap.ker R=⊥ from LinearMap.ker_eq_bot.mpr hi)
  apply continuous_pi
  intro j
  let u:Module.Dual ℝ U:=(LinearMap.proj j).comp L
  let v:Module.Dual ℂ U:=u.extendRCLike
  have same(s:ℝ):(v (A s)).re=a s j:=by
    rw [show (v (A s)).re=u (A s) from Module.Dual.re_extendRCLike_apply (𝕜:=ℂ) u _,←row]
    exact congrArg (fun q:Fin n→ℝ=>q j) (DFunLike.congr_fun hL (a s))
  exact (Complex.continuous_re.comp (ready v)).congr same

include H in
theorem coefficient (d k:ℕ)(u:Module.Dual ℂ (FieldEnd G d)):
    Continuous (fun s=>u (coeff k (B Z M ν s d))):=
  continuous_iff_continuousAt.mpr fun s=>((H.details.normative ν).criterion d s k u).continuousAt

include H in
theorem continuous (d k:ℕ):Continuous (fun s=>guide G d (letter Z M ν d k s)):=by
  let R:MoveSpace G d→ₗ[ℝ]FieldEnd G d:=((Change G d).subtype).comp (guide G d).symm.toLinearMap
  have hi:Injective R:=(Change G d).subtype_injective.comp (guide G d).symm.injective
  apply charted R hi _ (fun s=>coeff (k+1) (B Z M ν s d)) _ (coefficient Z M H ν d (k+1))
  intro s
  change ((guide G d).symm (guide G d (letter Z M ν d k s))).val=_
  rw [(guide G d).symm_apply_apply,filled Z M H ν]

include H in
theorem small (d q:ℕ){g:ℝ→ℝ}(hg:Tendsto g Trace.Pilot.trail (𝓝 0)):
    Tendsto (fun z:ℝ×Ratio=>trial Z M ν d q (time z.2) (g z.1)) sweep (𝓝 0):=by
  have joint:Continuous (fun z:Ratio×ℝ=>trial Z M ν d q (time z.1) z.2):=by
    apply continuous_finsetSum;intro k _
    exact (continuous_snd.pow _).smul ((continuous Z M H ν d k).comp
      (continuousTime.comp continuous_fst))
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have unif:=PhysMS.Frame.compact_event ℝ (isCompact_univ : IsCompact (univ:Set Ratio))
    (fun r t=>dist (trial Z M ν d q (time t) (g r)) 0<ε) (l:=Trace.Pilot.trail) (fun t _=>by
      have h:= (joint.tendsto (t,0)).comp (tendsto_snd.prodMk_nhds (hg.comp tendsto_fst))
      have base:trial Z M ν d q (time t) 0=0:=by simp [trial]
      rw [base] at h
      exact Metric.tendsto_nhds.mp h ε he)
  exact (tendsto_fst.eventually unif).mono fun z hz=>hz z.2 (mem_univ _)

include H in
theorem inclusions {d e:ℕ}(h:d≤e)(k:ℕ)(s:ℝ)(v:Sec G d):
    (letter Z M ν e k s).val (up h v)=up h ((letter Z M ν d k s).val v):=by
  rw [filled Z M H ν,filled Z M H ν]
  exact (H.details.normative ν).first.continues s h (k+1) v

end YM.Integration.WilsonPositionScaleLawIndependent
end
