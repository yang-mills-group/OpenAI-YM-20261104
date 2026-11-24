import YM.Integration.WilsonTrueProjectedGermStep
import YM.Integration.WilsonMeasuredOnlyHard

/-! Separate the analytic part on the canonical measured vacuum from the
forced numerator on the actual elected vacuum. A pure hard input can emit
a measured coordinate on its very next push. Both fresh charges appear
in the true field identity and the forced account is retained. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedTwoCarrierStep
open Filter MeasureTheory Lattice Wilson RG Labels Source
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato
open Extra.Histories Extra.Histories.Relay Bid MergeProof
open WilsonPhysicalMarkedDefect WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge} {C : Family G} {d p N i : ℕ}
local notation "σ" => (C.labels.level d).coeffSize
local notation "Q" => GermGraph.store C d p
local notation "V" => GermGraph.value (C:=C) d N p
local notation "Y" => GermGraph.calValues (C:=C) d N p
local notation "π" => GermGraph.page (C:=C) d p
local notation "X" => GermGraph.measuring C d N p
local notation "U" => GermGraph.transition (C:=C) d N p i
local notation "P" => C.path.rep N p i
local notation "S" => C.localSection d
local notation "κ" => safety C i

theorem clear (W : Rep G (C.side i p)) (e : Q i) (fmt : e.Format 0 C.params W) :
    account e W =ᶠ[𝓝 1] 0 := by
  filter_upwards [ProjectorNext.Equivariance.offFlags (G:=G) (n:=C.side i p)
    W.p.threshold W.p.threshold_pos] with B hB
  change (Real.exp (W.exponent B):ℂ)*_ = 0
  rw [tsum_congr (fun b => RegularProjection.clear e 0 W C.params fmt B hB b),tsum_zero,mul_zero]

/-- The two true pushes on the left are separate linear operands on the
same Wilson kernel. The lower elected hard inventory can have different
numerical activities from the canonical one. Only their reserved addresses,
budget point and vacuum value are identified. -/
theorem original (H : C.Makes) (hi : i<N) (hc : Opened C d i p)
    {γ ε r b u a M : ℝ} (gate : Gate C d N p i γ ε)
    (W : Rep G (C.side i p)) (Wf : Rep G (C.side (i+1) p))
    (point : (P).p=W.p) (owners : (P).activities.forced=W.activities.forced) (quiet : W.eval=(P).eval)
    {s c Λ δ ω : ℝ} (law : W.Lawful s c Λ δ ω)
    (y : C.label d) (q h : Q (i+1)) (e z template : Q i)
    (fine : Config G (C.side (i+1) p) → ℂ) (lower : Config G (C.side i p) → ℂ)
    (seated : reads d N p (i+1) q r) (null : π (i+1) q=0)
    (earned : e.Format 0 C.params W ∧ e.remBound 0 W κ b)
    (heard : z.Format 0 C.params W ∧ z.remBound 0 W κ u)
    (nearTemplate : lower =ᶠ[𝓝 1] V i template) (templateBill : reads d N p i template M)
    (held : Integrable (account h Wf) (prior G (C.side (i+1) p)))
    (input : Y (i+1) y = fine + (V (i+1) q + account h Wf))
    (fresh : U fine = lower + e.density 0 S W)
    (old : U (account h Wf) = z.density 0 S W)
    (cap : σ (π i (soft (beside e z))) ≤ a) :
    let mix := beside e z
    let loss := (factor C i)^(-GermGraph.rate)
    let fit := fitting d N p i H hc hi.le
    mix.Format 0 C.params W ∧ mix.remBound 0 W κ (b+u) ∧
    ∃ (next : Q i) (feed : C.label d), reads d N p i next (loss*r+((b+u)+2*stock C i*a)) ∧
      π i next=0 ∧ σ (X i feed) ≤ ε*r*loss ∧
      X i y-π i template = X i feed + π i (soft mix) ∧
      V i next + account mix W = Y i (fit.symm (π i template))-lower := by
  intro mix loss fit
  have bought : mix.Format 0 C.params W ∧ mix.remBound 0 W κ (b+u) :=
    presentation earned.1 earned.2 heard.1 heard.2
  have merged : mix.density 0 S W = e.density 0 S W + z.density 0 S W :=
    plus law earned.2 heard.2 S
  obtain ⟨regular,charge,identity,_⟩ := WilsonMeasuredOnlyHard.original mix P W point quiet owners
    S C.params 0 κ (b+u) bought.1 bought.2
  have orig : reads d N p i (soft mix) (b+u) := ⟨regular,charge⟩
  have split : mix.density 0 S W = V i (soft mix) + account mix W := funext identity
  have high := message d N p (i+1) H (hc.post.trans i.le_succ) hi seated
  have calibrated := message d N p (i+1) H (hc.post.trans i.le_succ) hi
    (entryOk d N p (i+1) H (hc.post.trans i.le_succ) hi y)
  have hf : Integrable fine (prior G _) := by
    rw [show fine = Y (i+1) y-(V (i+1) q + account h Wf) by rw [input]; abel]
    exact calibrated.sub (high.add held)
  have incoming : Y (i+1) y = (fine+account h Wf) + V (i+1) q := by rw [input]; abel
  have step : U (fine+account h Wf) = (lower+account mix W) + V i (soft mix) := by
    rw [transition_add d N p hf held,fresh,old,add_assoc,←merged,split]
    abel
  have clean : lower+account mix W =ᶠ[𝓝 1] V i template := by
    simpa only [add_zero] using nearTemplate.add (clear W mix bought.1)
  obtain ⟨next,feed,paid,pn,pf,amount,out⟩ :=
    WilsonTrueProjectedGermStep.original H hi hc gate y (fine+account h Wf) q
      (lower+account mix W) template (soft mix) seated null incoming templateBill orig clean step
  refine ⟨bought.1,bought.2,next,feed,⟨paid.1,rem_increase d paid.2 ?_⟩,pn,pf,amount,?_⟩
  · exact add_le_add le_rfl (add_le_add le_rfl (mul_le_mul_of_nonneg_left cap
      (mul_nonneg zero_le_two (zero_le_one.trans (stage C i).columns_ge))))
  · rw [out]
    abel

end YM.Integration.WilsonTrueProjectedTwoCarrierStep
