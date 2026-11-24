import YM.Pert.Scale.Adjust
import YM.Pert.Position.Four
/-! Engineering first term of actual frame scale derivative and position tests. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Pert.Scale
open Extra.FD Maxwell RawLabels Position Spec Climb Set Function Filter Topology Analysis MeasureTheory Ward
open scoped ContDiff BigOperators
variable {G:Gauge} {C:Family G} {d n : ℕ} {Q : Conditions C.labels d n}
lemma passage {A V : Type} [NormedAddCommGroup A] [NormedAddCommGroup V] [NormedSpace ℝ A] [NormedSpace ℝ V]
   (f : A → V) (a b : ℕ→A) (x y : A) (ha : Tendsto a atTop (𝓝 x)) (hb : Tendsto b atTop (𝓝 y)) (hf : ContDiffAt ℝ ω f x) :
   Tendsto (fun k=>fderiv ℝ f (a k) (b k)) atTop (𝓝 (fderiv ℝ f x y)) :=
     isBoundedBilinearMap_apply (𝕜:=ℝ) |>.continuous.continuousAt.tendsto.comp ((hf.continuousAt_fderiv (by decide) |>.tendsto.comp ha).prodMk_nhds hb)

lemma gear_curve (F : Labels.Frames G) (p : E F d) : ContDiff ℝ ω (fun t : ℝ => gear F d t p) := by
  have ht : (fun t : ℝ => gear F d t p)=(fun t => motor F (bank F d t) p) := funext fun t => Eq.symm (motor_bank F p t)
  rw [ht]; exact (motor_diff _).comp (bank_diff (recorded F d))
def choir (F : Labels.Frames G) (v : ℝ × Buffer F d) (p : E F d) := gear F d v.1 (motor F v.2 p)
lemma conducts (F : Labels.Frames G) (p : E F d) : ContDiff ℝ ω (fun v:ℝ×Buffer F d => choir F v p) := by
  have ht := (motor_diff p).comp (f:=fun x:ℝ×Buffer F d=>x.2) (g:=fun b=>motor F b p) contDiff_snd
  let M (x : ℝ×Buffer F d) := motor F (bank F d x.1)
  have hM : ContDiff ℝ ω M := by
    change ContDiff ℝ ω (fun (x : ℝ×Buffer F d) => (1:Position.operator F d)+(bank F d x.1).val)
    let L := (Submodule.subtypeL (buffers F d))
    exact contDiff_const.add ((ContinuousLinearMap.contDiff (n:=ω) (𝕜:=ℝ) (E:=Buffer F d) (F:=Position.operator F d) L).comp ((bank_diff (recorded F d)).comp (f:=Prod.fst) contDiff_fst))
  have hv : choir F = fun v:ℝ×Buffer F d=> fun p => M v (motor F v.2 p) := funext fun i=> funext fun p=> Eq.symm (motor_bank F (motor F i.2 p) i.1)
  rw [hv]; exact ContDiff.clm_apply hM ht
lemma quiet (F : Labels.Frames G) (p : E F d) (t : ℝ) : choir F (t,0) p=gear F d t p:= by change gear _ _ _ (p + (0:E F d))=_; rw [add_zero]

variable {I : Extraction.Order} {S : Table C.book} {b : Final C I S} {X : Climb.Scaling S} {φ : Ledger Q → Buffer C.labels d}
  (h : FirstExtension b X) (hv : CleanProfiles Q) (hl : Reports (chart Q) (white Q) 0 φ)

include h hv hl
private lemma atFrame {s : ℝ} (hs : 0<s) (p : E C.labels d) :
    ∀ᶠ k in atTop, (fun t : ℝ=>relative X φ k t p) =ᶠ[𝓝 s] fun t => choir C.labels (t,correction X φ k t) p := by
  obtain ⟨v,hv0,w,hw,he⟩ := eventually_prod_iff.mp (clearance h hv hl hs)
  exact hv0.mono (fun k hk=>hw.mono (fun t ht=>rel_eq X (he hk ht).1 p))
omit h hv hl in
lemma fixed_stitch {V : Type} [TopologicalSpace V] {v : ℕ→ℝ→V} {y : V} {s : ℝ} (h:Tendsto (uncurry v) (atTop ×ˢ 𝓝 s) (𝓝 y)) :
    Tendsto (fun k=>v k s) atTop (𝓝 y) := by
 have hk : Tendsto (fun k:ℕ=>(k,s)) atTop (atTop ×ˢ 𝓝 s) := tendsto_id.prodMk tendsto_const_nhds
 exact h.comp hk
private lemma correct_center {s : ℝ} (hs : 0<s) : Tendsto (fun k => correction X φ k s) atTop (𝓝 (0:Buffer C.labels d)) :=
   fixed_stitch (v:=correction X φ) (corrects h hv hl hs)

/-- Pointwise relative frame leading *and its first length-ratio derivative*, after returning to X.U coordinates. Does not bound (X.U k d) or its inverse on fixed-field coordinates as functions of a physical coupling. -/
lemma relative_leading {s : ℝ} (hs : 0<s) (p : E C.labels d) :
   Tendsto (fun k => relative X φ k s p) atTop (𝓝 (gear C.labels d s p)) ∧
   Tendsto (fun k=>deriv (fun t=>relative X φ k t p) s) atTop (𝓝 (deriv (fun t=> gear C.labels d t p) s)) := by
  let Y := fun t : ℝ=> gear C.labels d t p
  let Y' := fun v : ℝ×Buffer C.labels d=>choir C.labels v p
  obtain ⟨ih,ht⟩ := correction_deriv h hv hl hs
  have he := atFrame h hv hl hs p
  have h₁ : Tendsto (fun k=> (s,correction X φ k s)) atTop (𝓝 (s,(0:Buffer C.labels d))) := tendsto_const_nhds.prodMk_nhds (correct_center h hv hl hs)
  have hh := (conducts C.labels p).continuous.continuousAt.tendsto.comp h₁
  refine ⟨quiet C.labels p s ▸ hh.congr' (he.mono (fun _ hk=> Eq.symm hk.eq_of_nhds)),?_⟩
  let U k t := (t,correction X φ k t)
  have hU k (hk : DifferentiableAt ℝ (correction X φ k) s) : HasDerivAt (U k) (1,deriv (correction X φ k) s) s := by
    have hx : HasDerivAt (correction X φ k) (deriv (correction X φ k) s) s :=
      DifferentiableAt.hasDerivAt (𝕜:=ℝ) (f:=correction X φ k) hk
    exact (hasDerivAt_id' s).prodMk (G:=Buffer C.labels d) (f₂:=correction X φ k) (f₂':=deriv (correction X φ k) s) hx
  have ht0 : fderiv ℝ Y' (s,(0:Buffer C.labels d)) (1,0) = deriv Y s := by
    let T (t : ℝ) := (t,(0:Buffer C.labels d))
    have ht : Y' ∘ T = Y := funext (quiet C.labels p)
    change _ = deriv _ _
    rw [← ht]
    exact Eq.symm (((conducts C.labels p).differentiable (by decide) |>.differentiableAt.hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id' s).prodMk (hasDerivAt_const _ (0:Buffer C.labels d)) : HasDerivAt T _ s)).deriv)
  have hr : Tendsto (fun k : ℕ => ((1:ℝ),deriv (correction X φ k) s)) atTop (𝓝 (1,0)) := tendsto_const_nhds.prodMk_nhds ht
  let q := passage (V:=E C.labels d) (A:=ℝ×Buffer C.labels d) Y' (fun k=>U k s) (fun k=>((1:ℝ),deriv (correction X φ k) s)) (s,0) (1,0) h₁ hr (conducts _ _ |>.contDiffAt)
  rw [ht0] at q
  refine q.congr' ?_
  filter_upwards [he,ih] with k hk hi
  change _ = deriv _ _ 
  rw [hk.deriv_eq]
  exact Eq.symm (((conducts C.labels p).differentiable (by decide) |>.differentiableAt.hasFDerivAt.comp_hasDerivAt s (hU k hi)).deriv)
end YM.Pert.Scale
