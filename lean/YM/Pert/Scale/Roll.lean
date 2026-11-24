import YM.Pert.Scale.ColumnLedger
/-! Leading scale-law patch with a dilation-adjusted seed for all compact length ratios. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
noncomputable section
namespace YM.Pert.Scale
open Extra.FD RawLabels Maxwell Filter Topology Set Function Analysis Spec Ward Climb Position
open scoped Topology ContDiff
variable {G:Gauge} {C:Family G} {I:Extraction.Order} {S:Table C.book} {d n : ℕ}
variable (Q : Conditions C.labels d n) (X : Scaling S)
def rolled (k : ℕ) (t : ℝ) := swipe Q (cloud Q X k t, bank C.labels d t)

variable (hv : CleanProfiles Q) {X} {b:Final C I S} 
include hv
theorem rolling (h : FirstExtension b X) {s : ℝ} (hs : 0<s) :
  Tendsto (uncurry (rolled Q X)) (atTop ×ˢ 𝓝 s) (𝓝 (white Q)) := by
  rw [← swipe_wax Q hv hs]
  exact ((swipe_diff Q).continuous.tendsto _).comp ((cloud_tends Q h hv hs) |>.prodMk_nhds ((bank_diff (recorded C.labels d)).continuous.tendsto s |>.comp tendsto_snd))

lemma cancelled {s : ℝ} (hs : 0<s) :
    fderiv ℝ (swipe Q) (wax Q s, bank C.labels d s) (waxSlope Q s,deriv (bank C.labels d) s) = 0 := by
  let v := fun t : ℝ=>swipe Q (wax Q t, bank C.labels d t)
  have he : v =ᶠ[𝓝 s] fun _=>white Q :=(show ∀ᶠ s' : ℝ in 𝓝 s,0<s' from lt_mem_nhds hs).mono fun i hi=>swipe_wax Q hv hi
  have ht := (show deriv v s=0 by rw [he.deriv_eq,deriv_const])
  have hg : HasDerivAt (bank C.labels d) _ s := ((bank_diff (recorded C.labels d)).differentiable (by decide)).differentiableAt.hasDerivAt
  have hl := ((swipe_diff Q).differentiable (by decide) |>.differentiableAt.hasFDerivAt.comp_hasDerivAt s ((wax_deriv Q hv hs).prodMk hg)).deriv.symm
  exact hl.trans ht

theorem rolled_deriv (h : FirstExtension b X) {t : ℝ} (ht : 0<t) :
    Tendsto (fun k : ℕ => deriv (rolled Q X k) t) atTop (𝓝 0) ∧ ∀ k : ℕ, DifferentiableAt ℝ (rolled Q X k) t := by
  let v k := (cloud Q X k t,bank C.labels d t)
  let w k := (turnedSlope Q (X:=X) k t,deriv (bank C.labels d) t)
  let b0 := bank C.labels d t
  let w0 := (waxSlope Q t,deriv (bank C.labels d) t)
  have hd k : HasDerivAt (rolled Q X k) (fderiv ℝ (swipe Q) (v k) (w k)) t := ((swipe_diff Q).differentiable (by decide) |>.differentiableAt.hasFDerivAt.comp_hasDerivAt t
    ((cloud_deriv Q h hv k ht).prodMk ((bank_diff (recorded C.labels d)).differentiable (by decide) |>.differentiableAt.hasDerivAt)))
  refine ⟨?_ ,fun k=>(hd k).differentiableAt⟩
  have he0 : Tendsto (fun k : ℕ=> (k,t)) atTop (atTop ×ˢ 𝓝 t) := tendsto_id.prodMk tendsto_const_nhds
  have hb : Tendsto v atTop (𝓝 (wax Q t,b0)) := ((cloud_tends Q h hv ht) |>.comp he0).prodMk_nhds tendsto_const_nhds
  have hw : Tendsto w atTop (𝓝 w0) := (cloud_turns Q h hv ht).prodMk_nhds tendsto_const_nhds
  have he := (isBoundedBilinearMap_apply (𝕜:=ℝ) (F:=Ledger Q)).continuous.continuousAt.tendsto.comp
      ((((swipe_diff Q).continuous_fderiv (by simp)).tendsto _ |>.comp hb).prodMk_nhds hw)
  change Tendsto (fun k => fderiv ℝ (swipe Q) (v k) (w k)) _ (𝓝 (fderiv ℝ (swipe Q) (wax Q t,bank C.labels d t) (waxSlope Q t,deriv (bank C.labels d) t))) at he
  rw [cancelled _ hv ht] at he
  exact he.congr (fun k => (hd k).deriv.symm)

end YM.Pert.Scale
