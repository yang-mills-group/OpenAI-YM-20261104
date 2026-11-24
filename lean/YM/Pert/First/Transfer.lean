import YM.Pert.First.Dress
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Pert.First
open Filter Orb Lattice Function Topology Matrix
open scoped Topology
variable {G : Gauge} {N : Side}
variable (u : G.El)
lemma rough_colored : ∀ᶠ p : Potential G N × Parameter G N in 𝓝 (0,0), roughLog (linkCol u p.1) (paramCol u p.2) = G.adjoint u ∘roughLog p.1 p.2 := by
 refine ((eventually_all.mpr (fun l=> (turn_cont l).eventually (Stationary.plog_conj u)))).mono (fun p hp=>funext fun e=> ?_)
 rw [roughLog,turn_under]; exact hp e
lemma fpfield_colored : ∀ᶠ a : Potential G N in 𝓝 0, (∀ᶠ b in 𝓝 0, FPField (linkCol u a) (paramCol u b) = meanCol u (FPField a b)) := by
 have H:= rough_colored (N:=N) u
 rw [nhds_prod_eq] at H
 exact H.curry.mono fun a ha=> ha.mono fun b he=> by rw [FPField,shiftedLog,show roughLog (linkCol u a) _ = _ from he, color_bal,color_dlin];rfl
lemma ready_field : ∀ᶠ a : Potential G N in 𝓝 0, DifferentiableAt ℝ (FPField a) 0 := by
  have H := (field_smooth (G:=G) (n:=N)).eventually (by simp) -- actual name?
  have ht := H.mono (q:=fun p=>DifferentiableAt ℝ (fun z => FPField p.1 z) p.2) (fun p hp => (hp.comp p.2 (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp))
  rw [nhds_prod_eq] at ht
  exact ht.curry.mono (fun v h=>mem_of_mem_nhds (x:=(0 : Parameter G N)) (s:={b | DifferentiableAt ℝ (FPField v) b}) h)
lemma fpLin_colored : ∀ᶠ a : Potential G N in 𝓝 0, FPDeriv (linkCol u a) ∘L (LinearMap.toContinuousLinearMap (paramCol u (N:=N)))=(LinearMap.toContinuousLinearMap (meanCol u (N:=N))) ∘L FPDeriv a := by
  have hA : Tendsto (linkCol u (N:=N)) (𝓝 0) (𝓝 0):=by
    have e := (LinearMap.toContinuousLinearMap (linkCol u (N:=N))).continuous.tendsto (0:Potential G N)
    rw [map_zero] at e; exact e
  filter_upwards [fpfield_colored u,ready_field (G:=G) (N:=N), hA.eventually (ready_field (G:=G) (N:=N))] with a hw ha hb
  let P := (LinearMap.toContinuousLinearMap (paramCol u (N:=N)))
  let Q := (LinearMap.toContinuousLinearMap (meanCol u (N:=N)))
  have he : ((FPField (linkCol u a)) ∘ P) =ᶠ[𝓝 0] Q ∘ (FPField a) := hw
  have hb0 : HasFDerivAt (FPField (linkCol u a)) (FPDeriv (linkCol u a)) (P 0) := P.map_zero.symm ▸ hb.hasFDerivAt
  have hp : HasFDerivAt (FPField (linkCol u a) ∘ P) (FPDeriv (linkCol u a) ∘L P) 0 := hb0.comp (0:Parameter G N) P.hasFDerivAt -- ambiguity
  rw [← hp.fderiv, Filter.EventuallyEq.fderiv_eq he, (Q.hasFDerivAt.comp 0 ha.hasFDerivAt).fderiv];rfl
lemma reset_colored : ∀ᶠ a : Potential G N in 𝓝 0, resetFP (linkCol u a) ∘L (LinearMap.toContinuousLinearMap (paramCol u (N:=N))) = (LinearMap.toContinuousLinearMap (paramCol u (N:=N))) ∘L resetFP a := by
  filter_upwards [fpLin_colored u] with a he
  have hp b : FPDeriv (linkCol u a) (paramCol u b) = (meanCol u) (FPDeriv a b) := congrArg (fun h : Parameter G N →L[ℝ] (Mean G N) => h b) he
  have eq (a : Potential G N) b : bridge G N (resetFP a b) = FPDeriv a b := (bridgeEquiv G N).apply_symm_apply _
  ext1 b
  apply bridgeEquiv G N |>.injective
  exact (eq (linkCol u a) ((paramCol u) b)).trans ((hp b).trans ((congrArg ((meanCol u) ·) (eq _ b).symm).trans (color_bridge u _).symm))
end YM.Pert.First
