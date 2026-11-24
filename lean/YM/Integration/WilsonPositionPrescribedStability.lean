import YM.Integration.WilsonPositionPrescribedTariff

/-! Quantitative error in the actual registered implicit frame at the same
raw test vector. The extra parameter is the measured equation residual. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionPrescribedStability
open Function Filter Metric Set XSpace XSpace.Normalize Maxwell
open scoped Topology ContDiff
variable {G : Gauge} {d : ℕ} {A : Screen G d} (D : Fray A) (H : A.Prepared)
local notation "M" => MoveSpace G d

private def shifted (z : (D.Bag × M) × M) : M := D.itinerary (z.1.1,z.2) - z.1.2
private def anchor : (D.Bag × M) × M := ((D.opening.1,0),0)

private theorem smooth : ContDiff ℝ ω (shifted D) :=
  (D.fair.comp (contDiff_fst.fst.prodMk contDiff_snd)).sub contDiff_fst.snd

private theorem partialAt :
    fderiv ℝ (shifted D) (anchor D) ∘L ContinuousLinearMap.inr ℝ (D.Bag × M) M =
      D.delta D.opening := by
  let b := anchor D
  have h1 := (((smooth D).differentiable (by simp) b).hasFDerivAt).comp (0:M)
    (hasFDerivAt_prodMk_right b.1 (0:M))
  have h2 := ((D.fair.differentiable (by simp) D.opening).hasFDerivAt).comp (0:M)
    (hasFDerivAt_prodMk_right D.opening.1 (0:M))
  have h2' : HasFDerivAt (shifted D ∘ Prod.mk b.1) (D.delta D.opening) (0:M) := by
    have he : shifted D ∘ Prod.mk b.1 = D.itinerary ∘ Prod.mk D.opening.1 := by
      funext w
      change D.itinerary (D.opening.1,w) - 0 = D.itinerary (D.opening.1,w)
      rw [sub_zero]
    rw [he]
    exact h2
  exact h1.unique h2'

include H in
private theorem invert :
    (fderiv ℝ (shifted D) (anchor D) ∘L ContinuousLinearMap.inr ℝ (D.Bag × M) M).IsInvertible := by
  rw [partialAt]
  exact D.pin_inv H

private def recover := ((smooth D).contDiffAt (x:=anchor D)).implicitFunction (by simp) (invert D H)

private theorem chart :
    ∀ᶠ z in 𝓝 (anchor D), shifted D z = shifted D (anchor D) ↔ recover D H z.1=z.2 :=
  ContDiffAt.eventually_apply_eq_iff_implicitFunction ..

private theorem analytic : ContDiffAt ℝ ω (recover D H) (anchor D).1 :=
  ContDiffAt.contDiffAt_implicitFunction ..

/-- The original signed test frame at x differs from a trial frame v by at
most a *fixed* multiple of the actual diagnostic violation of v. -/
theorem residual {ι : Type*} {u : Filter ι} {x : ι→D.Bag} {v : ι→M}
    (hx : Tendsto x u (𝓝 D.opening.1)) (hv : Tendsto v u (𝓝 0)) :
    ∃ L : ℝ,0≤L ∧ ∀ᶠ i in u,
      ‖D.route H (x i)-v i‖ ≤ L*‖D.itinerary (x i,v i)-D.itinerary D.opening‖ := by
  let y := fun i=>D.itinerary (x i,v i)-D.itinerary D.opening
  have hxy : Tendsto (fun i=>(x i,v i)) u (𝓝 D.opening) := hx.prodMk_nhds hv
  have hy : Tendsto y u (𝓝 0) := by
    simpa only [y,Function.comp_apply,sub_self] using ((D.fair.continuous.tendsto _).comp hxy).sub
      (tendsto_const_nhds (x:=D.itinerary D.opening))
  have xy := hx.prodMk_nhds hy
  have x0 := hx.prodMk_nhds (tendsto_const_nhds (x:=(0:M)))
  have htrial : Tendsto (fun i=>((x i,y i),v i)) u (𝓝 (anchor D)) := xy.prodMk_nhds hv
  have hsolve : Tendsto (fun i=>((x i,0),D.route H (x i))) u (𝓝 (anchor D)) :=
    x0.prodMk_nhds ((D.destination H).comp hx)
  obtain ⟨L,S,hs,hl⟩ := ((analytic D H).of_le (by decide : 1≤ω)).exists_lipschitzOnWith
  refine ⟨L,L.coe_nonneg,?_⟩
  filter_upwards [htrial.eventually (chart D H),hsolve.eventually (chart D H),
    hx.eventually (D.terrain H),xy.eventually hs,x0.eventually hs] with i trial solve actual hyi h0i
  have ht : recover D H (x i,y i)=v i := trial.mp (by
    change D.itinerary (x i,v i) - (D.itinerary (x i,v i)-D.itinerary D.opening) = D.itinerary D.opening - 0
    abel)
  have ha : recover D H (x i,0)=D.route H (x i) := solve.mp (by
    change D.itinerary (x i,D.route H (x i)) - 0 = D.itinerary D.opening - 0
    rw [actual])
  have h := hl.dist_le_mul _ h0i _ hyi
  rw [ha,ht] at h
  have de : dist (x i,(0:M)) (x i,y i) = ‖y i‖ := by
    rw [Prod.dist_eq,dist_self,dist_zero_left,max_eq_right (norm_nonneg _)]
  rw [de,dist_eq_norm] at h
  exact h

end YM.Integration.WilsonPositionPrescribedStability

