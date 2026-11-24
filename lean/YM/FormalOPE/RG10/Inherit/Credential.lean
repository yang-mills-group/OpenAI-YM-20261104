import YM.FormalOPE.RG10.Inherit.Atelier
/-!
 # Cost pullback: Hessian validity independent of size in conclusion, not in gap constants.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}{I J K : Type}[Fintype I][Fintype J][Fintype K]
abbrev Spending (G:Gauge)(I:Type):= Configuration G I → ℝ

-- Basic finite stationary support assumptions. For entire hierarchy g. `nonnegative`
-- prevents spurious cancellations. Measurable but need not be globally continuous; contour.
structure Component (a:Spending G I):Prop where
 meas : Measurable a
 nn (u): 0 ≤ a u
 center : a 1=0
 smooth : ContDiffAt ℝ ω (a ∘ expLinks G I) 0
structure Credential (a:Spending G I) : Prop extends Component a where
 cut (S : Set (Configuration G I))(h:S∈ 𝓝 1):∃ C:ℝ,0<C ∧ ∀ u,a u<C → u∈ S
 strict (u: Direction G I): u≠0 → 0<jet (a ∘ expLinks G I) 2 u
omit [Fintype I] in
lemma compactAid {a:Spending G I}(ha:Continuous a)(hn:∀ u,u≠1→0<a u) (S : Set (Configuration G I))(h:S∈ 𝓝 1): ∃ C:ℝ,0<C ∧ ∀ u,a u<C → u∈S:= by
 obtain ⟨t,ht,hop,ho⟩:=mem_nhds_iff.mp h
 by_cases hv:tᶜ.Nonempty
 · obtain ⟨u,hu,hb⟩:= hop.isClosed_compl.isCompact.exists_isMinOn hv ha.continuousOn
   refine ⟨a u, hn u (fun e=> hu (e.symm ▸ ho)),fun x hx=>?_⟩
   apply ht; by_contra HH; exact (not_le.mpr hx) (hb HH)
 exact ⟨1,one_pos,fun x _=> ht (by by_contra hx; exact hv ⟨x,hx⟩)⟩ -- hh unused

variable {a:Spending G I}
lemma Component.centered (C:Component a): Stationary (a ∘ expLinks G I):= stable C.smooth (by simp [C.center]) (fun x=> C.nn _)
lemma Credential.boundedBy (C:Credential a) : ∃ c:ℝ,0<c ∧ ∀ u,c*‖u‖^2≤ jet (a ∘ expLinks G I) 2 u:= quadratic_min _ (fun u h=> C.strict u h)

variable (X: Atelier G I J)
lemma Component.pull {a:Spending G J}(C:Component a): Component (a ∘ X.placement) where
 meas:= C.meas.comp X.placement.measurable
 nn _:= C.nn _
 center:= by simp [X.origin,C.center]
 smooth := by
   apply ((show ContDiffAt ℝ ω (a ∘ expLinks G J) (X.prepare 0) from X.prepare_zero.symm ▸ C.smooth).comp (0:Direction G I) X.prepare_form).congr_of_eventuallyEq
   exact (X.prepare_apply.symm).fun_comp a
lemma Credential.pull {a:Spending G J}(C:Credential a): Credential (a ∘ X.placement) where
 toComponent:= C.toComponent.pull X
 cut S h:= by
    have hh: X.placement.symm ⁻¹' S ∈ 𝓝 1:= (show ContinuousAt X.placement.symm 1 from X.rev.dHere).preimage_mem_nhds (by rw [X.dOrigin]; exact h)
    obtain ⟨b,hb,h⟩:= C.cut _ hh; refine ⟨b,hb,fun u hu=> ?_⟩
    have hx: X.placement.symm (X.placement u)∈ S:= h (X.placement u) hu; simpa only [MeasurableEquiv.symm_apply_apply] using hx
 strict u hu:= by
    have he:= X.prepare_apply.symm.fun_comp a
    rw [same_jet (k:= (a ∘ X.placement) ∘ expLinks G I) (l:=(a ∘ expLinks G J) ∘ X.prepare) he, second X.prepare_form X.prepare_zero C.smooth ?_]
    · exact C.strict _ (X.solo u hu)
    exact (show IsLocalMin (a ∘ expLinks G J) 0 from Filter.Eventually.of_forall (fun x=> by change a (expLinks G J 0)≤_; rw [identity_zero,C.center]; exact C.nn _)).fderiv_eq_zero
end YM.FormalOPE.RG10.Inherit
