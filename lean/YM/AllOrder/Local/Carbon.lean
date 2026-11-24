import YM.AllOrder.Local.Render

/-!
# PURE gap stationary services can be taken at different expansion orders/period stencils

-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Local.Pure
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Shellac Vote Work.G05
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S)
    (A : ChartRatio G) (ρ σ : Bid.Dir G c→AxisChart G F) (l : S.Choices)
local notation "M" => (Uniform.Primary c G)
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "μ" => Lapis.orbit F
local notation "J" => Lapis.gram F T.up T.high
local notation "D" => table F l T.up T.high
local notation "P" => mist F A T.up

lemma t_eq {X F:Type*} [NormedAddCommGroup X][NormedAddCommGroup F] [NormedSpace ℝ X][NormedSpace ℝ F]
    {f g:X→F} (n:ℕ) (h : f=ᶠ[𝓝 0] g) : blockTaylor n f=blockTaylor n g := by unfold blockTaylor Tensor.coeff; exact Finset.sum_congr rfl fun i _=> by rw [(h.iteratedFDeriv ℝ i).self_of_nhds]

variable (h : ρ=ᶠ[𝓝 0] σ)
include h
lemma visits : μ ρ=ᶠ[𝓝 0] μ σ ∧ J ρ l=ᶠ[𝓝 0] J σ l:= by
  let g:= tint G (Exterior.Body 1 c); have hh:= (g.continuous.tendsto 0).eventually (p:=fun z=> ρ z=σ z) ((g.map_zero).symm ▸ h)
  refine ⟨hh.mono fun y hy=>?_, hh.mono fun y hy=>?_⟩
  · unfold Lapis.orbit; simp only [Uniform.station,Function.comp_apply]; change ρ (tint G (Exterior.Body 1 c) y)= _ at hy; rw [hy]
  exact congr_arg (fun a=> glow F T.up T.high l (g y) a) hy
lemma grace_same (z:Poll.Body (Precision.Key F G)) {v:ℝ} {x: Xs} (hu : μ ρ x=μ σ x) (hv : J ρ l x=J σ l x) : grace D P (μ ρ) (J ρ l) z (v,x)=grace D P (μ σ) (J σ l) z (v,x):= by
  have hx:= visits F T ρ σ l h; unfold grace Lantern.shade Lantern.vote Lantern.offer Lantern.visit; dsimp only; simp_rw [hv,hu,hx.1.self_of_nhds,hx.2.self_of_nhds]

lemma one_frame (k:ℕ) (β:ℝ) : script F T A ρ β l k=script F T A σ β l k := by
  obtain ⟨hu,hv⟩:= visits F T ρ σ l h; have h₀:=hv.self_of_nhds
  have he (i:ℕ) (z): probe D P (μ ρ) (J ρ l) i z=probe D P (μ σ) (J σ l) i z:= by
    let p:= (ContinuousLinearMap.snd ℝ ℝ Xs)
    have hx': ∀ᶠ x:ℝ×Xs in 𝓝 0, μ ρ x.2=μ σ x.2 ∧ J ρ l x.2=J σ l x.2 := ((show Continuous p from p.continuous).tendsto 0).eventually (p:=fun x => μ ρ x=μ σ x ∧ J ρ l x= J σ l x)  (hu.and hv)
    have hx : (Real.exp ∘ grace D P (μ ρ) (J ρ l) z)=ᶠ[𝓝 0](Real.exp ∘ grace D P (μ σ) (J σ l) z):= hx'.mono fun x hQ=> congr_arg Real.exp (grace_same F T A ρ σ l h z (v:=x.1) hQ.1 hQ.2)
    exact (hx.iteratedFDeriv ℝ i).eq_of_nhds
  have hm : moment D P (μ ρ) (J ρ l)=moment D P (μ σ) (J σ l) := by funext i; unfold Vote.moment Vote.raw; simp_rw [he,h₀]
  have hh : Lantern.shade (J ρ l)=ᶠ[𝓝 0] Lantern.shade (J σ l):= hv.mono fun x hx=> congr_arg (fun i=>Real.log (i:Matrix (Precision.Key F G) (Precision.Key F G) ℝ).det/2) hx
  have hH : hard F T ρ l=ᶠ[𝓝 0] hard F T σ l:= hu.mono fun _ hg=> congr_arg (fun v=>D (_,v)) hg
  have hS : soft F T A ρ l=ᶠ[𝓝 0] soft F T A σ l:= by filter_upwards [hh,hu] with i ht hx; unfold soft; rw [ht, hx,hh.self_of_nhds]
  funext x; unfold script connected aggregation; rw [t_eq _ hS, t_eq _ hH, hm, hh.self_of_nhds]
end YM.AllOrder.Local.Pure
