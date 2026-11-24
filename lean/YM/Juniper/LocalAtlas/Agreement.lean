import YM.Juniper.LocalAtlas.Local
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Calls
/-!
 # Single rank agreement from the real `Critical` policy

 Don't infer equivalence of analytic estimator extending a map off of the
 system paid; use a germ EXACTLY with full tag for the local prescription.
 The redundant extra `n+3` in (effective) classical path orders
 buys one power in $(β^{-1/2-ε})^k$, necessary even for the pure model.
 Here the explicit cumulant is computed in canonical UV unmarked tilted
 system; no estimate on changing `α`.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis Work.G05 Shellac
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge}

section smooth
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
    {k : ℕ} {ι : Type}[Fintype ι][DecidableEq ι]
    {φ ψ : E × Poll.Body ι→ℝ}{ρ ρ' : E→ Poll.Body ι}
    {M M' : E→Matrix ι ι ℝ} (h:ρ=ᶠ[𝓝 0] ρ')(hm : M=ᶠ[𝓝 0] M')
include h hm
omit [FiniteDimensional ℝ E] in
private lemma grace_change (z:Poll.Body ι) : grace φ ψ ρ M z=ᶠ[𝓝 0] grace φ ψ ρ' M' z := by
   have ht: ∀ᶠ x in 𝓝 (0:ℝ×E), ρ x.2=ρ' x.2∧M x.2=M' x.2:= (show Tendsto (@Prod.snd ℝ E) (𝓝 0) (𝓝 0) from continuous_snd.continuousAt) (h.and hm)
   have hv:= h.self_of_nhds; have he:= hm.self_of_nhds
   filter_upwards [ht] with x ⟨hh,hM⟩; unfold grace Lantern.shade Lantern.vote Lantern.offer Lantern.visit; simp only [hv,he,hh,hM]
omit [FiniteDimensional ℝ E] in
lemma agreed : oneEra φ ψ ρ M=oneEra φ ψ ρ' M':= by
   funext i; unfold oneEra; rw [hm.self_of_nhds]; refine integral_congr_ae (Eventually.of_forall fun z=>?_); unfold coin Tensor.coeff
   rw [(((grace_change h hm z).fun_comp Real.exp).iteratedFDeriv ℝ i).self_of_nhds] -- fun_comp
end smooth

section
variable {c f:Side}{S: StepData c f} (F:Forest S.ratio)(T:Tube G S)(A:ChartRatio G)(k:S.Choices)
    (ρ: Bid.Dir G c→AxisChart G F)
local notation "X"=> Positions (Uniform.Primary c G)
local notation "Ω"=> solar F A
-- PT polynomial separate components, y,t homogeneous decomposition. retain exact C₀ including J.scale
-- effective Hessian, thermalLoop, through-β-replacement. α external.
local notation "Tp*" => blockTaylor
abbrev loopCharge (n:ℕ):= Real.log ∘ through n (oneEra (Lapis.table F k T.up T.high) (mist F A T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k))
local notation "D₁" => cedar F T ρ k
local notation "D₂" => shed F T A ρ
local notation "L₁" => loopCharge F T A k ρ
def arctic (n:ℕ) (α β:ℝ)(x:X) := Real.log (Ω β) + β*(D₁ 0+Tp* (n+3) (off D₁) x)+(D₂ α k 0+(Tp* n (off (D₂ α k))) x)+(Tp* n (L₁ n)) (gStep β,x)

-- operator norm invoice for Vk use. May need additionally zeroth determinant controls; log beam etc. Use separately.
@[mk_iff]
structure Estimate (n:ℕ) (α:ℝ)(V:ℝ) : Prop where
   core : cap (fun j=>Tensor.coeff (off (cedar F T ρ k)) j 0) (n+3) V
   kinetics : cap (fun j=>Tensor.coeff (off (shed F T A ρ α k)) j 0) n V
   jet : cap (fun j=>Tensor.coeff (loopCharge F T A k ρ n) j 0) n V

section
variable (ρ' : Bid.Dir G c → AxisChart G F) (h:ρ=ᶠ[𝓝 0] ρ')
include h
private lemma pairAgree (α:ℝ)(n:ℕ):
    D₁=ᶠ[𝓝 0] cedar F T ρ' k∧ D₂ α k=ᶠ[𝓝 0] shed F T A ρ' α k∧ loopCharge F T A k ρ n=loopCharge F T A k ρ' n:=by
    let P:=Uniform.tint G (Exterior.Body 1 c); let t : X→Bid.Dir G c:=P
    have he:P 0=0:=map_zero P; have hf:= h.comp_tendsto (show Tendsto t (𝓝 0) (𝓝 0) from he ▸ P.continuousAt)
    have ht:Lapis.orbit F ρ=ᶠ[𝓝 0] Lapis.orbit F ρ':=by
      filter_upwards [hf] with i hi using congr_arg (fun x=> (weld (Precision.Key F G)).symm ((tint G F.Free).symm x)) hi -- weld namespace
    have hh:Lapis.gram F T.up T.high ρ k=ᶠ[𝓝 0] Lapis.gram F T.up T.high ρ' k:=hf.mono fun i hi=> congr_arg (glow F T.up T.high k (t i)) hi
    refine ⟨ht.mono fun x hx=>?_,?_,?_⟩
    · unfold cedar shaft; rw [hx]
    · filter_upwards [ht,hh] with x hx hh; unfold shed hum Lantern.shade; rw [hx,hh]
    unfold loopCharge; rw [agreed ht hh]
end
section off
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f g:E→ℝ}(h:f=ᶠ[𝓝 0] g)
include h
private lemma off_coeff (k:ℕ):Tensor.coeff (off f) k 0=Tensor.coeff (off g) k 0:= by
    have hh:off f=ᶠ[𝓝 0] off g := h.mono fun i hi=> congrArg₂ (·-·) hi h.self_of_nhds
    unfold Tensor.coeff; rw [(hh.iteratedFDeriv ℝ k).self_of_nhds]
private lemma off_block (k:ℕ) : Tp* k (off f)=Tp* k (off g):= by rw [daily, daily]; exact congr_arg (through _) (funext fun i=> off_coeff h i)
end off
lemma paired (ρ' : Bid.Dir G c → AxisChart G F) (h:ρ=ᶠ[𝓝 0] ρ') (n:ℕ) (α β V:ℝ):
    arctic F T A k ρ n α β=arctic F T A k ρ' n α β ∧ (Estimate F T A k ρ n α V ↔ Estimate F T A k ρ' n α V):= by
  obtain ⟨he,hv,hh⟩:= pairAgree F T A k ρ ρ' h α n; constructor
  · ext1 x; rw [arctic,arctic,he.self_of_nhds,hv.self_of_nhds,off_block he,off_block hv,hh]
  rw [estimate_iff, estimate_iff,funext (off_coeff he),funext (off_coeff hv),hh] -- iff
end
end YM.Juniper.LocalAtlas
