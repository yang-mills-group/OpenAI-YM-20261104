import YM.OPE.Compatible.Draft.Flint
/-!
# All joints receive one Bor: bramble upkeep
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n c f:Side}
open Wilson RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp Pilot
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial Flock Metric Glass
attribute [local instance] Gauge.frobInner
variable {i j:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {S: StepData c f} {H: Even c.val}
local notation "μ"=> even_both S.ratio H
local notation "J!"=> Rill.rollB S H
variable {A:Alps B Q i l} (Z:Bor (even_both S.ratio H) A b) (t:S.Choices) (h:S.patch.Branches S.kernel G)
abbrev Stir (S:StepData c f)(H:Even c.val):=(Tableau S H).Stand ({origin (even_both S.ratio H)}:Set _)
local notation "L!"=>Stir S H
structure Elm (A:Alps B Q i l)(S:StepData c f)(H:Even c.val)(t:S.Choices)(b:ℝ) where
    f : Keys G (Rill.rollB S H)→ℝ
    w : Keys G (Rill.rollB S H)→ℝ
    ok: f =ᶠ[𝓝 0] worldF S H t A
    up: w =ᶠ[𝓝 0] worldW S H t b A
    L (j:Stir S H) : Lid G j.Free
    Lf (j:Stir S H) : (L j).f=f∘ j.rollX
    Lw (j:Stir S H) : (L j).w=w∘ j.rollX
include h Z
lemma buoy : Nonempty (Elm A S H t b):=by
      let J:=bramble μ; let W:=StemX S H J; obtain ⟨u,hu,hU⟩:=bravePQ S H J t h; let T:= piBond S H J; let Y:= wellX S H b (G:=G); let M := hu.suite T
      have ht:Pilot.Hark (u⁻¹):=⟨hu.moving.inv,fun j=> by
           simp only [Pi.inv_apply,G.mat_inv];exact (starL' ℝ: G.Mat ≃L[ℝ] G.Mat).contDiff.contDiffAt.comp _ (hu.prices j),by rw [Pi.inv_apply,hu.zero,inv_one]⟩
      let P:= ht.suite T
      have hp : M.q=P.q.symm:= by ext1 x; apply (shoot T G.El).injective; simp [M,P,Hark.suite,Hark.run,curveW]
      obtain ⟨hx,Hw⟩:= stems J t Z hu hU h; obtain ⟨F,hF,HF⟩:=arcShape (safeF (H:=H) t h A); obtain ⟨V,hV,HV⟩:= arcShape (safeW (H:=H) (b:=b) t h A); let D:= cradle T (Z.L J) Y
      have hL(k: Stir S H): Tendsto (k.rollX (G:=G)) (𝓝 0) (𝓝 0):= by simpa using! k.rollX.continuous_of_finiteDimensional.tendsto (0:Keys G k.Free)
      have ha:Tendsto P.gradient (𝓝 0) (𝓝 0):=by simpa only [P.grad0] using! P.gradC.continuousAt.tendsto
      have hr:F ∘ W.rollX=ᶠ[𝓝 0] D.f∘ P.gradient:=by
           have ht:= ((hx.comp_tendsto ha).symm); have hh:=coil P M hp; refine (HF.comp_tendsto (hL W)).trans ?_; filter_upwards [ht,hh] with i H hb; change D.f _=worldF _ _ t A (W.rollX (M.gradient _)) at H; change _= D.f _; rw [H, show M.gradient (P.gradient i) =i from hb];rfl
      have hg: V ∘ W.rollX=ᶠ[𝓝 0] D.w∘ P.gradient:=by
           have ht:= ((Hw.comp_tendsto ha).symm); have hh:=coil P M hp; refine (HV.comp_tendsto (hL W)).trans ?_; filter_upwards [ht,hh] with i H hb; change D.w _=worldW _ _ t b A (W.rollX (M.gradient _)) at H; change _= D.w _; rw [H, show M.gradient (P.gradient i) =i from hb];rfl
      obtain ⟨w,hf,hv⟩:= newLid P M hp D (hF.comp (W.rollX.continuous_of_finiteDimensional.measurable)) (hV.comp (W.rollX.continuous_of_finiteDimensional.measurable)) hr hg
      have he(k:Stir S H):∃ g:Lid G k.Free,g.f=F∘ k.rollX∧ g.w=V∘ k.rollX:=by
           let B:= k.beenX (G:=G) W
           have ht:Tendsto B.gradient (𝓝 0) (𝓝 0):=by simpa only [B.grad0] using! B.gradC.continuousAt.tendsto
           have hc: ∀ᶠ i in 𝓝 (0:Keys G k.Free),F (k.rollX i)=w.f (B.gradient i) ∧ V (k.rollX i)=w.w (B.gradient i):=by
               filter_upwards [outing B,(hL k).eventually HF,(hL k).eventually HV,((hL W).comp ht).eventually HF,((hL W).comp ht).eventually HV] with i hx hl hh hg hc; change V (W.rollX _)=_ at hc; have he:(Tableau S H).dress (W.sweep (put (k.rollX i))) (put (k.rollX i))=put (W.rollX (B.gradient i)):=by rw [W.emits,k.rollPut,W.rollPut, hx];rfl
               rw [hf,hv,_root_.Function.comp_apply,_root_.Function.comp_apply,hl, hh, show F (W.rollX (B.gradient i)) =_ from hg,hc]; exact loft t h _ _ _ he
           exact newLid _ (W.beenX k) (show (W.beenX (G:=G) k).q=B.q.symm from Homeomorph.ext fun i=>rfl) w (hF.comp k.rollX.continuous_of_finiteDimensional.measurable) (hV.comp k.rollX.continuous_of_finiteDimensional.measurable) (hc.mono fun i hi=>hi.1) (hc.mono fun i hi=>hi.2)
      choose g hH hG using he; exact ⟨⟨F,V,HF,HV,g,hH,hG⟩⟩
end YM.OPE.Cascade.Rill
