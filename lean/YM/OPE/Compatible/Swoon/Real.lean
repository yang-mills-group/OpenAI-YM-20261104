import YM.OPE.Compatible.Swoon.Barn
/-!
# Halo-y journals. arbitrary chart. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:ReadyV S he U A D L g)
variable (V:Bor H D b)(Y:Elm A S H t r) {P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
lemma Serum : fderiv ℝ (swornY D.live (n:=c)) 0=0:=by
     let f:=turnSeries D.live.loop (m:=c); let L:= extX G c; have hu :swornY D.live (n:=c)=f ∘ L:=by
          funext i; have hz: input G c (L i)=represent i:=congr_arg represent ((arm _ _ _).apply_symm_apply i); change Precision.loop D.live _=Precision.loop D.live (input G c (L i));rw [hz]
     have he:= turns_analytic D.live.loop D.pays.width D.pays.two (m:=c); have hz:fderiv ℝ f 0=0:=by
        have hp := (rays_jet he _).1 (turns_low _ D.pays.width D.pays.two) 1 (by decide); ext i; exact (show (iteratedFDeriv ℝ 1 f 0) ![i]= 0 from DFunLike.congr_fun hp _)|> fun h0=>by rw [iteratedFDeriv_one_apply] at h0; exact h0
     rw [hu,fderiv_comp _ (show DifferentiableAt ℝ f (L 0) from L.map_zero.symm ▸ he.differentiableAt) L.differentiableAt,L.map_zero,hz];rfl
-- use original Eu Pert.Halo
abbrev haloP (p:ℝ)(D:Alps K T d u): Bid.Dir G c→ℝ:= ((4:ℝ)⁻¹) • ((-p) • (swornV D.clip D.live)+(-1:ℝ) • swornY D.live)
include ht
lemma SwiftD (hS:G.Simple)(x:P!):
     (V.L X).hat P x=
     let p:=rayS H X G x
     let M:=swornV D.clip D.live (n:=c)
     flareTok (-(jet M 3 p)/4) (-jet M 4 p/4+ jet (haloP b D) 2 p+jet (looper P) 2 x):=by
          dsimp only; let p:=rayS H X G x; let M:=swornV D.clip D.live (n:=c); let W:= haloP b D (c:=c); let P':= rayS H X G; let D':=swornY D.live (n:=c); let U:=W ∘ P'
          have hp: (V.L X).w =ᶠ[𝓝 0] Real.exp ∘ U:=by
               rw [V.serves]; have hv : Tendsto (X.rollX (G:=G)) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! X.rollX.continuous_of_finiteDimensional.tendsto (0:P!)
               exact (V.t.comp_tendsto hv).trans (Eventually.of_forall fun i=>congr_arg Real.exp (show -b*(M (P' i) /4)-D' (P' i)/4=((4:ℝ)⁻¹) * (-b*M (P' i)+(-1:ℝ)*D' (P' i)) by ring))
          have hm:ContDiffAt ℝ ω M 0:=(chartK D.live D.clip c D.pays).1; have hy:ContDiffAt ℝ ω D' 0:=(tubesY D.live D.clip c D.pays).1; have hz:ContDiffAt ℝ ω W 0:=(((hm.const_smul (-b)).add (hy.const_smul (-1:ℝ))).const_smul ((4:ℝ)⁻¹)); have h0:P' 0=0:=P'.map_zero; have h':ContDiffAt ℝ ω U 0:=(show ContDiffAt ℝ ω W (P' 0) from h0.symm ▸ hz).comp _ P'.contDiff.contDiffAt; have hh:fderiv ℝ U 0=0:=by
              unfold U; rw [fderiv_comp (0:P!) (show DifferentiableAt ℝ W (P' 0) from h0.symm ▸ hz.differentiableAt (by simp)) P'.differentiableAt,h0]; suffices hw:fderiv ℝ W 0=0 by rw [hw];rfl
              change fderiv ℝ ((4:ℝ)⁻¹ • ((-b) • M+(-1:ℝ) • D')) 0=0
              rw [fderiv_const_smul ?_, fderiv_add (f:=(-b) • M) (g:=(-1:ℝ) • D') ((hm.differentiableAt (by simp)).const_smul _) ((hy.differentiableAt (by simp)).const_smul _), fderiv_const_smul (hm.differentiableAt (by simp)),fderiv_const_smul (hy.differentiableAt (by simp)), show fderiv ℝ M 0=0 from dawnV D hS, show fderiv ℝ D' 0=0 from Serum]; simp
              exact ((((hm.differentiableAt (by simp)).const_smul (-b))).add ((hy.differentiableAt (by simp)).const_smul (-1:ℝ)) : DifferentiableAt ℝ ((-b) • M+(-1:ℝ) • D') 0)
          rw [keyWarm (V.L X) P ht U hp h' hh, riseR H X V (by decide), riseR H X V (by decide)]; simp only [neg_div]; apply congr_arg (flareTok (-(jet M 3 p / 4))); rw [show jet U 2 x= _ from (show jet U 2 x=jet W 2 p by unfold jet U; rw [jets_linear P' (hz.of_le le_top)];rfl)]
lemma bandC (s:ℝ)(hp:ContDiffAt ℝ ω (pane X! t A.clip A.live) 0)(x: Bid.Dir G c × Z!): ContDiffAt ℝ ω (HaloC S he t s A P) 0∧
    jet (HaloC S he t s A P) 2 x= (-s*jet (pane X! t A.clip A.live) 2 x-jet (springF X! A.live) 2 x.2+ jet (taxY X! P) 2 x.2)/4:=by
      let D:= pane X! t A.clip A.live; let A':=taxY X! P; let B':=springF X! A.live; let Q:=ContinuousLinearMap.snd ℝ (Bid.Dir G c) Z!; let p:= (-s) • D; let u:= (-1:ℝ) • (B' ∘ Q); let v:= A' ∘ Q; have hz: HaloC S he t s A P=(4:ℝ)⁻¹ • (p+u+v):=by funext i; change (-s*D i-B' i.2+A' i.2)/4=(4:ℝ)⁻¹ * ((-s*D i+(-1:ℝ)*B' i.2)+A' i.2);ring
      have hP:ContDiffAt ℝ ω p 0:=hp.const_smul (-s); have hv:ContDiffAt ℝ ω A' 0:= (accountV X! ht).1; have hu:ContDiffAt ℝ ω B' 0:=(sophok X! A.pays).1; have hf:ContDiffAt ℝ ω (B' ∘ Q) 0 := (show ContDiffAt ℝ ω B' (Q 0) from Q.map_zero.symm ▸ hu).comp _ Q.contDiff.contDiffAt; have hA:ContDiffAt ℝ ω u 0:= hf.const_smul (-1:ℝ); have hQ:ContDiffAt ℝ ω v 0:=(show ContDiffAt ℝ ω A' (Q 0) from Q.map_zero.symm ▸ hv).comp _ Q.contDiff.contDiffAt; rw [hz]; refine ⟨((hP.add hA).add hQ).const_smul (4:ℝ)⁻¹,?_⟩
      rw [arcConst _ (f:=p+u+v) (((hP.add hA).add hQ).of_le le_top),arcAdd (f:=p+u) ((hP.add hA).of_le le_top) (hQ.of_le le_top), arcAdd (hP.of_le le_top) (hA.of_le le_top), show jet v 2 x=jet A' 2 x.2 from ?_, show jet p 2 x=(-s)*jet D 2 x from arcConst (-s) (hp.of_le le_top) x, show jet u 2 x=(-1:ℝ)*jet (B' ∘ Q) 2 x from arcConst (-1:ℝ) (hf.of_le le_top) x, show jet (B' ∘ Q) 2 x=jet B' 2 x.2 from ?_]; unfold A' B' D;ring
      all_goals first | unfold jet; rw [jets_linear Q (hu.of_le le_top)];rfl | unfold v jet; rw [jets_linear Q (hv.of_le le_top)];rfl
end YM.OPE.Cascade.Rill
