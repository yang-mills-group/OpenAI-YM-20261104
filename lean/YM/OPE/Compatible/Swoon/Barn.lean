import YM.OPE.Compatible.Swoon.Bray
/-!
# mark weights mantle. Joint Borrow receipts
-/
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
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:ReadyV S he U A D L g)
variable (V:Bor H D b)(Y:Elm A S H t r) {P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
def HaloC (R:ℝ)(A:Alps K T i v)(P:ChartRatio G) (x:Bid.Dir G c × Z!):=
  ((-R)*pane X! t A.clip A.live x - springF X! A.live x.2+ taxY X! P x.2)/4
section generic
omit S
open Radial
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma arcConst (c:ℝ){f:E→ℝ}{n:ℕ}(h:ContDiffAt ℝ (↑n) f 0)(x:E): jet (c • f) n x= c * jet f n x:=by rw [jet,jet, iteratedFDeriv_const_smul_apply h,_root_.smul_apply,smul_eq_mul];ring
lemma arcAdd {f g:E→ℝ}{n:ℕ}(h:ContDiffAt ℝ (↑n) f 0)(hx:ContDiffAt ℝ (↑n) g 0)(x:E): jet (f+g) n x= jet f n x+jet g n x:=by rw [jet,jet,jet,iteratedFDeriv_add_apply h hx,_root_.add_apply,mul_add]
end generic
open Radial
include ht
lemma SwiftF (x:LK)(hy:ContDiffAt ℝ ω (pane X! t A.clip A.live) 0):
    (Y.L W!).hat P x =
    let X':=pane X! t A.clip A.live
    let v:= lamps S he H X G x
    flareTok (-(jet X' 3 v)/4) (-jet X' 4 v/4+jet (HaloC S he t r A P) 2 v+jet (looper P) 2 (prL V! G x)):=by
       let L:=lamps S he H X G; let J:=stroll S he H X; let M:=pane X! t A.clip A.live; let Y':= Y.L J; let V:=valley S he H X
       let Z:=springF X! A.live; let D:=fun x:Bid.Dir G c × Z!=> ((-r)*M x -Z x.2)/4; let K:=D ∘ L -- parser
       have hp : Y'.w=ᶠ[𝓝 0] Real.exp ∘ K:=by
            have hv:Tendsto (J.rollX (G:=G)) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using! J.rollX.continuous_of_finiteDimensional.tendsto (0:LK)
            change (Y.L J).w=ᶠ[_] _;rw [Y.Lw]; exact (Y.up.comp_tendsto hv).trans (Eventually.of_forall fun i=> (tints S he H X A t r i).trans (congr_arg (Real.exp) (by change _=D (L i); unfold D; ring))) -- maybe unfold context
       obtain ⟨hs,hJ⟩:= sophok X! A.pays; let T:= ContinuousLinearMap.snd ℝ (Bid.Dir G c) Z!; let fK:=Z ∘ T; have hT0:T 0=0:=map_zero _; have hx:ContDiffAt ℝ ω fK 0:=(show ContDiffAt ℝ ω Z (T 0) from hT0.symm ▸ hs).comp 0 T.contDiff.contDiffAt; have hf: fderiv ℝ fK 0=0:=by unfold fK; rw [fderiv_comp (0:Bid.Dir G c × Z!) (show DifferentiableAt ℝ Z (T 0) from hT0.symm ▸ hs.differentiableAt (by simp)) T.differentiableAt,hT0,show fderiv ℝ Z 0=0 from hJ]; rfl
       have Hs:D= (4:ℝ)⁻¹ • ((-r) • M-fK):=by funext y; change _= (4:ℝ)⁻¹ * ((-r)*M y-Z y.2); unfold D;ring
       have hD:ContDiffAt ℝ ω D 0:=by rw [Hs]; exact (((hy.const_smul (-r)).sub hx).const_smul (4:ℝ)⁻¹)
       have hL:L 0=0:= L.map_zero; have hK:ContDiffAt ℝ ω K 0:=(show ContDiffAt ℝ ω D (L 0) from hL.symm ▸ hD).comp _ L.contDiff.contDiffAt
       have hW: fderiv ℝ K 0=0:=by
           have hz:fderiv ℝ (M ∘ L) 0=0:=by -- from bright
                let k := hK; apply ContinuousLinearMap.ext; intro i; have hw:jet (Y.L W!).f 1 i=0:=(Y.L W!).F.base1 i; rw [riseF S _ H X t Y (by decide) i hy] at hw; unfold jet at hw; norm_num [iteratedFDeriv_one_apply] at hw
                rw [fderiv_comp _ (show DifferentiableAt ℝ M (L 0) from hL.symm ▸ hy.differentiableAt (by simp)) L.differentiableAt,hL,L.fderiv]; exact hw
           change fderiv ℝ (D ∘ L) _=0; have hp:fderiv ℝ (fK ∘ L) 0=0:=by rw [fderiv_comp _ (show DifferentiableAt ℝ fK (L 0) from hL.symm ▸ hx.differentiableAt (by simp)) L.differentiableAt,hL,hf];rfl
           have hh:D ∘ L=(4:ℝ)⁻¹ • ((-r) • (M ∘ L)- (fK ∘ L)):= Hs ▸ rfl
           let U:= M ∘ L; have hj: DifferentiableAt ℝ U 0:= (show DifferentiableAt ℝ M (L 0) from hL.symm ▸ hy.differentiableAt (by simp)).comp 0 L.differentiableAt; have hg:DifferentiableAt ℝ (fK ∘ L) 0:= (show DifferentiableAt ℝ fK (L 0) from hL.symm ▸ hx.differentiableAt (by simp)).comp _ L.differentiableAt
           rw [hh, fderiv_const_smul ?_, fderiv_sub (f:=(-r) • (M ∘ L)) (hj.const_smul (-r)) hg, fderiv_const_smul hj,hz,hp, smul_zero,sub_zero,smul_zero]; exact (DifferentiableAt.sub (f:=(-r)• U) (hj.const_smul (-r)) hg)
       dsimp only; rw [keyWarm (Y.L W!) P ht K hp hK hW,billLoop _ _ _ _ ht,riseF S _ H X t Y (by decide) x hy,riseF S _ H X t Y (by decide) x hy,neg_div]
       apply congr_arg; let φ := taxY X! P; let p:= L x; have ht1:ContDiffAt ℝ ω φ (T 0):= hT0.symm ▸ (accountV X! ht).1
       rw [show HaloC S he t r A P=D+(4:ℝ)⁻¹ • (φ ∘ T) from funext fun i=>by unfold HaloC;change ((-r)*M i-Z i.2+φ i.2)/4=D i+(4:ℝ)⁻¹ * φ i.2;unfold D;ring, arcAdd (g:=(4:ℝ)⁻¹ • (φ ∘ T)) (hD.of_le le_top) ((( (ht1.comp _ T.contDiff.contDiffAt).const_smul (4:ℝ)⁻¹ : ContDiffAt ℝ ω ((4:ℝ)⁻¹ • (φ ∘ T)) 0)).of_le le_top), arcConst _ ((ht1.comp _ T.contDiff.contDiffAt).of_le le_top)]
       have hv: jet K 2 x= jet D 2 p:=by unfold K p jet; rw [jets_linear L (hD.of_le le_top)];rfl
       have hr :jet (φ ∘ T) 2 p=jet φ 2 p.2:=by rw [hT0] at ht1; unfold jet;rw [jets_linear T (ht1.of_le le_top)];rfl
       rw [hv, show jet (φ ∘ T) 2 _= _ from hr]; unfold p φ L;ring
end YM.OPE.Cascade.Rill
