import YM.OPE.Compatible.Grafts.Diamond
/-!
# Ordinary and quotient paths. Poles
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)
local notation "X!"=> forest S.ratio he
local notation "Z!" => AxisChart G X!
local notation "K!" => Bid.Dir G c
local notation "U!" => Bid.Dir G f
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable {P:ChartRatio G}(ht:LocalRatio P)
variable (X:FibreRep S he U t A g b)
local notation "F!"=> pane X! t A.clip A.live
local notation "Y"=> HaloC S he t b A P
local notation "Tk"=> Adhesion.Curling X.L.f (X.L.wSign P)
open JetS
abbrev rum (b:ℝ)(x:K!×Z!) := (-b)*pane X! t A.clip A.live x-springF X! A.live x.2+taxY X! P x.2
include h ht
lemma gumbar (x:K! ×Z!)(hs:G.Simple):
    Adhesion.Curling X.L.f (X.L.wSign P) x= flareTok (-jet F! 3 x) (-jet F! 4 x+4*jet Y 2 x):=by
      let u:K!×Z!→ℝ:=rum S he t (A:=A) (P:=P) b; let p:= pane X! t A.clip A.live; let t':=jackpot P (forest S.ratio he).Free; let w:=X.L.wSign P
      have hx:ContDiffAt ℝ ω p 0:= (viewer t h.2.1).origin; have hh:Y = (4:ℝ)⁻¹ • u:=funext fun q=>by unfold HaloC u rum; simp only [Pi.smul_apply,smul_eq_mul];ring
      let P':=ContinuousLinearMap.snd ℝ K! Z!; let V:=springF X! A.live; let T:= taxY X! P; have hz:u=((-b) • p-V ∘ P')+(T∘P'):=rfl; have hA:=sophok X! A.pays; have hv:=accountV X! ht; have hu : ContDiffAt ℝ ω (V∘P') 0:=(show ContDiffAt ℝ ω V (P' 0) from hA.1).comp (g:=V) 0 P'.contDiff.contDiffAt; have h₁: ContDiffAt ℝ ω (T ∘ P') 0:= (show ContDiffAt ℝ ω T (P' 0) from hv.1).comp _ P'.contDiff.contDiffAt; have hK:= ((hx.const_smul (-b)).sub hu); have h₂: ContDiffAt ℝ ω u 0:=hz ▸ hK.add h₁
      let Z:=u+ fun (_: K! ×Z!)=> t'; have hS: w=ᶠ[𝓝 0] Real.exp∘ Z:=by
           have hp:Tendsto P' (𝓝 0) (𝓝 0):=P'.map_zero ▸ P'.continuous.tendsto 0
           filter_upwards [X.serves, hp.eventually (parW (I:=(forest S.ratio he).Free) P ht)] with i hi hk; unfold w Fiber.wSign; rw [Pi.mul_apply, hi,show Chart.jacobian P i.2=_ from hk,Function.comp_apply,←Real.exp_add]; -- hp hi: OreA S
           change _=Real.exp (u i+t'); unfold u rum; congr 1; rw [add_assoc];rfl
      have hb: fderiv ℝ u 0=0:=by rw [hz,fderiv_add (f:=(-b) • p-V ∘ P') (hK.differentiableAt (by simp)) (h₁.differentiableAt (by simp)), fderiv_sub (f:=(-b) • p) ((hx.const_smul (-b)).differentiableAt (by simp)) (hu.differentiableAt (by simp)),fderiv_const_smul (hx.differentiableAt (by simp)), fderiv_comp _ ((show ContDiffAt ℝ ω V (P' 0) from hA.1).differentiableAt (by simp)) P'.differentiableAt,fderiv_comp _ ((show ContDiffAt ℝ ω T (P' 0) from hv.1).differentiableAt (by simp)) P'.differentiableAt,map_zero,show fderiv ℝ V 0=0 from hA.2,show fderiv ℝ T 0=0 from hv.2, show fderiv ℝ p 0=0 from pegZ S he U t h hs]; simp
      have hpZ : ContDiffAt ℝ ω Z 0:= h₂.add contDiffAt_const; have hZ: fderiv ℝ Z 0=0:=by unfold Z; rw [fderiv_add (h₂.differentiableAt (by simp)) (differentiableAt_const _),hb,fderiv_const_apply,add_zero]
      have hF(i:ℕ)(hi:0 < i):jet X.L.f i x=jet p i x:=by unfold jet; have hh: X.L.f=ᶠ[𝓝 0] p- fun _=> p 0:=X.meter; rw [(hh.iteratedFDeriv ℝ _).eq_of_nhds,iteratedFDeriv_sub_apply (hx.of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hi),Pi.zero_apply,sub_zero]
      have ht1: jet w 1 x=0:=by unfold jet; rw [iteratedFDeriv_one_apply,hS.fderiv_eq,fderiv_comp _ Real.differentiableAt_exp (hpZ.differentiableAt (by simp)),hZ]; simp
      have hr2: jet w 2 x=w 0*jet u 2 x:=by rw [show jet w 2 x=jet (Real.exp∘Z) 2 x from (by unfold jet; rw [(hS.iteratedFDeriv ℝ _).eq_of_nhds]),jetExp2 Z x hpZ hZ,hS.eq_of_nhds, show jet Z 2 x= _ from (show jet Z 2 x=jet u 2 x from (by unfold Z jet;rw [iteratedFDeriv_add_apply (f:=u) (h₂.of_le le_top) contDiffAt_const,iteratedFDeriv_const_of_ne (by decide)];simp))];rfl
      have hw:w 0≠0:= (X.L.signPay ht).ne'; rw [hh,arcConst (4:ℝ)⁻¹ (h₂.of_le le_top)]; unfold Adhesion.Curling Adhesion.GateT; apply eta
      · change (w 0)⁻¹ * (jet w 0 x*1)=1; rw [jet_zero,mul_one]; exact inv_mul_cancel₀ hw
      · change (w 0)⁻¹ * (jet w 0 x * (-jet X.L.f 3 x)+ jet w 1 x*1)+0*_= -jet p 3 x; rw [ht1,hF 3 (by decide),jet_zero]; field_simp; ring
      change (w 0)⁻¹*(jet w 0 x*(-jet X.L.f 4 x+(jet X.L.f 3 x)^2/2)+ jet w 1 x*_+jet w 2 x*1)+ 0*_+0*_ = -jet p 4 x+ 4*((4:ℝ)⁻¹*_)+ (-jet p 3 x)^2/2;rw [ht1,hr2, hF 4 (by decide),hF 3 (by decide),jet_zero]; field_simp;ring
end YM.OPE.Cascade.Rill
