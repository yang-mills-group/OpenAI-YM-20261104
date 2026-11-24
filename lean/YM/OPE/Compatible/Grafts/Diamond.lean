import YM.OPE.Compatible.Grafts.Wail
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
local notation "Pz"=>pane X! t A.clip A.live
variable (X:FibreRep S he U t A g b)
include h
lemma PaneCo (x y:K! × Z!)(q:Site c→ G.El)(hA:(tor c).dress q (put x.1)=put y.1)(hp:(vital S he).dress q (put x.2)=put y.2): Pz y=Pz x ∧ springF X! A.live y.2=springF X! A.live x.2:=by
      let I:Site f→G.El:= q ∘ S.ratio.parent
      have hx:= (Mar_ord ..).mp (compassV S he x y q hp); rw [frameReal,frameReal] at hx; change Lattice.gauge I _= _ at hx
      have hv:Lattice.gauge (I ∘ S.ratio.embed) (represent x.1)=represent y.1:=by rw [show I ∘ S.ratio.embed=q from funext fun i=> by unfold I; simp only [Function.comp_apply,Ratio.embed_parent]]; exact (Mar_ord ..).mp hA
      simp only [pane,score,springF,uncurry]; rw [← hx, ← hv, caring S h.1.cover, Work.F05.loop_gauge A.pays,Work.F05.mainTerm_gauge A.pays]; exact ⟨rfl,rfl⟩
lemma booths : Fiber.Pursue X.L (tor c) (vital S he):=by
      constructor
      · intro u hp; funext i; unfold Score.dress; change u _*1*(u _)⁻¹=1; rw [mul_one]; exact mul_inv_eq_one.mpr (cstV _ hp ..)
      intro a b u hh; have ht:=hh.jobs.law; have hx:=hh.forks.law; have hu:Tendsto a (𝓝 0) (𝓝 0):= (show a 0=0 from Prod.ext hh.jobs.gx hh.forks.gx) ▸ (hh.jobs.hX.prodMk hh.forks.hX |>.continuousAt |>.tendsto); have hs:Tendsto b (𝓝 0) (𝓝 0):= (show b 0=0 from Prod.ext hh.jobs.gy hh.forks.gy) ▸ (hh.jobs.hY.prodMk hh.forks.hY|>.continuousAt |>.tendsto)
      constructor
      · filter_upwards [ht,hx,hu.eventually X.meter, hs.eventually X.meter] with i h1 h2 h3 h4; rw [Function.comp_apply,h3,Function.comp_apply,h4,(PaneCo S he U t h (a i) (b i) (u i) h1 h2).1]
      filter_upwards [ht,hx, hu.eventually X.serves, hs.eventually X.serves] with i h1 h2 h3 h4; rw [Function.comp_apply,h3,Function.comp_apply,h4]; unfold OreA; obtain ⟨he,hL⟩:= PaneCo S he U t h (a i) (b i) (u i) h1 h2; rw [he,hL]
lemma hikeQ {p:ScriptJ U!}(hp:(tor f).Marbles p)(hs:G.Simple)(ht:LocalRatio P): (tor c).Marbles (X.L.predicts P (p ∘ ribz S he)):=by
      obtain ⟨e⟩:= colorAvail _ hs; let k:=Unit; let W:= Keys G Unit; let s:W→L[ℝ] ℝ:= (PiLp.proj 2 (fun (_:G.ColorIndex)=>ℝ) e) ∘L ContinuousLinearMap.proj (R:=ℝ) (); let u:k→G.Color:=fun _=>toLp 2 fun _=>1
      exact Fiber.ArchRise ht (booths S he U t h X) u s rfl (irruption S he p hp)
-- H call from Mark
omit h
lemma Flux (H:Even c.val){p:ScriptJ K!}(hp:(tor c).Marbles p): (Pond H).Marbles (p ∘ cloak H):=by
    let F:= cloak H (G:=G); refine ⟨fun i=> (hp.toll i).compLinear F.toLinearMap,fun {x y s} h=>?_⟩; let X:= F ∘ x; let Y:=F ∘ y; let u(i:ℝ):= s i ∘ crumb H; have he:(tor c).Track X Y u:=by
         refine ⟨F.contDiff.contDiffAt.comp _ h.hX,F.contDiff.contDiffAt.comp _ h.hY,?_,?_,h.law.mono fun i ht=>?_,fun i=> h.chart _⟩
         · unfold X; rw [Function.comp_apply,h.gx,map_zero]
         · unfold Y; rw [Function.comp_apply,h.gy,map_zero]
         apply (Mar_ord ..).mpr; rw [show represent (X i)= _ from cloak_e H _, show represent (Y i)= _ from cloak_e H _,← ht]; exact (coat_gauge H ..).symm
    apply (hp.honors he).congr' _ EventuallyEq.rfl; filter_upwards with t; change (p _).atK _-(p _).atK _= (p (F (_•_))).atK _ - (p (F (_ • _))).atK _ ; rw [map_smul,map_smul];rfl
end YM.OPE.Cascade.Rill
