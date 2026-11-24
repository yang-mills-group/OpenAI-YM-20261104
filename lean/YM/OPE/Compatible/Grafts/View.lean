import YM.OPE.Compatible.Grafts.Micro
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
open Flume.Script Shell Char Pilot Essay Arc
open Asymptotics
open Planned.PrimaryIntegral295.Carrier
section jump
local notation "μ"=> Tested.germ
lemma marFort (x:ℕ→ScriptJ K!)(s:ℕ→Side)(hx:Tendsto (fun i=>(s i).val) atTop atTop)(p:ScriptJ K!)(k:ℕ)(A:ℝ)(hA:0 ≤ A)(hp:∀ i,(tor c).Marbles (x i))(h:p.B)(hz:∀ i:ℕ,∀ t:Phase,∀ v:K!, Mold ((x i v).seq t.val) ((p v).seq t.val) (A*(1+‖spool G c v‖)^k) (s i) 1): (tor c).Marbles p :=by
        refine ⟨h,fun {v u f} hv=>?_⟩; let y(t:ℝ):=t⁻¹ • v t; let w(t:ℝ):= t⁻¹ • u t; have he:Gael y:= Gael.walk v hv.hX hv.gx; have hV: Gael w:= Gael.walk u hv.hY hv.gy
        have hh(i):mine (x i ∘ y)=mine (x i ∘ w):=by
             have hk:Fitted (x i ∘ y):= Fitted.arose y (x i) he (hp i).toll; have hM:Fitted (x i∘ w):= Fitted.arose w (x i) hV (hp i).toll; exact ((hk.take).clash ((hp i).honors hv)).equality hM.take
        let a:K!→L[ℝ] deck (Shade G) c:=spool G c|>.toContinuousLinearMap; have h₁(v:K!)(t:Phase): Tendsto (fun i=> (x i v).seq t.val) atTop (𝓝 ((p v).seq t.val)):=by
             let f(i:ℕ):ℝ:= (s i).val; let P:=A*(1+‖spool G c v‖)^k; apply tendsto_sub_nhds_zero_iff.mp; apply tendsto_zero_iff_norm_tendsto_zero.mpr; apply squeeze_zero (g:=fun i=>P/f i) (fun _=>norm_nonneg _) _ (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hx)); intro i; rw [le_div_iff₀ (show 0 < f i from Nat.cast_pos.mpr (s i).pos),mul_comm]; have ht:= hz i t v; simpa only [Mold,Shell.grain,pow_one] using! ht
        have h₂(i:ℕ)(j:Phase):∃ c:ℝ,0≤c∧∀ v:K!,‖(x i v).seq j.val- (p v).seq j.val‖ ≤ c*(1+‖a v‖)^k :=by
             refine ⟨A,hA,fun v=> (le_mul_of_one_le_left (norm_nonneg _) (show (1:ℝ) ≤ Shell.grain (s i) 1 from ?_)).trans (hz i j v)⟩; simp only [Shell.grain,pow_one]; exact_mod_cast (s i).pos
        let t:= p ∘ y; let u':=p∘w; have ht (j:Phase): (mine t).seq j.val=(mine u').seq j.val:=by
             have hZ(j:Phase):=impax a x p (fun i=>(hp i).toll) h k h₂ h₁ w hV j; apply tendsto_nhds_unique (impax a x p (fun i=>(hp i).toll) h k h₂ h₁ y he j); convert! hZ j using 1; funext i;rw [hh]
        have hEq:mine t=mine u' := JetS.eta _ _ (ht 0) (ht 1) (ht 2); have hp:= Fitted.take (p:=t) (Fitted.arose y p he h); have hh:= Fitted.take (p:=u') (Fitted.arose w p hV h); rw [hEq] at hp; change (fun i:ℝ=> (t i).atK i-(u' i).atK i)=O[μ]_; apply (hp.sub hh).congr' ?_ Filter.EventuallyEq.rfl; filter_upwards with i; change (jur _ i-_)-(jur _ i-_)=(t i).atK i-(u' i).atK i; unfold jur; ring
variable {p':Patch}{K':KernelChoices}
structure Era (U:Boxes G p' K')(A:Alps K T i v):Prop where
      bind: ∃ k:ℕ,∀ n:Side,k ≤ n.val→ ∃ L g, licensed (subStud p' K' n) p'.odd_side U A.clip A.live L A.sky g
def Pathic (d:ℕ)(X:Muse G):Prop:= ∀ (n:Side)(x:Site n),(tor n).Marbles (inkM X d x)
end jump
end YM.OPE.Cascade.Rill
