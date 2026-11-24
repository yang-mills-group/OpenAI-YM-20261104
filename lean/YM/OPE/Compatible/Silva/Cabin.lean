import YM.OPE.Compatible.Silva.Slope
import YM.OPE.Compatible.Draft.Drift
import YM.AnalyticNext.QUARTIC_MATCH.Rephase
/-!
# Ell signs. Determinant paid in finite image sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}{p:Clip}{R:PathData G}
variable (S:StepData c f) (he:Odd S.ratio.count.val)(H:Even c.val)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "Y"=> AxisChart G X!
def trainV (q:Kv) (p:(forest S.ratio he).Free):(forest S.ratio he).Free:= ⟨ferry q p.val,fun h=>p.property (by have hh:=staff_at S.ratio H he q _ h; rw [←ferry_plus μ,twinned,ferry_0] at hh; exact hh)⟩
@[simp] lemma trainW (q k:Kv)(p:(forest S.ratio he).Free): trainV S he H (q+k) p=trainV S he H q (trainV S he H k p):= Subtype.ext (ferry_plus μ q k _)
@[simp] lemma train0 (p:(forest S.ratio he).Free):trainV S he H 0 p=p:=Subtype.ext (ferry_0 _)
lemma train2 (k: Kv)(p:(forest S.ratio he).Free): trainV S he H k (trainV S he H k p)=p:=by rw [← trainW,twinned,train0]
def fernV (k:Kv): (forest S.ratio he).Free≃ (forest S.ratio he).Free:=⟨trainV S he H k,trainV S he H k,train2 S he H k,train2 S he H k⟩
def twirlF (k:Kv): Y→L[ℝ] Y:= ContinuousLinearMap.pi fun i=> if (axisK k).flip i.val.2 then -(ContinuousLinearMap.proj (trainV S he H k i)) else ContinuousLinearMap.proj (trainV S he H k i)
lemma spinF0 (k:Kv)(x:Y)(p:(forest S.ratio he).Free): twirlF S he H (G:=G) k x p= if (axisK k).flip p.val.2 then -x (trainV S he H k p) else x (trainV S he H k p):=by unfold twirlF; rw [ContinuousLinearMap.pi_apply]; split <;> rfl
lemma spinF2 (k:Kv)(x:Y): twirlF S he H k (twirlF S he H k x)=x:=by
     ext1 i; simp_rw [spinF0, train2,show (trainV S he H k i).val.2=i.val.2 from ferry_axis ..];split <;>simp
open AnalyticNext.QuarticMatch.Joint
lemma spins (k:Kv)(p:Libra.Keys G (Limb H)): shifts (axisK k) (offset k c) (cloak H p)=cloak H p:=by
     funext ⟨x,i⟩; obtain ⟨j,rfl⟩:=axisEquiv.surjective i; unfold shifts; rw [ContinuousLinearMap.pi_apply]; dsimp only; rw [axisEquiv.symm_apply_apply j]; have he:=Streamer.hoverEll H p k (x,j)
     split <;>rename_i h
     · change ((posDir j).rotate (axisK k)).neg=true at h; simp only [Step.rotate,posDir,Bool.false_xor] at h; rw [if_pos h] at he; change -cloak _ p ((ferry k (x,j)).1,coord (ferry k (x,j)).2)=cloak H p (x,coord j); simp_rw [cloak_at,Prod.mk.eta]; exact he.symm
     simp only [Step.rotate,posDir,Bool.false_xor] at h; rw [if_neg h] at he; change cloak H p ((ferry k (x,j)).1,coord (ferry k (x,j)).2)= cloak H p (x,coord j); simp_rw [cloak_at,Prod.mk.eta]; exact he.symm
lemma pullFZ (k:Kv)(x:Y): fieldF X! (twirlF S he H k x) = pull (axisK k) (offset k f) (fieldF X! x):=by
     ext1 i; let v:= ferry k i; let KX:=axisK k; let YX:= twirlF S he H k x; have hp: pull KX (offset k f) (fieldF X! x) i= if KX.flip i.2 then (fieldF X! x v)⁻¹ else fieldF X! x v:=by
         unfold pull Step.read; split
         next h=> change ((posDir i.2).rotate _).neg=true at h; rw [if_pos (by simpa only [Step.rotate,posDir,Bool.false_xor] using! h)];rfl
         next h=> rw [if_neg (by simpa only [Step.rotate,posDir,Bool.false_xor] using h)];rfl
     change (forest S.ratio he).drape (expF X! YX) i= _; rw [hp]; by_cases h:i∈ (forest S.ratio he).trunks
     · rw [show (forest S.ratio he).drape (expF X! YX) i=1 from (forest S.ratio he).on_tree _ ⟨_,h⟩,show fieldF X! x v=1 from (forest S.ratio he).on_tree _ ⟨_,staff_at S.ratio H he _ _ h⟩]; simp
     let p:(forest S.ratio he).Free:= ⟨i,h⟩; let t:=trainV S he H k p; rw [show (forest S.ratio he).drape (expF X! YX) i =_ from (forest S.ratio he).off_tree _ p,show fieldF X! x v=_ from (forest S.ratio he).off_tree _ t]; unfold expF; rw [show YX p = _ from spinF0 S he H _ x p]; change G.lieExp (if KX.flip i.2 then -x t else x t)=_; split <;> simp [*,Work.F03.exp_neg_color]
def DoubleX (k:Kv) : (Bid.Dir G c × Y)→L[ℝ] (Bid.Dir G c × Y) := ContinuousLinearMap.prodMap (shifts (axisK k) (offset k c)) (twirlF S he H k)
lemma priceDX (h:S.patch.Branches S.kernel G)(k:Kv)(t:S.Choices): (pane X! t p R) ∘ DoubleX S he H k =ᶠ[𝓝 0] pane X! t p R:=by
     let V:=fun i:Bid.Dir G c × Y=> fieldF X! i.2; have hN: Tendsto V (𝓝 0) (𝓝 1):=by
          let A := fun x:AxisChart G X!=>input G f (Stationary.pad X! x); have hp: Tendsto (A ∘ Prod.snd) (𝓝 (0:Bid.Dir G c × Y)) (𝓝 1):=by
                have hE :Continuous A:=by apply continuous_pi; intro i; unfold A; simp_rw [input_color]; fun_prop -- if not
                simpa only [A,map_zero, Prod.snd_zero,Function.comp_apply,input_zero] using! (hE.comp continuous_snd).tendsto (0:Bid.Dir G c×Y)
          simpa only [A,V, fieldF, spoolP] using! hp -- simpl manually
     filter_upwards [hN.eventually (Work.F04.prediction_germ h (S.withinChoice (axisK k) (offset k c) t) t)] with i hi
     let a:=axisK k;let b:= offset k c; change mainTerm _ _ (fieldF X! (twirlF S he H k i.2))+noiseTaylor _ (represent (shifts a b i.1)) (fieldF X! (twirlF S he H k i.2)) _=_; rw [pullFZ, rep_shifts,main_pull]; unfold noiseTaylor; rw [← offset_step S.ratio H k,S.prediction_channel h,show S.prediction (fieldF X! i.2) _=_ from hi]; exact congr_arg (mainTerm p R (fieldF X! i.2)+ · ) (energy_channel ..)
end YM.OPE.Cascade.Rill
