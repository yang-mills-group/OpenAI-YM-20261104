import YM.MS.Dial.Arc
/-!
# Negative time domination in continuum frame.Purpose: separated continuity; also grants actual PT regulator statements on sequences of profile samples converging to fixed physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane -- alias
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{a b:ℤ}{l:Filter I} {r:ℕ}
set_option quotPrecheck false
local notation "Υ" => east ( frameF I v ) false
local notation "Ω"=> ( Υ ).price
open Wire Belt
variable {F: Glade G I}
local notation "R"=> frameF I v
lemma boxX (X:Glade G I)(h: Came R false X )(w:Legs ( Lane4 G )) : ∃ (m:ℝ→ℝ), IntegrableOn m (Set.Iic 0) ∧ ∀ x q,q ≤ 0→ ‖X x q w‖≤ m q := by
    obtain ⟨C,hC,k,hk⟩:=(( h.1.pick 0 ) ℝ ( ray w ) (fun i=>Bool.noConfusion i) (fun i=>Bool.noConfusion i) ).norm_cost; obtain ⟨A,hA,h⟩:= capped zero_lt_one k; let r:ℝ:=1+|v|; let T:= C*(r*2)^k; have hT:0<T:= by unfold T r; positivity
    refine ⟨fun s:ℝ=> (T*A)*exp ( (1/2:ℝ)*s ), (integrableOn_exp_mul_Iic (a:= (1/2:ℝ)) (by norm_num) 0).const_mul (T*A),fun x s hs=>?_⟩
    let t:=slotL (v:=v) hs x; obtain he:= hk t 1 trivial; dsimp only at he; rw [ show birthTar R 0 t=exp s from (by simp only [birthTar,pow_zero,mul_one,t,slotL,tstart]) ] at he; let q:ℤ:= pitch (ray w); have hu : (Ω).full.cheap t (1:ℝ)≤ r*2*(1+-s):= by
       unfold Scale.full Scale.weight; dsimp only; rw [ norm_one,mul_one,length_Ω,size_Ω,abs_of_nonpos hs ]; have ht:= exp_le_one_iff.mpr hs; change ( r*(1+-s) )*(1+exp s)≤_; have hq:r≥1:= by unfold r; simp
       rw [mul_right_comm r 2]; exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) (by linarith))
    apply le_trans (b:= ‖Chart (plug X) ( ray w ) t (1:ℝ)‖) ( le_of_eq (by unfold Chart; rw [ray_sail]; rfl) ) (he.trans ?_);
    let hL: ℝ:= exp s; have hm:hL≤1:= exp_le_one_iff.mpr hs; have hx:0<hL:= exp_pos _; have hS : 0≤ (Ω).full.cheap t (1:ℝ):= zero_le_one.trans ((Ω).full.one_le _ _ trivial); have hv := hS.trans hu; apply le_trans (b:= C*(r*2*(1+-s))^k * ( 1*hL )) (by gcongr; rw [length_Ω hs x]; exact zpow_le_one₀ hx hm (pitch_nn _)) ?_
    obtain he := h (-s) (by linarith); calc
      _ = T*((1+-s)^k*exp ( -(1:ℝ)*(-s) )):= by unfold T hL; rw [mul_pow]; ring_nf
      _ ≤ _:= (mul_le_mul_of_nonneg_left he hT.le).trans_eq (by rw [← mul_assoc, neg_mul_neg])
variable {p:I}{q:ℤ}[l.IsCountablyGenerated]
lemma pastH (h:Came R false F)(ht:t≤0)(w:Legs (Lane4 G))(hv:∀ s,s≤0→ tend l p (fun i=>F i s w)) : tend l p (fun i=> river F i t w):= by
    unfold river; obtain ⟨m,hM,hm⟩:= boxX F h w; let M:= volume.restrict (Set.Iic t); have he:∀ᵐ x:ℝ ∂M,x≤0:= (ae_restrict_mem measurableSet_Iic).mono fun _ h=> le_trans h ht
    apply tendsto_integral_filter_of_dominated_convergence m (Eventually.of_forall fun i=> (h.1.mood.walk i w (fun i=>Bool.noConfusion i)).aestronglyMeasurable ) (Eventually.of_forall (fun i=>he.mono fun p hp=>hm _ _ hp)) ( hM.mono_set (Iic_subset_Iic.mpr ht) ) (he.mono hv) -- last syntax
end YM.MS.Dial
