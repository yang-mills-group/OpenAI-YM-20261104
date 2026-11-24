import YM.MS.Plum.Ribbons
/-!
# Terrain continuity at the prescribed rate

Three norms of lines between rays. z=0 UH orientation. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Plum
open Function Set Filter Finset MeasureTheory Real Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans
open Momentum Metric
open scoped Topology ContDiff
variable {I J E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 {G:Gauge}{z: UScale I}{U V: Rip G}{m n:ℕ}{K:Shade G}{b c:Bool}
def fade (n:ℕ): ℝ:= (n+1:ℝ)⁻¹
lemma being (n:ℕ): 0<fade n:=by unfold fade; positivity
lemma sold (n:ℕ): fade n≤1:= inv_le_one_of_one_le₀ (by simp)
lemma fading: Tendsto fade atTop (𝓝 0):=by
   unfold fade; apply tendsto_inv_atTop_zero.comp; refine tendsto_atTop_mono ?_ (tendsto_natCast_atTop_atTop (R:=ℝ)); intro i; exact le_add_of_nonneg_right zero_le_one
-- rails raise/add/sub
lemma r_add {X Y: I→ Rip G}{a:I→ℝ}(h:rib z a X)(he:rib z a Y) : rib z a (fun i=> X i + Y i):= fun m u v n=> Costs.add (h m u v n) (he m u v n)
lemma climb {X: I→ Rip G}{v w:I→ℝ}(hp:rib z v X)(he:∀ i,v i≤ w i): rib z w X := fun m i l n=> Costs.raise (hp m i l n) (Cost.of_le fun k p _=> by gcongr; exact pow_nonneg (Scale.weight_pos ..).le _; exact he k)
lemma trust {X: I→ Mob G}{v w:I→ℝ}(hp:fell z v X)(he:∀ i,v i≤ w i): fell z w X:= fun m E _ _ _ K=> (hp m E K).raise (Cost.of_le fun i _ _=> he i)
variable {F H: Mob G}{X Y:ℕ→ Mob G}{Z:ℕ→Rip G}
-- supported growth for any Form0. need stability for both to pay ocean。
structure Drift (b:Bool)(X:ℕ→Mob G)(F:Mob G): Prop where
   real : Form0 b F
   ticket n : Form0 b (X n)
   grey : fell 0 fade fun i=> X i-F
structure From (b:Bool)(Z:ℕ→ Rip G)(U:Rip G): Prop where
   price : Knot b U
   go n : Knot b (Z n)
   ops : rib 0 fade fun i=> Z i-U
lemma From.haze (h:From b Z U): rib 0 (fun _=>1) Z:= by convert! r_add (climb h.ops sold) (transport h.price.price) using 1; simp
lemma Drift.level (h:Drift b X F): fell 0 (fun _=>1) X:= by convert! fall_add (trust h.grey sold) (travel h.real.price) using 1; simp
lemma newer (h:Knot b U): From b (fun n=>twine (fade n) U) U:= ⟨h,fun n=>(tried h (fade n) (being n) (sold n)).toKnot,ribbon being sold h.price⟩
lemma realP {l:Legs (Shore G m)} (h: fell 0 fade X): Tendsto (fun i=>X i m l) atTop (𝓝 0):= by
   obtain ⟨C,hC,b,hb⟩:= Arc.ride (h m ℝ (ray l)) 0; let A:= C*(1+‖(1:ℝ)‖)^b; have hp : Tendsto (fun z:ℕ=> A*fade z) atTop (𝓝 0):= by simpa only [mul_zero] using tendsto_const_nhds (x:=A)|>.mul fading
   apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall (fun _=> norm_nonneg _)) (.of_forall (fun i=>?_)) hp; simpa only [norm_iteratedFDeriv_zero,Pi.zero_apply,abs_zero,add_zero,one_mul,fieldVal,ray_sail,A] using hb i 1
lemma lean (h: fell 0 fade fun i=>X i-F)(l:Legs (Shore G m)): Tendsto (fun i:ℕ=> X i m l) atTop (𝓝 (F m l)):= by
    convert! (realP (l:=l) h).add_const (F m l) using 1 <;> simp
lemma Drift.now (h:Drift b X F): ∀ n (l:Legs (Shore G n)), Tendsto (fun i=>X i n l) atTop (𝓝 (F n l)):=fun _ l=> lean h.grey l
lemma steak (h:Form0 b F): Drift b (fun _=>F) F:= by refine ⟨h,fun _=>h,?_⟩; simp; exact fall_zero (G:=G) (fun i=> (being i).le) -- named F
-- immediate sym ops
variable {P: Type}
lemma Drift.portQ (h:Drift b X F) {Q: Shade G}(hp:CountsD b Q)(hr: Priced Q): Drift b (fun i=>portZ Q (X i)) (portZ Q F):= by
   refine ⟨Form0.portQ Q hp h.real hr, fun n=> Form0.portQ Q hp (h.ticket _) hr,?_⟩; convert! count_price Q hr h.grey using 1; ext; simp only [portZ,Pi.sub_apply,map_sub]
lemma Drift.add (h: Drift b X F)(hv: Drift b Y H): Drift b (fun i=> X i+Y i) (F+H):= by refine ⟨h.real.add hv.real,fun i=>(h.ticket i).add (hv.ticket i),?_⟩; convert! fall_add h.grey hv.grey using 1; funext i; abel
end YM.MS.Plum
