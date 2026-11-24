import YM.OPE.Compatible.Pendulum.Purse
/-!
# General Round budgets (alternation not required)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Pixel
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open Mirror Deb Allot Lights Wave Relay Cells CutOrder Arcade
open scoped Topology BigOperators Classical
variable {X I : Type} [PartialOrder X][OrderBot X][Fintype X](D:Origin X){U:Finset X}
   {G:Gauge}{C:Family G}{L:Extraction.Order}(A:Allot C)(hG:G.Simple){φ:Filter I}{s:I→X→ℝ}{T z c a:I→ℝ}
    {q:I→ℕ}(b d J :ℕ){η:ℝ}
variable (h:Glowing D U φ T s η) {u:X}
set_option quotPrecheck false
local notation "Y!"=> fun i=>schedule C b η (s i)
local notation "p"=> fun i=>aperture D C b d η (T i) (s i)
local notation "ν"=>fun i x=>min (p i x) (Y! i x)
local notation "K"=> fun i=> Y! i u-1
local notation "v!"=>fun i=>81*(course C b J i+1)
include hG A h
lemma gleans (hv:u∈U): Tendsto (fun i=>schedule C b η (s i) u-1) φ atTop∧ Round φ T (fun i=>β C (K i)) ∧ Round φ T (fun i=>C.S.a (K i)/s i u):=by
   let j i:= schedule C b η (s i) u; let k i:=j i-1; have hf:= lives D hG A h b hv; have hj : ∀ᶠ i in φ,k i+1=j i:= (hf.eventually_gt_atTop 0).mono fun i hi=> Nat.sub_add_cancel hi
   have hb:Round φ T (fun i=>β C (k i)):= Round.if_inv (Eventually.of_forall fun _=> β_pos ..) ((thermal D hG A h b hv).up.pointwise (hj.mono fun i hi=>(β_increases hG).monotone ((Nat.le_succ _).trans hi.le)) (Eventually.of_forall fun _=> (β_pos ..).le)) h.ray (Eventually.of_forall fun _=> (β_one ..).le)
   have hn:Tendsto k φ atTop:= tendsto_atTop.mpr fun n=>by filter_upwards [hf.eventually_gt_atTop n] with i hi; change n< j i at hi; change n ≤ j i-1; omega
   refine ⟨hn,hb,((stands D hG A h b hv).mul (block_score A h.ray hb)).adjust ?_⟩
   filter_upwards [hj] with i hi; change C.S.a (j i)/_ *_= _; rw [show j i= _ from hi.symm]; rw [C.S.a_step]; have hb:0< extent C (k i):=zero_lt_two.trans_le (extent_two ..); change (C.S.a _/extent C _)/_*extent C _=_; field_simp; rfl
lemma taxes_pay {H:ℕ}(hp:0 < H)(hq:Tendsto q φ atTop)(ht:Round φ T (fun i=>β C (q i))) : ∃ z e:I→ℝ,Round φ T z∧ Round φ T e∧ ∀ᶠ i in φ, Expenses C D U (Y! i) (ν i) v! b (z i)∧ Taxes C D U (Y! i) (ν i) v! (q i) H b (e i) ∧ z i ≤1∧ e i ≤1:=by
   obtain ⟨z,hZ,hU⟩:= fund D hG A h b d J
   let k' i:=q i+1; let a i:= Lights.valve C H b (v! (q i)) (q i); let c i:= Lights.valve C H b (v! (k' i)) (k' i)
   have he(i:ℕ) : v! i ≤81*(5*J+1)*(1+gapL C b i):=by unfold course; nlinarith only [Nat.zero_le J, Nat.zero_le (gapL C b i)]
   have ht': Round φ T (fun i=> β C (k' i)):= stepβ A hG h.ray ht.up
   have ha:Round φ T a:= valve_price A hG hq h.ray ht.up hp (Eventually.of_forall fun _=>he _)
   have hc:Round φ T c:=valve_price A hG (tendsto_atTop_mono (fun i=> Nat.le_succ (q i)) hq) h.ray ht'.up hp (Eventually.of_forall fun _=>he _)
   let r i:= sash C (k' i)/2; have h':Round φ T r:= (priced_sash h.ray ht').div (Round.const zero_lt_two h.ray); let e' i:=min (min (min (z i) (a i)) (c i)) (r i); have hE:Round φ T e':= ((hZ.less ha h.ray).less hc h.ray).less h' h.ray
   have hw(i:ℕ):1 ≤ v! i:= Nat.succ_le_of_lt (show 0< v! i from Nat.mul_pos (by norm_num) (Nat.zero_lt_succ _)); refine ⟨z,e',hZ,hE,?_⟩
   filter_upwards [hU,hE.pos] with i hi hx; have hr:e' i ≤ min (min (z i) (a i)) (c i):= min_le_left ..; have hp':e' i ≤ min (z i) (a i):= hr.trans (min_le_left ..); have hQ:e' i ≤ z i:=hp'.trans (min_le_left ..); refine ⟨hi,⟨hx,⟨hw _,hw _⟩,min_le_right ..,?_,fun v hv=>hQ.trans (hi.rating v hv)⟩,hi.small,hQ.trans hi.small⟩ -- field names
   intro j hj hh; obtain hh'|hh': j=q i ∨ j=q i+1:=(by omega); exact (hh'.symm) ▸ hp'.trans (min_le_right ..); exact (hh'.symm) ▸ hr.trans (min_le_right ..)
end YM.OPE.Arboreal.Pixel
