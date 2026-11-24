import YM.OPE.Compatible.Maestro.Timber
/-! Relative credits and printed bounds. No height comparisons between unborn clocks from other branches. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{I : Type}{l:Filter I}{T r : I→ℝ}{q:I→ℕ}{i k n b d:ℕ}
open YM.OPE Arboreal
variable (A:Allot C)(hG:G.Simple)(hT:Tendsto T l atTop)(hh:Tendsto q l atTop)(hu:Round l T (fun i=>β C (q i))) (hp:∀ᶠ i in l,0< r i)
include A hT hu
lemma coin_cost (d:ℕ)(hh:Tendsto q l atTop): Round l T (fun i=>(C.path.levels.params (q i)).columns):=by
   let x i:= (C.path.levels.params (q i)).columns; have hf(i): 1 ≤ x i:= (C.path.levels.params (q i)).columns_ge; have hx(i):0 ≤ x i:=zero_le_one.trans (hf i); exact Round.if_inv (Eventually.of_forall fun i=> zero_lt_one.trans_le (hf i)) ((hu.up.power (MergeProof.winter G d) hT).pointwise ((hh.eventually_ge_atTop (C.ref d)).mono fun i hi=>columns_save A d _ hi) (Eventually.of_forall hx)) hT (Eventually.of_forall hf)
lemma block_score : Round l T (fun i=>extent C (q i)):=by
   have hp(i):1≤extent C (q i):=one_le_two.trans (extent_two ..); exact Round.if_inv (Eventually.of_forall fun i=>zero_lt_one.trans_le (hp i)) (hu.up.pointwise (Eventually.of_forall fun i=> block_cheap A (q i)) (Eventually.of_forall fun i=>zero_le_one.trans (hp i))) hT (Eventually.of_forall hp)
include hG hp hh
lemma owed_cost (d:ℕ): Round l T (fun i=> owed C (r i) d (q i) * r i / (C.S.a (q i))^d):=by
   have hq:= stepβ A hG hT hu.up; have hv:= (Round.const one_pos hT).sum (coin_cost A hT hu d hh) hT; let f(i):=(C.path.levels.params (q i)).columns; have hh:Round l T (fun i=> (32:ℝ)*(1+f i)*β C (q i+1)*(extent C (q i))⁻¹^d):=((Round.const (by norm_num : (0:ℝ)<32) hT|>.mul hv).mul hq).mul ((block_score A hT hu).inv.power d hT)
   apply hh.adjust; filter_upwards [hp] with i hi; unfold owed; rw [C.S.a_step]; have hz:= C.path.S.a_pos (q i); have hu:= extent_two C (q i); unfold extent; change _ = _ / C.path.S.a (q i)^d; unfold f; rw [div_pow, inv_pow]; field_simp; ring
lemma repol (hK:C.ref d≤k): Round l T (fun i=> rebate C (r i) d k (q i)* (C.S.a (q i))^d / r i):=by
   let K:=‖alto C.path k d‖; have h0:0<K:= by rw [show K=_ from alto_norm ..]; exact inv_pos.mpr (pow_pos (C.S.a_pos _) _)
   let c i:= (C.path.levels.params (q i)).columns; let v i:=owed C (r i) d (q i); let s i:=(C.S.a (q i))^d; let m i:=v i*r i/s i; let p i:= β C (q i+1); let z i:= renal C.path.levels (q i); let X:= fly C.path.levels d k
   have he : Round l T p:= stepβ A hG hT hu.up; have ht:Round l T z:= ((he.power 2 hT).inv).adjust (Eventually.of_forall fun _ =>(renal_eq ..).symm); have hY:=pow_pos (C.S.a_pos k) d
   let u i := X / (64*(1+c i)*K*m i); let y i:= (z i/(16*p i))* (C.S.a k)^d
   have hh:Round l T u:=((Round.const (A.buy.system.grows d _ hK) hT).div ((((Round.const (a:=64) (by norm_num) hT).mul ((Round.const one_pos hT).sum (coin_cost A hT hu d hh) hT)).mul (Round.const h0 hT)).mul (owed_cost A hG hT hh hu hp d)))
   have hy:Round l T y:= (ht.div ((Round.const (by norm_num : (0:ℝ)<16) hT).mul he)).mul (Round.const hY hT); refine (hh.less hy hT).adjust ?_
   filter_upwards [hp] with i hi; let a':=C.S.a (q i)
   change min (u i) (y i) = min _ _ * s i / _
   have hx:s i>0:=pow_pos (C.S.a_pos _) _; have hv:0<p i:= β_pos ..
   rw [min_mul_of_nonneg _ _ hx.le, div_eq_mul_inv (min _ _),min_mul_of_nonneg _ _ ((inv_pos.mpr hi).le)]
   congr 1
   · unfold u m; change X /(_*(v i*r i/s i))=X / ((64*(1+c i)*K)*v i)*s i*(r i)⁻¹; field_simp
   unfold y badge_fee; rw [div_pow]; change z i / (16*p i)*_=z i * (r i/(16*p i))/(s i/ (C.S.a k)^d)*s i*(r i)⁻¹; field_simp
end YM.OPE.Allot
