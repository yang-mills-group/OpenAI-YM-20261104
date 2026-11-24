import YM.WilsonCoeffUV.Product.Connected.Derive
/-!
# Rooted two-parent join guard
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
section
open Wilson Tree AnalyticNext.QuarticMatch.Sheets Exterior
variable [Fintype α]
abbrev FleetG (α:Type*) := Layers ℝ (Cloth α)
def inertial (G:ropes Cover α α)(D P Q: FleetG α)(T: FleetG α)(k e:ℕ): Gen ℝ (Cloth α) := rime G (T k e)+ Soil.paintC G D T k e + Soil.paintC G.transpose D T k e + Soil.paintC G P Q k e+Soil.paintC G.transpose P Q k e
noncomputable def gorge (G:ropes Cover α α)(D P Q: FleetG α)(k e:ℕ): Gen ℝ (Cloth α):= match k with
 | 0=>0
 | k+1=>((k+1:ℕ):ℝ)⁻¹ • inertial G D P Q (fun h e=> if _f:h≤k then gorge G D P Q h e else 0) k e
termination_by k
omit [Fintype α] in lemma riseG (G:ropes Cover α α)(D P Q: FleetG α)(k e:ℕ): gorge G D P Q (k+1) e=((k+1:ℕ):ℝ)⁻¹ • inertial G D P Q (gorge G D P Q) k e:=by
    let g:=gorge G D P Q; let f h e:= if _f:h≤k then gorge G D P Q h e else 0; have ht A : Soil.paintC A D f k e=Soil.paintC A D g k e:=by
       unfold Soil.paintC; refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl (fun j hj=>?_); have hv:i.2≤k:=by have he:=Finset.mem_antidiagonal.mp hi; omega
       rw [show f _ _=g i.2 j.2 from dif_pos hv]
    rw [gorge]; change _ • inertial G D P Q f k e=_; unfold inertial; rw [ht,ht,show f k e=g k e from dif_pos le_rfl]
omit [Fintype α] in lemma forest_amber {U L:Type*}{P:Ten ℝ (U×L) i}{o}{d:Distance U}(h:Cork d o s A P)(he:0≤s): Amber d s A P:= by
    refine ⟨h.1,fun x=>(h.2 x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (league_le d _ fun i j=> leg_le d (stud o x) i.succ j.succ)) (by linarith))) h.1)⟩
-- rooted−rooted rill not Yields(no stroll)
variable {P Q:(n:Side)→ Gen ℝ (Co n α)}{F T:Gen ℝ (Cloth α)}{u:(n:Side)→ ropes (Site n) α α}{v: ropes Cover α α}
omit [Fintype α] in
lemma mailTree (f:Pilots u v)(p:Bends 0 (fun n=>P n (i+1)) (F (i+1)))(q:Bends 0 (fun n=>Q n (j+1)) (T (j+1))) (h:i+j=r): Paves 0 (fun n=> rill (u n) (P n) (Q n) r i j) (rill v F T r i j):=by
    subst r; obtain ⟨s,a,hs,H⟩:= f.fees; obtain ⟨t,b,ht,U⟩:=p.price; obtain ⟨z,c,hz,V⟩:=q.price; set x:=min s (min t z); have hx:=lt_min hs (lt_min ht hz)
    refine ⟨fun a b=>?_,x,_,hx,(H.and (U.and V)).mono fun n hn=> solorill_bill (hn.1.mono (min_le_left ..)) ((forest_amber hn.2.1 ht.le).mono ((min_le_right ..).trans (min_le_left ..))) (hn.2.2.mono ((min_le_right ..).trans (min_le_right ..))) hx.le rfl⟩
    simp_rw [rill_spell]; have he :=p.point (Fin.cons (b 0) (a ∘ Fin.castAdd j)); have hf:=q.point (Fin.cons (b 1) (a ∘ Fin.natAdd i)); unfold slideC at he hf; simp_rw [←comps_head] at he hf; exact ((((f.point (b 0) (b 1)).const_mul _).mul_const _ |>.mul_const _).mul he).smul hf
lemma towArbor (f:Pilots u v)(p:∀ i,Bends 0 (fun n=>P n i) (F i))(q:∀ i,Bends 0 (fun n=>Q n i) (T i)) (r:ℕ): Bends 0 (fun n=>arbor (u n) (P n) (Q n) r) (rondel v F T r):=by
   have hw (i:ℕ×ℕ)(hh:i∈Finset.antidiagonal r):=(mailTree f (p (i.1+1)) (q (i.2+1)) (Finset.mem_antidiagonal.mp hh)).swiveled.rest
   refine (Soil.Bends.sum hw).congr (Eventually.of_forall fun n=>?_); rw [Finset.sum_apply]; exact rill_reads ..
lemma tow_ravel {P Q:(n:Side)→ Layers ℝ (Co n α)}{F T:FleetG α}(f:Pilots u v)(p:∀ i j r,Bends 0 (fun n=>P n i j r) (F i j r))(q:∀ i j r,Bends 0 (fun n=>Q n i j r) (T i j r))(i j r): Bends 0 (fun n=> ravel (u n) (P n) (Q n) i j r) (Soil.paintC v F T i j r):=by
   apply leaderT; intro v hv; exact leaderT fun w hw=> towArbor f (p v.1 w.1) (q v.2 w.2) r
end
end YM.WilsonCoeffUV.Mer
