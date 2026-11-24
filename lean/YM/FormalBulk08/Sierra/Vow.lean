import YM.FormalBulk08.Sierra.Soar
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{I X:Type}{g δ:X→ℝ}{τ:Time X}{R: Reach I}{a:I}{S:Tile I 0}{η B:ℝ}{u e:ℕ}
def spice (T:Tile I 0):ℝ:= T default
lemma icing : Knoxville R η a S B ↔ |spice S|≤ B:= by
    have he : ∀ i:chain I 0,herb R a i=0:= fun i=> Nat.eq_zero_of_le_zero (known_wide _ _ 0 (fun x y=> Nat.le_zero.mpr (by rw [show x=y from Fin.ext (by omega),R.self])))
    have hp : (∑' i,penon R a η S i)= ENNReal.ofReal ‖spice S‖:= by simp [penon,he,Gorge.shine,spice];rw [←Real.norm_eq_abs,ofReal_norm]
    change (0≤B∧ (∑' i,penon R a η S i)≤_)↔_; rw [hp]; exact ⟨fun h=>(ENNReal.ofReal_le_ofReal_iff h.1).mp h.2,fun h=>⟨(abs_nonneg _).trans h, ENNReal.ofReal_le_ofReal h⟩⟩
lemma warble {f:X→Tile (edgeL G) 0}{o:X→edgeL G}{ε:X→ℝ≥0}: Wake τ u ε o g f ↔ Faint τ g (fun i=>spice (f i)):= by
    constructor; intro h; obtain ⟨C,c,v,H⟩:=h; exact ⟨C,c,v,fun i=>icing.mp (H i ())⟩
    rintro ⟨C,c,v,H⟩; exact ⟨C,c,v,fun i _=>icing.mpr (H i)⟩
lemma glow_v {f b:X→Tile (edgeL G) 0}{o:X→edgeL G}{ε:X→ℝ≥0}: Wit τ u ε o δ g f b ↔ Calm τ δ g (fun i=>spice (f i)) (fun i=>spice (b i)):= by constructor; intro h; exact ⟨warble.mp h.1,warble.mp h.2,warble.mp (rivals h)⟩; intro h; refine ⟨warble.mpr h.aF,warble.mpr h.bF,?_⟩; exact (warble (f:=fun i=> f i-b i)).mpr h.diff
variable {P:Page X}{C:Pin P}{f b:Deck C→ℝ}{V W:Turn C→ℝ}
lemma stepful (hv:∀ i,0≤g i)(hp:Faint (qday τ C) (fun i=> g i.a) V) (h:Faint τ g (fun i=> f (peak C i))) (he:Soft τ (fun i=>(steps C i:ℝ)))(hf:∀ i:Turn C,|f i.bed| ≤ |f i.ups|+|V i|): Faint (rday τ C) (fun i=>g i.a) f:= by
    obtain ⟨L,⟨A,n,ha,H⟩,v,U⟩:=hp;let α(x:X):= A*(τ.day x)^n;have hb x:0≤α x:=mul_nonneg ha (pow_nonneg (τ.good x) _);have hc:Soft τ α:=(soft_coin _ A).times ((soft_day τ).pows n)
    obtain ⟨B,b,t,W⟩:=h; have hh x m(ht:m≥ P.ell x)(he:m≤ C.N x): let i: Deck C:= ⟨⟨x,m,ht⟩,he⟩;|f i|≤ ((C.N x-m:ℕ)*α x+B x)*g x:= by
       induction he using Nat.decreasingInduction with
       | self=> intro i; rw [Nat.sub_self,Nat.cast_zero,zero_mul,zero_add]; exact W x
       | of_succ m hi ih=>
         intro i; let z:Turn C:= ⟨⟨x,m,ht⟩,hi⟩; have hh:=ih (ht.trans (Nat.le_succ _)); apply (hf z).trans; refine (add_le_add hh ((U z).trans (mul_le_mul_of_nonneg_right (show L z ≤ α x from (le_abs_self _).trans (H z)) (hv _)))).trans ?_; rw [show C.N x-m=C.N x-(m+1)+1 by omega,Nat.cast_add_one]; change ((↑(C.N x-(m+1))*α x +B x)*g x+α x*g x)≤_;apply le_of_eq;ring
    refine ⟨_, ((he.times hc).plus b).reach (fun i:Deck C=>i.a),fun i=>add_nonneg (mul_nonneg (by positivity) (hb _)) (t _),fun i=>(hh i.a i.b i.zone i.cap).trans ?_⟩; refine mul_le_mul_of_nonneg_right (add_le_add_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?_) (hb _)) _) (hv _); exact Nat.sub_le_sub_left i.zone _
lemma steepCalm (hv:∀ i,0≤g i)(hp: ∀ i,0≤δ i)(ht: Calm (qday τ C) (fun i=>δ i.a) (fun i=>g i.a) V W)(h:Calm τ δ g (fun i=>f (peak C i)) (fun i=>b (peak C i)))(he:Soft τ (fun i=>(steps C i:ℝ)))(hf: ∀ i:Turn C,f i.bed-f i.ups=V i)(hh:∀ i:Turn C,b i.bed-b i.ups=W i): Calm (rday τ C) (fun i=>δ i.a) (fun i=>g i.a) f b := by
    have hz (f:Deck C→ℝ)(V:Turn C→ℝ)(h:∀ i:Turn C,f i.bed - f i.ups=V i)(i:Turn C):|f i.bed| ≤ |f i.ups|+ |V i|:= by
       nth_rw 1 [show f i.bed=f i.ups+ V i from (by have hx:=h i; linarith only [hx])];apply abs_add_le
    exact ⟨stepful hv ht.aF h.aF he (hz _ _ hf),stepful hv ht.bF h.bF he (hz _ _ hh),stepful (C:=C) (g:=fun i=>δ i*g i) (fun i=>mul_nonneg (hp i) (hv i)) (ht.diff) h.diff he (hz (fun i=> f i-b i) (fun i=>V i-W i) (fun i=>by rw [←hf,←hh];ring))⟩
end YM.FormalBulk08.Sierra
