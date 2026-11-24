import YM.FormalBulk08.Sierra.Pier
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Sierra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Orb Tundra Dove Spruce Elm
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices} {X I:Type}{E m r u l R:ℕ}{θ α:ℝ}{W:Lab G K X}
variable {Y T:X→Pot G}{ρ:ChartRatio G}{a:hue G}
variable {g δ:X→ℝ}{τ:Time X}
section
variable {P:Page X}{C:Pin P}
lemma addendum {U: Deck C→Tile (edgeL G) r}{R:Deck C→edgeL G}{η: Deck C→ℝ≥0} (h:Years P)(hp:θ<α)(hh:θ≤1)(hg:∀ i,0≤g i)(w:Gleam (Dove.tide C) r u (Turn.rad α) (fun i=>g i.a* Dove.bump θ i) (fun i=>R i.ups) (fun i=>R i.bed) (fun i=>η i.ups) (fun i=>η i.bed) (fun i=>U i.ups) (fun i=>U i.bed))
   (he:Wake ((sage C).reach (peak C)) u (fun i=>η (peak C i)) (fun i=>R (peak C i)) g (fun i=>U (peak C i))): Wake (sage C) u η R (fun i=>g i.a*Degree θ i) U:= by
   obtain ⟨B,b,t,Y⟩:= he; obtain ⟨K,k,c,hK⟩:=w
   let q(x:Turn C):= (((P.mesh x.a).block x.b).val:ℝ); have hu:Soft (Dove.tide C) q:= h.blocks.reach (fun x:Turn C=>x.toLeaf)
   let f(x:Deck C)(b:ℝ):Prop:= Knoxville (grain (fame _) (η x)) u (R x) (U x) (b*(Degree θ x*g x.a))
   have hv x:f (peak C x) (B x):= by
       have he: Degree θ (peak C x)=1:= by unfold Degree ratioR; rw [show (peak C x).a=x from rfl,show (peak C x).b=C.N x from rfl,div_self ((P.mesh x).a_pos _).ne',Real.one_rpow]
       unfold f;rw [he,one_mul];exact Y x ()
   have ht(x:Turn C)(Z:ℝ)(h:f x.ups Z): f x.bed (Turn.rad (α-θ) x*Z+ K x*q x):= by
       let V:=Degree θ x.ups;let U:=Degree θ x.bed; have hp:0<V:=ratioR_pos ..;have he:0<U:=ratioR_pos ..
       have hv:= hK x (Z*(V*g x.a)) h;apply hv.mono; change Turn.rad α x*(Z*(V*g x.a))+K x*(g x.a*V)≤ (Turn.rad _ x*Z+K x*q x)*(U*g x.a)
       have hh':Turn.rad α x*V=Turn.rad (α-θ) x*U:= adjusted _ _ _ _ _
       obtain ⟨M,hM,u,H⟩:=adjust_rate (P.mesh x.a) hh x.b (C.N x.a); have hU:V=M*U:=H;apply le_trans (le_of_eq (b:=(Z*(Turn.rad α x*V)+ K x*V)*g x.a) (by ring)); rw [hh',←mul_assoc (Turn.rad (α-θ) x*Z+K x*q x)];apply mul_le_mul_of_nonneg_right _ (hg _);rw [mul_comm Z,mul_right_comm _ U,add_mul];apply add_le_add_right
       rw [hU];have hv:= c x; calc
          _ = K x*M*U:= by ring
          _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u hv) he.le
   obtain ⟨C,c,H,Q⟩:= upward h (sub_pos.mpr hp) (f:=f) (fun i A hp B h=> hp.mono (mul_le_mul_of_nonneg_right h (mul_nonneg (ratioR_pos ..).le (hg _)))) b hv (k.times hu) (fun i Z h _=> ht i Z h);exact ⟨_,c,H,fun i _=>by dsimp only;rw [mul_comm (g i.a)];exact Q i⟩
end
variable {ε:X→ℝ≥0}{U Q:X→Tile (edgeL G) r}{o:X→edgeL G}{s:Time I}
lemma wax (p:I→X)(h:Soft s (fun i=>τ.day (p i)))(hp:Wake τ u ε o g U): Wake s u (fun i=> ε (p i)) (fun i=>o (p i)) (fun i=>g (p i)) (fun i=>U (p i)):= by obtain ⟨C,c,H,V⟩:=hp; exact ⟨_,town_fold (g:=p) h c,fun _=>H _,fun i=> V (p i)⟩
lemma waxy (p:I→X)(h:Soft s (fun i=>τ.day (p i)))(hp:Wit τ u ε o δ g U Q): Wit s u (fun i=> ε (p i)) (fun i=>o (p i)) (fun i=>δ (p i)) (fun i=>g (p i)) (fun i=>U (p i)) (fun i=>Q (p i)):= ⟨wax p h hp.1,wax p h hp.2,wax p h (rivals hp)⟩
end YM.FormalBulk08.Sierra
