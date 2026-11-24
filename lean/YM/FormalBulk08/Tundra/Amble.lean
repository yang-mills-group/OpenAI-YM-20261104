import YM.FormalBulk08.Tundra.Lane
import YM.FormalBulk08.Spruce.Height

/-! Budget for wakes. Quantities set before L, no polynomial weight
loss in them. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Tundra
open Reef Flat Lattice Laurent Bloch Exterior Filter Function Next.Free RG Precision Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Bank Work.F03 Work.F05 Work.F08 PowerSeries
open Quire Sable Aster Dawn Wine Roof Clover Dove Castor North Spruce Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped NNReal Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G:Gauge}{K:KernelChoices}{X I:Type}{E m l e r u D R d:ℕ}{o:Loc G 1}{W:Lab G K X}{Z:Frame G d}
structure Nesting (Z:Frame G d)(D E R u:ℕ)(W:Lab G K X)(o:Loc G 1): Prop where
    width: Soft (chron W.scrolls) (fun x=> (W.windowD x)⁻¹)
    plus:d*d ≤ u
    owned: ∃ B:Leaf W.scrolls→ℝ,Soft (chron W.scrolls) B ∧ ∀ x,Buried K Z o D E R u (W.upper x) (W.lower x) (W.pat x) (W.wood x.a x.b) (B x)
lemma ticky (C:Pin W.scrolls)(h: Nesting Z D E R u W o)(M:X→ℕ): Ticket K Z o (graded W.liftF (W.trail (C:=C) M)) W.liftU E R D u (Dove.tide C) (Turn.rad (1/2)):= by
    obtain ⟨B,b,H⟩:= h.owned; refine ⟨h.plus,fun e he r hr l hl=> ⟨_, b.reach (fun i:Turn C=> i.toLeaf),fun i=>?_⟩⟩; have hh:=(H i.toLeaf).bill (graded W.liftF (W.trail M) i) (W.liftU i) rfl rfl e he r hr l hl; change OfficeK _ Z _ _ _ _ _ _ _ _ (Dove.Mulct ((W.V i.a).S.block i.b)) _ at hh;rw [mulct_step] at hh;exact hh
variable {g δ:X→ℝ}{τ:Time X}{s:Time I}
lemma lynx (p:I→X) {T:X→Studio D→Tile (edgeL G) r}(h:Soft s (fun i=>τ.day (p i)))(hp:Sigh u τ o g T): Sigh u s o (fun i=> g (p i)) (fun i=>T (p i)):= by obtain ⟨C,c,H,V⟩:=hp; exact ⟨_, town_fold (g:=p) h c,fun i=>H _,fun i=> V _⟩
lemma b_join {T S:X→ Studio D→ Tile (edgeL G) r}(h:Sigh u τ o g T)(hp:Sigh u τ o g S)(hv:Sigh u τ o (fun i=>δ i*g i) (fun i p=>T i p-S i p)): Blizzard u τ o δ g T S:= by refine ⟨h,hp,?_⟩; unfold Sigh Whey at hv; simp_rw [mul_assoc] at hv; exact hv
lemma ley (p:I→X){T S:X→ Studio D→ Tile (edgeL G) r}(h:Soft s (fun i=>τ.day (p i)))(hp: Blizzard u τ o δ g T S): Blizzard u s o (fun i=>δ (p i)) (fun i=>g (p i)) (fun i=>T (p i)) (fun i=>S (p i)):= b_join (lynx p h hp.1) (lynx p h hp.2) (lynx p h (remains hp))
variable {α θ :ℝ}{P:Page X}{C:Pin P}{T:Deck C→Studio D→Tile (edgeL G) r}
lemma veranda (h:Years P)(hp:θ<α)(hx:θ≤1)(hg:∀ i,0≤ g i) (w:Sugar o (Dove.tide C) u (Turn.rad α) (fun i=>g i.a*Dove.bump θ i) r (fun i=>T i.ups) (fun i=>T i.bed)) (he:Sigh u ((sage C).reach (peak C)) o g (fun i=> T (peak C i))): Sigh u (sage C) o (fun i=>g i.a*Degree θ i) T:= by
   obtain ⟨B,b,t,Y⟩:= he; obtain ⟨K,k,c,hK⟩:= w
   let q(x:Turn C):= (((P.mesh x.a).block x.b).val:ℝ);have hu:Soft (Dove.tide C) q:= h.blocks.reach (fun x:Turn C=> x.toLeaf)
   let f(x:Deck C)(b:ℝ):Prop:=∀ p, Knoxville (grain (fame _) 1) u (0,o) (T x p) ((b*(Degree θ x*g x.a))*‖p‖)
   have hv x:f (peak C x) (B x):= by
       have he:Degree θ (peak C x)=1:= by unfold Degree ratioR; rw [show (peak C x).a=x from rfl,show (peak C x).b=C.N x from rfl,div_self ((P.mesh x).a_pos _).ne', Real.one_rpow]
       intro p;rw [he,one_mul,mul_assoc];exact Y x p
   have ht(x:Turn C)(Z:ℝ)(h:f x.ups Z)(z:0≤Z): f x.bed (Turn.rad (α-θ) x*Z+K x*q x):=by
       let V:= Degree θ x.ups;let U:= Degree θ x.bed; have hp:0<V:= ratioR_pos ..;have he:0<U:=ratioR_pos ..
       have hv:= hK x (Z*(V*g x.a)) (mul_nonneg z (mul_nonneg hp.le (hg _))) h;intro p;apply (hv p).mono;apply mul_le_mul_of_nonneg_right _ (norm_nonneg _);change Turn.rad α x*(Z*(V*g x.a))+K x*(g x.a*V) ≤ (Turn.rad _ x*Z+K x*q x)*(U*g x.a)
       have hh : Turn.rad α x*V=Turn.rad (α-θ) x*U:= adjusted _ _ _ _ _
       obtain ⟨M,hM,u,H⟩:=adjust_rate (P.mesh x.a) hx x.b (C.N x.a); have hU: V=M*U:= H; apply le_trans (le_of_eq (b:=(Z*(Turn.rad α x*V)+K x*V)*g x.a) (by ring)); rw [hh,←mul_assoc (Turn.rad (α-θ) x*Z+K x*q x)]; apply mul_le_mul_of_nonneg_right _ (hg _);rw [mul_comm Z,mul_right_comm _ U,add_mul];apply add_le_add_right
       rw [hU]; have hv:= c x; calc
           _ = K x * M*U:= by ring
           _ ≤ _:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u hv) he.le
   obtain ⟨C,c,H,R⟩:= upward h (sub_pos.mpr hp) (f:=f) (fun i A hp B h p=>(hp p).mono (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (mul_nonneg (ratioR_pos ..).le (hg _))) (norm_nonneg _))) b hv (k.times hu) ht
   exact ⟨C,c,H,fun i p=>by dsimp only; rw [mul_comm (g i.a) (Degree θ i), ←mul_assoc]; exact R i p⟩
end YM.FormalBulk08.Tundra
