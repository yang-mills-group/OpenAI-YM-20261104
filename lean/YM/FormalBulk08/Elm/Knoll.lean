import YM.FormalBulk08.Elm.Mast
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Elm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E e R d D m n l r:ℕ}{o:Loc G 1}{ρ:ChartRatio G}
variable {W:Lab G K X}{F:Frame G d}{H:Hol G}{T:SectionData F} (hp:Quota F H W o D E R)(u:W.Use ρ E)(C C':Pin W.scrolls) (p:∀ x,C.N x≤C'.N x)
     (h:LocalRatio ρ)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(a:hue G)
include u h hs p
lemma pulls (i:ℕ)(he:i≤E)(r:ℕ): Totem (Dove.tide C) (fun _=>fame _) W.stub (bump targetPower) (fun x=> Lab.instory ρ a W C.N x.ups i r) (fun x=> Lab.instory ρ a W C'.N x.ups i r):= by
    have he:=Lab.weigh_all u h hs a he r; exact Totem_lift (g:=fun x:Turn C=> (⟨x.ups.toLeaf,C.N x.a,C'.N x.a,x.head,p _⟩ : Lab.meshPoint W)) (up_age C u.liable) he
lemma grasp : Wells (Dove.tide C) (W.liftF) (W.liftU) (W.liftH) ρ a W.stub W.sail (bump targetPower) (W.trail C.N) (W.trail C'.N) (fun x=> Lab.instory ρ a W C.N x.ups) (fun x=>Lab.instory ρ a W C'.N x.ups) E :=
    ⟨Lab.Freight_from u C,Lab.flight_dust u C C'.N p,fun i=>(bump_pos _ i).le, u.liable.blocks.reach (fun i:Turn C=>i.toLeaf), h,fun i=>(genu (W.V i.a) _ _ _ a h hs i.head).toStory,fun i=>(genu (W.V i.a) _ _ _ a h hs (i.head.trans_le (p _))).toStory, pulls u C C' p h hs a, fun i=>(W.V i.a).clock.adm _, Lab.barn C C' u p h hs a⟩
omit p
include hp
lemma heart (i:X)(k)(hk:W.neck i≤ k)(he:k ≤ C.N i)(x: Letter F): Qual (bornY ρ W a F T hp.horizon i (C.N i) k x) o E (W.width i k):= by
   let N:=C.N i; induction he using Nat.decreasingInduction generalizing x with
   | self=> rw [went_top a hp]; exact sectionQual F T _ x o E _
   | of_succ k he ih=>
      rw [born_walk a hp i (C.N i) k he]; unfold avenue; refine qual_larch _ _ x fun y=> ?_; let z : Turn C:=⟨⟨i,k,hk⟩,he⟩
      have H:=grasp u C C (fun _=>le_rfl) h hs a; obtain ⟨B,b,hB,V⟩:= H.carts.left.swirl; obtain ⟨A,c,hA,Q⟩:=H.carts.left.rays
      refine migrate_qual (graded W.liftF (W.trail C.N) z) (W.liftU z) a ρ (W.liftH z) _ h (H.church z) (H.pay.input z) (H.pay.output z) (H.pay.coverage z) _ (H.aV z) E ?H (V z) (Q z) (hB _) (hA _) _ _ _ (ih (by omega) y); intro e he r; obtain ⟨C,c,hC⟩:= (H.paid e he r).left; exact ⟨_,hC z⟩
-- remove unused hypotheses
lemma qualitative (i:Deck C)(x:Letter F): Qual (bornY ρ W a F T hp.horizon i.a (C.N i.a) i.b x) o E (W.width i.a i.b) := heart hp u C h hs a i.a i.b i.zone i.cap x
end YM.FormalBulk08.Elm
