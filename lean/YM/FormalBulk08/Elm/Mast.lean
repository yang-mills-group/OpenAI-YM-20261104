import YM.FormalBulk08.Elm.Yard
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Elm
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{X:Type}{E e R d D m n l r:ℕ}{o:Loc G 1}{ρ:ChartRatio G}
section
variable (V:Levels G) (h:∀ i,Lodge ((V.clock.op i 0).patch))(u:∀ i,(V.clock.op i 0).patch.Branches K G) (a:hue G)
    (ρ)(F:Frame G d)(T:SectionData F)(hd:d+1≤D)
-- readable beyond N just UV top entries; recurrence when m<N
lemma growL (V:Levels G)(i): 2≤(V.S.block i).val:= le_trans (show 2≤3 by decide) (V.S.block_large i)

def walkF : ℕ→ℕ→ Roof.Plaza F D
   | 0,_=>sectionY T hd
   | n+1,i => avenue F ρ a (stageHop V i (flying V n (i+1))) (h i) (u i) (growL V i) (Dove.voyage V h u ρ a n (i+1)) (walkF n (i+1))
def terrace (N i:ℕ): Roof.Plaza F D:= walkF ρ V h u a F T hd (N-i) i
lemma terrace_zero (N): Elm.terrace ρ V h u a F T hd N N= sectionY T hd:= by rw [Elm.terrace,Nat.sub_self,walkF]
lemma thickets (i N)(he:i<N): Elm.terrace ρ V h u a F T hd N i= avenue F ρ a (destination V N i) (h i) (u i) (growL V i) (Dove.model V h u ρ a N (i+1)) (Elm.terrace ρ V h u a F T hd N (i+1)):= by
    rw [Elm.terrace, show N-i=N-(i+1)+1 by omega, walkF]; rfl
end
-- lab adventures. primary books
variable (W:Lab G K X)(a:hue G)(F:Frame G d)(H:Hol G)(T: SectionData F)(ρ)(h:LocalRatio ρ)(u:W.Use ρ E)(hp:Quota F H W o D E R)

def bornY (hd:d+1≤D)(x:X):ℕ→ℕ→ Roof.Plaza F D:= Elm.terrace ρ (W.V x) (W.wood x) (W.toEmpire.bill x) a F T hd
variable {W F ρ H T}
def bornM (hd:d+1≤D)(x:X)(N i:ℕ): Tilework F := pTrain F ρ a (destination (W.V x) N i) (W.wood x i) (W.toEmpire.bill x i) (growL _ _) (Lab.saga ρ a W x N (i+1)) (bornY ρ W a F T hd x N (i+1))
lemma went_top (i N) : bornY ρ W a F T hp.horizon i N N=sectionY T hp.horizon:= terrace_zero ..
lemma born_walk (i N k)(hx:k<N): bornY ρ W a F T hp.horizon i N k= avenue F ρ a (destination (W.V i) N k) (W.wood i k) (W.toEmpire.bill i k) (growL _ _) (Lab.saga ρ a W i N (k+1)) (bornY ρ W a F T hp.horizon i N (k+1)) := thickets ρ (W.V i) _ _ a F T _ _ _ hx -- tactic
include h
variable (hs:G.Simple)(ht:T.Sound H)(hb: Bid.pop T) (C:Pin W.scrolls)
include hp hs ht hb
lemma birth (i:X)(k N)(hx:W.neck i ≤ k)(he:k≤ N): Court o F (bornY ρ W a F T hp.horizon i N k) := by
   induction he using Nat.decreasingInduction with
   | self=> rw [went_top a hp]; exact topC o F T H ht hb _
   | of_succ i' hX hi=>
      rw [born_walk a hp i N i' hX]; refine (axle F ρ a (destination (W.V i) N i') (W.wood i i') _ (growL (W.V i) i') _ _ (hi (by omega)) (genu (W.V i) (W.wood i) _ ρ a h hs hX).toStory h H hp.horizon (quota_fits hp (⟨i,i',hx⟩:Leaf W.scrolls)) ((W.V i).clock.adm _)).1
lemma mat_begins (i:X)(k N)(hx:W.neck i ≤k)(he:k<N): Colfax (slots F) (Pose.weight F) (bornM (T:=T) (W:=W) (ρ:=ρ) a hp.horizon i N k) (fun x=>heightK ((W.V i).S.block k) d (Pose.weight F x)) ∧ larch (bornY ρ W a F T hp.horizon i N k) (bornM (T:=T) (W:=W) (ρ:=ρ) a hp.horizon i N k)=(migrates a (destination (W.V i) N k) (W.wood i k) K (Lab.saga ρ a W i N (k+1)) ρ (W.toEmpire.bill i k) (growL _ _) d d) ∘ bornY ρ W a F T hp.horizon i N (k+1) := by
   have ht': Story (Lab.saga ρ a W i N (k+1)) _ := (genu (W.V i) (W.wood i) _ ρ a h hs he).toStory; let b: Leaf W.scrolls:=⟨i,k,hx⟩; have hv:= birth a h hp hs ht hb i _ N (show W.neck i≤k+1 by omega) he
   rw [born_walk a hp i N k he]; exact ⟨performed o F _ ρ a (destination (W.V i) N k) (W.wood i k) _ (growL (W.V i) k) _ H hp.horizon (quota_fits hp b) ((W.V i).clock.adm _) ht' h hv,(axle F ρ a (destination (W.V i) N k) (W.wood i k) _ (growL (W.V i) k) _ _ hv ht' h H hp.horizon (quota_fits hp b) ((W.V i).clock.adm _)).2⟩
lemma harmony (i:X)(k N)(hx:W.neck i ≤k)(he:k≤N)(s:Signed): Harmonized F s (bornY ρ W a F T hp.horizon i N k):= by
   induction he using Nat.decreasingInduction with
   | self=> rw [went_top a hp];exact harmony_top _ o _ _ _ ht hb _
   | of_succ k he ih=> rw [born_walk a hp i N k he]; have hv:= birth a h hp hs ht hb i _ N (show W.neck i≤k+1 by omega) he; exact (breadth F ρ a (destination (W.V i) N k) (W.wood i k) (W.toEmpire.bill i k) (growL _ _) _ _ (genu (W.V i) (W.wood i) _ ρ a h hs he).toStory h ((W.V i).clock.adm _) hp.horizon (quota_fits hp (⟨i,k,hx⟩:Leaf W.scrolls)) H s hv (ih (by omega))).2.2
end YM.FormalBulk08.Elm
