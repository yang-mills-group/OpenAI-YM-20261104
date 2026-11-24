import YM.FormalBulk08.Dove.Harp

/-! Define READ windows and honor economy changes. `Pin` each itinerary fixes
N,N' by family; get uniform by instantiating with all top choices, at fixed
preparation (scouts). -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X I:Type} {P:Page X}
-- need soft adapters
lemma town_fold {s:Time X}{t:Time I}{g:I→X}(e:Soft t (fun i=>s.day (g i))){B:X→ℝ}(h:Soft s B): Soft t (fun i=>B (g i)):= by obtain ⟨C,n,h,V⟩:= h; exact ((soft_coin t C).times (e.pows n)).below (fun i=> (V _).trans (le_abs_self _))
lemma Cost_lift {s:Time X}{t:Time I}{g:I→X}(e:Soft t (fun i=>s.day (g i))){V:X→Type}{r:ℕ}{K:∀ x,Tile (V x) r}{σ:X→ℝ}{R: ∀ x, Reach (V x)}(h:Cost s R σ K): Cost t (fun i=>R (g i)) (fun i=> σ (g i)) (fun i=> K (g i)):= by obtain ⟨C,c,H⟩:=h; exact ⟨_,town_fold e c,fun i=> H (g i)⟩
lemma Dust_lift {s:Time X}{t:Time I}{g:I→X}(e:Soft t (fun i=>s.day (g i))){V:X→Type}{r:ℕ}{K:∀ x,Tile (V x) r}{σ δ:X→ℝ}{R: ∀ x, Reach (V x)}(h:Dust s R σ δ K):Dust t (fun i=>R (g i)) (fun i=>σ (g i)) (fun i=>δ (g i)) (fun i=>K (g i)):=by obtain ⟨C,c,h,H⟩:=h; exact ⟨_,town_fold e c,fun i=>h (g i),fun i=> H (g i)⟩
lemma Totem_lift {s:Time X}{t:Time I}{g:I→X}(e:Soft t (fun i=>s.day (g i))){V:X→Type}{r:ℕ}{K M:∀ x,Tile (V x) r}{σ δ:X→ℝ}{R:∀ x,Reach (V x)}(h:Totem s R σ δ K M): Totem t (fun i=>R (g i)) (fun i=>σ (g i)) (fun i=>δ (g i)) (fun i=>K (g i)) (fun i=>M (g i)):= ⟨Cost_lift e h.left,Cost_lift e h.right, Dust_lift e h.nebula⟩
lemma Leaf.plume {S: Schedule}(i:ℕ): Real.log ((S.block i).val:ℝ)≤ (S.block i).val := by
   have h: 0 < ((S.block i).val:ℝ):= by positivity
   have ht:= Real.log_le_sub_one_of_pos h; linarith
lemma Years.over (h:Years P): Soft (chron P) (fun i=>(chron P).day (stageFoot P i 1)):=by
    obtain ⟨B,b,H⟩:=h.distance; refine ((soft_coin (chron P) B).times ((soft_day _).plus h.blocks)).below (fun i=> ?_)
    rw [abs_of_nonneg ((chron _).good _)]; apply le_trans (H i.a (i.b+1) i.b i.zone (Nat.le_succ _)); unfold sowing; rw [Schedule.scale_succ,add_sub_cancel_left]
    exact (mul_le_mul_of_nonneg_left (add_le_add_right (Leaf.plume _) _) b).trans (le_abs_self _)

def turnPage (P:Page X)(g:I→X):Page I:= ⟨P.mesh ∘g,P.ell ∘g,P.age ∘g⟩
def turnLeaf (P:Page X)(g:I→X)(x: Leaf (turnPage P g)):Leaf P:= ⟨g x.a,x.b,x.zone⟩
lemma Years.turn (h:Years P)(g:I→X): Years (turnPage P g) := by
    obtain ⟨B,b,H⟩:= h.distance; exact ⟨⟨B,b,fun i=>H (g i)⟩, h.blocks.reach (turnLeaf P g)⟩
-- Local budgets on arbitrary chosen window position
structure Pin (P:Page X) where
   N:X→ℕ
   land:∀ x,P.ell x ≤ N x
structure Deck {X:Type} {P:Page X} (C:Pin P) extends Leaf P where
   cap:b ≤ C.N a
structure Turn {X:Type}{P:Page X}(C:Pin P) extends Leaf P where
   head:b < C.N a
variable {C:Pin P}
def sage (C:Pin P): Time (Deck C):= (chron P).reach (·.toLeaf)
def tide (C:Pin P): Time (Turn C):=(chron P).reach (·.toLeaf)
abbrev wideA (i:Leaf P):= ((P.mesh i.a).block i.b).val
abbrev Turn.bed (x: Turn C): Deck C:= ⟨x.toLeaf,x.head.le⟩
abbrev Turn.ups (x:Turn C): Deck C:= ⟨stageFoot P x.toLeaf 1, x.head⟩
def Turn.rad (θ:ℝ)(x:Turn C):ℝ:= ringR (P.mesh x.a) θ x.b (x.b+1)
abbrev peak (C:Pin P)(x:X):Deck C:= ⟨⟨x,C.N x,C.land x⟩,le_rfl⟩
lemma down_age (C:Pin P): Soft (tide C) (fun i=> (sage C).day i.bed):= soft_day _
lemma up_age (C:Pin P)(h:Years P): Soft (tide C) (fun i=> (sage C).day i.ups):= Soft.reach h.over (fun i:Turn C=> i.toLeaf)
def Degree (θ:ℝ)(i: Deck C): ℝ:=ratioR (P.mesh i.a) (C.N i.a) i.b θ
def bump (θ:ℝ)(i:Turn C):ℝ:= Degree θ i.ups
lemma bump_pos (θ:ℝ)(i: Turn C): 0<bump θ i:= ratioR_pos ..
-- adapter for deck, sub
end YM.FormalBulk08.Dove
