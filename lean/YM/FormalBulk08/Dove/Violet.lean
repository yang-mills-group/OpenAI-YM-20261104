import YM.FormalBulk08.Dove.Province

/-! Norm and freight adapters. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Dove
open Lattice Laurent Bloch RG Precision Wilson Orb Reef City Filter Function Series Wick Jets Stationary Lotus Shore Lava Gorge Mesa Cork Wine Flat Glide Bank Work.F08 Next.Free Chapel Rift Aster
open scoped Topology ENNReal BigOperators Classical
variable {X:Type}{G:Gauge}{K:KernelChoices}{ρ:ChartRatio G}{E:ℕ}(W:Lab G K X){C:Pin W.scrolls}
namespace Lab
-- choose F independent of N. avoid `toLeaf` reduc cost with abbrevs
abbrev liftF (x:Turn C) := destination (W.V x.a) (C.N x.a) x.b
abbrev liftU (x:Turn C) := W.wood x.a x.b
lemma liftH (x:Turn C): (W.liftF x).patch.Branches K G:= W.toEmpire.bill _ _
abbrev trail (M:X→ℕ)(x:Turn C):= location (W.V x.a) (M x.a) (x.b+1)
abbrev sail (x:Turn C):= W.windowD x.toLeaf
abbrev stub (x:Turn C):= W.windowU x.toLeaf
abbrev billU (E:ℕ)(x:Turn C):= W.riseFee x.toLeaf E
abbrev billD (E:ℕ)(x:Turn C):= W.rootFee x.toLeaf E
lemma dole (M:X→ℕ)(x:Turn C): graded W.liftF (W.trail M) x=destination (W.V x.a) (M x.a) x.b:=rfl
variable {W}(h:Use W ρ E)
include h
lemma Freight_from (C:Pin W.scrolls): Freight (W.liftF (C:=C)) W.liftU ρ K (tide C) W.stub W.sail E := by
   have hv i:= W.turn_whose h ((i:Turn C).toLeaf); have hh:= h.post.reach (fun i: Turn C=> i.toLeaf)
   have hb : Soft (tide C) (fun i=> Real.exp (8* W.sail i)):= (soft_coin (tide C) (Real.exp 8)).below fun i=> by simp_rw [abs_of_pos (Real.exp_pos _)]; refine Real.exp_monotone ?_; have he: W.sail i≤1:= (h.cost i.toLeaf).trans (window_le ..);linarith
   exact ⟨fun i=>(hv i).ship,fun i=>h.zero (stageFoot W.scrolls i.toLeaf 1), fun i=>h.zero i.toLeaf,hb,(W.residency h.liable).reach (fun i:Turn C=>i.toLeaf), (W.board_price h.liable).reach (fun i:Turn C=> i.toLeaf),(W.slots_price h.liable).reach (fun i: Turn C=> i.toLeaf),fun e _ he r _ hr=>⟨_,hh,fun i=>(hv i).hail _ he _ hr⟩,fun e _ he r _ hr=>⟨_,hh,fun i=>(hv i).cone _ he _ hr⟩⟩
lemma grip (i: Turn C)(M N :ℕ)(he:i.b<N)(hu:N ≤ M): charge (W.V i.a) N M i.b K (W.sail i) (W.callL i.toLeaf ρ E) (W.liftU i) (W.liftH i) := (W.turn_whose h i.toLeaf).goods _ _ _ _ he hu rfl rfl _
lemma flight_bill (C:Pin W.scrolls)(M:X→ℕ)(p:∀ i,C.N i ≤ M i): Honest (W.liftF (C:=C)) W.liftU K G (W.trail M) (tide C) W.sail W.liftH := by
    have ht (x:Turn C) := grip h x (M x.a) (M x.a) (x.head.trans_le (p _)) le_rfl; have hv (x:Turn C):=(W.turn_whose h x.toLeaf).plus.le; have he:= h.post.reach (fun i:Turn C=> i.toLeaf); exact ⟨⟨_,he,hv,fun i=>(ht i).mean⟩,⟨_,he,hv,fun i=>(ht i).single⟩⟩
lemma flight_dust (C:Pin W.scrolls)(M:X→ℕ)(p:∀ i,C.N i ≤ M i): Canvas (W.liftF (C:=C)) W.liftU W.liftH (tide C) (W.trail C.N) (W.trail M) W.sail (bump targetPower):= by
   obtain hx:= flight_bill h C M p; obtain ht:=flight_bill h C C.N (fun _=>le_rfl); have hp i:= (grip h (i:Turn C) (M i.a) _ i.head (p _)); have hv (x:Turn C):=(W.turn_whose h x.toLeaf).plus.le; have he:= h.post.reach (fun i:Turn C=> i.toLeaf)
   exact ⟨⟨ht.swirl,hx.swirl,_,he,hv,fun i=>(hp i).bend⟩,⟨ht.rays,hx.rays,_,he,hv,fun i=>(hp i).line⟩⟩
lemma punctual (C:Pin W.scrolls)(M:X→ℕ)(p:∀ i,C.N i ≤ M i): TermPrice (W.liftF (C:=C)) W.liftU (W.trail M) (tide C) W.stub W.sail (Turn.rad (1/2:ℝ)) G K E:= by
    have ht (i: Turn C):= W.turn_quota h i.toLeaf; have hb (i: Turn C):= W.turn_quota h (stageFoot _ i.toLeaf 1); have hx:= h.post.reach (fun i:Turn C=>i.toLeaf); have he:= h.structural.reach (fun i:Turn C=>i.toLeaf)
    have hU: Soft (tide C) (W.billU E):= by
        let g:Turn C→ Leaf W.scrolls:=fun i=> stageFoot W.scrolls i.toLeaf 1
        have ht:Soft (tide C) (fun i=> (chron W.scrolls).day (g i)):= up_age C h.liable; exact town_fold (s:=chron W.scrolls) (g:=g) ht h.structural
    refine ⟨⟨_,_,he,he,fun i=> (ht i).price,fun i=>(ht i).seat _,fun m hm hy=> ⟨_,hx,fun i=>?_⟩⟩,fun e he m hm hz=> ⟨_,hU,fun i=>(hb i).value _ he _ hm hz⟩⟩
    have hr:= (W.turn_whose h i.toLeaf).parts (W.V i.a) i.b (M i.a) (i.head.trans_le (p _)) rfl rfl (W.liftH i) m hm hy
    rw [mulct_step] at hr; exact hr
end Lab
end YM.FormalBulk08.Dove
