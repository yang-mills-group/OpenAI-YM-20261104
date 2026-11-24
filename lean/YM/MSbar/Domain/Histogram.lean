import YM.MSbar.Domain.Event
import YM.MSbar.Grid.Euclidean
/-! User calls in continuation. All elementary fields model a bar scalar component or a hat-vector,
all antifields likewise. Don't reduce polynomial dimensions of coherent tensors at any truncation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Domain
open Dim Symbol Super Loops MeasureTheory Function Set Filter
open scoped Topology BigOperators Classical ContDiff
variable {C:Type} {m n j : ℕ}
structure Edition (C: Type) where
    parity : C → Bit
    vector : C → Prop
    active : Finset C
namespace Edition
variable (W : Edition C)
def binary (W : Edition C)(m:ℕ): Token C m→ Bit := fun i=> W.parity i.1
def members (W:Edition C) (m:ℕ): Finset (Token C m):= W.active.biUnion fun i=> (index (W.vector i) m).image (fun a=>(i,a))
lemma mem {x:C}{t:Hat m}: (x,t)∈ W.members m↔ x∈W.active ∧ t∈index (W.vector x) m:= by simp [members]
lemma sum {E:Type*} [AddCommMonoid E] {f:Token C m→E}: ∑ v∈ W.members m,f v= ∑ c∈W.active,∑ b∈ index (W.vector c) m,f (c,b):=by
    unfold members;rw [Finset.sum_biUnion]; apply Finset.sum_congr rfl; intro c _; rw [Finset.sum_image]; exact InjOn.mono (Set.subset_univ _) (fun i _ j _ h=> congr_arg Prod.snd h)
    intro i h j k l; refine Finset.disjoint_left.mpr ?_; intro x hx hh; obtain ⟨y,_,rfl⟩:= Finset.mem_image.mp hx; obtain ⟨b,_,e⟩:= Finset.mem_image.mp hh; exact l (congr_arg Prod.fst e.symm)
theorem lattice (m:ℕ): Nonempty (Snap (Mom m) volume) := by obtain ⟨h⟩:= Snap.euclidean (2*2); obtain ⟨g⟩:=Snap.euclidean (2*m); exact h.prod g
end Edition

-- payload predicates including at nonzero and zero integer dimensions, depending on U
abbrev Functionals (C:Type) := Record (Words C)
variable {U:Set ℂ} {W : Edition C}
abbrev Polar (W:Edition C) (f:Words C m→ℂ):Prop:= ∀ (x:C) (p: Mom m) (u v : Words C m), One (W.vector x) (fun y : Hat m=>f (u++((x,y),p)::v))
variable {d:Bit} {F G : Functionals C}
structure Full (U:Set ℂ)(j:ℕ)(W:Edition C)(d:Bit)(F:Functionals C): Prop where
   licensed: Eligible U j (arena C) F
   quiet (t:ℂ): t∈U→ ∀ m:ℕ,Quiet (F t m)
   colors (t:ℂ): t∈U→∀ m,Polar W (F t m)
   span (t:ℂ): t∈U→ ∀ m:ℕ, Homogeneous (lift (W.binary m)) d (F t m)

abbrev Links (C:Type):= ℂ→∀ m,Line (Token C m) (Mom m)
-- For marks which may be treated as spectators outside `active`, parity and symbol/pol requirements on all
-- colors remain in place, if padding unused function values. Useful when link-type for linear substitution in
-- kinetic transport (no compact support there and with external heuristic mark moment continuity).
abbrev Here : ℕ→ Type:= fun m=> Mom m × (Hat m × Hat m)
def home : Site Here := momentum.prod (Site.moving.prod Site.moving)
def lines (L:Links C) (a b:C): Record Here:= fun z i p=> L z i (a,p.2.1) (b,p.2.2) p.1
variable {L:Links C}
structure Pilot (U:Set ℂ)(j:ℕ)(W:Edition C)(d:Bit)(L:Links C):Prop where
   cost (a b:C): Eligible U j home (lines L a b)
   parity (a b:C): W.parity a+W.parity b≠d → ∀ z∈U,∀ m:ℕ,∀ v:Here m,lines L a b z m v=0
   uniformL (a b:C):∀ z∈U,∀ m:ℕ,∀ p q, One (W.vector a) fun t:Hat m=> lines L a b z m (p,(t,q))
   uniformR (a b:C):∀ z∈U,∀ m:ℕ,∀ p q, One (W.vector b) fun t:Hat m=> lines L a b z m (p,(q,t))
namespace Pilot
variable (h: Pilot U j W d L)
include h
lemma pace {z:ℂ}(hz:z∈U): Pace (W.binary m) (W.members m) d (L z m):= by
    intro a ha b hb v h'; exact not_not.mp fun he=> h' (h.parity a.1 b.1 he z hz m (v,a.2,b.2))
-- assembly estimates
lemma applies {E : Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](a b:C)(g:E→Here m)(hg:g.HasTemperateGrowth):
    Bet U j (fun p:ℂ×E=> lines L a b p.1 m (g p.2)):=by
    have hx : HasTemperateGrowth (Prod.snd ∘ g):= tame_projR.comp hg
    have he : home.plot g:= ⟨(moment_plot _).mpr (tame_projL.comp hg),⟨tame_projL.comp hx,tame_projR.comp hx⟩⟩
    exact (h.cost ..).ev _ _ he
lemma visit {x:ℂ} (hx:x∈U)(a b:Token C m): (L x m a b).HasTemperateGrowth:=by
    let V(v: Mom m):=(v,(a.2,b.2)); exact (h.applies a.1 b.1 V (tame_pair (by fun_prop : HasTemperateGrowth (fun x:Mom m=>x)) (HasTemperateGrowth.const _))).cost.slice hx
end Pilot
def Band (U:Set ℂ)(L:Links C)(c:ℝ): Prop := ∀ z∈U, ∀ m:ℕ,∀ a b, Vanish c (L z m a b)
lemma supported (h: Pilot U j W d L) {c} (hp:Band U L c) {z:ℂ}(hz:z∈ U): Supported (L z m) (W.members m) :=
    ⟨fun a b _ _ => (h.visit hz a b).1.continuous,Metric.closedBall 0 c,isCompact_closedBall ..,fun a _ b _ x hx=>mem_closedBall_zero_iff.mpr (le_of_not_gt fun h=>hx (hp z hz m a b x h))⟩
end YM.MSbar.Domain
