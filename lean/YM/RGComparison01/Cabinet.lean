import YM.RGComparison01.Ribbon
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Vista
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Nil

/-!
# Catalog of MUSIC+chosen E across compatible period

 Lots drawn identically. arity, diameter and budgets left to Virtue. Avoid
 any recoding of predicates on the old durations. -/

set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Deck Stellar Mint
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M n b : ℕ} {K : Teller G}
variable {s u U a W : ℝ} {X : ConnectedActivityE6.Target G K} {o:Target.Order G W} {p:RG.BudgetPoint}

/-- Abstraction for unmarked optional heads (before pricing). -/
structure Cabinet (ι : Type) {S : StepData c f} {T : Tube G S} {R : RG.Rep G f}
    (I : Cash W s a L₀ X o U T R) (r : ℕ) where
  job : ι ↪ LogIndex c f
  site : ι → Site c
  sails (v:ι) : site v ∈ I.supportP (.inr (.inr (.inl (job v)))) ∧ I.supportP (.inr (.inr (.inl (job v)))) ⊆ neighbors r (site v)
  hold : ι → ℕ
  finite (k:ℕ) : {i : ι | hold i ≤ k}.Finite

variable {ι χ : Type} {R : RG.Rep G f} {R' : RG.Rep G F}
section gen
variable {S : StepData c f} {T : Tube G S} {r : ℕ} {I : Cash W s a L₀ X o U T R}
namespace Cabinet
def ink (E : Cabinet ι I r) : ι ↪ Head S := ⟨fun i=>.inr (.inr (.inl (E.job i))),fun _ _ h=> E.job.injective (Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h)))⟩
abbrev foot (E : Cabinet ι I r) := I.supportP ∘ E.ink
lemma penned (E : Cabinet ι I r) (i:ι): E.site i∈E.foot i ∧ E.foot i⊆ neighbors r (E.site i):= E.sails i
end Cabinet
end gen

namespace Drawing
variable {S : StepData c f} {T : Tube G S} {I : Cash W s a L₀ X o U T R} (E : Ribbon R n)
local notation "B" => radiusB s
abbrev Lyric (_I : Cash W s a L₀ X o U T R) := { i : Music c f // verse R.path i≤radiusB s }
abbrev Count (I : Cash W s a L₀ X o U T R) := Lyric I ⊕ E.Node
variable (I)
lemma payer (i : Mint.Music c f) (b:ℕ) : Mint.note i ≠ .inl (.inl b) := by rcases i with i|i|i|i<;>simp [Mint.note]

def scorecard : Count E I ↪ LogIndex c f:=
    ⟨Sum.elim (fun i=>Mint.note i.val) (fun i=> .inl (.inl i.val)), fun i j h=> by
      rcases i with i|i<;> rcases j with j|j
      · exact congr_arg Sum.inl (Subtype.ext (Mint.record h))
      · exact (payer _ _ h).elim
      · exact (payer _ _ h.symm).elim
      exact congr_arg Sum.inr (Subtype.ext (Sum.inl_injective (Sum.inl_injective h)))⟩
lemma tucks (k:ℕ) : {i: Lyric I|Meadow.held i.val≤k}.Finite := by
  apply Set.Finite.subset ((Meadow.tuck (c:=c) (f:=f) k).finite_toSet.preimage (show Set.InjOn (fun i:Lyric I=>i.val) _ from Subtype.val_injective.injOn))
  intro i hi; exact (Meadow.pocket _ _).2 hi


def cabinet : Cabinet (Count E I) I (Mint.width X.halo (radiusB s) (radiusB s+n)) := by
  let q : Lyric I → ℕ:= fun i=> Meadow.held i.val
  have hB : 0<B:= lt_of_lt_of_le (by norm_num) I.laws.data.room.sight.1
  refine ⟨scorecard I E,Sum.elim (fun i=>pace S i.val) (fun i=>S.ratio.parent (E.home i)),fun i=>?_,Sum.elim q E.ride,fun k=>?_⟩
  · rcases i with i|i
    · exact Mint.centered X.halo B (B+n) hB i.val S T R (i.property.trans (Nat.le_add_right ..))
    have he := E.covers S.ratio X.halo B hB i
    change S.ratio.parent _ ∈ regularFoot _ _ _ _ _ ∧ regularFoot _ _ _ _ _ ⊆ _
    exact ⟨he.1,fun x hx=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (he.2 hx)).trans (by unfold Mint.width; omega))⟩
  apply Set.Finite.subset (((tucks I k).image (Sum.inl (β:=E.Node))).union ((E.finite k).image (Sum.inr (α:=Lyric I))))
  rintro (i|i) hi; exact Or.inl ⟨_,hi,rfl⟩; exact Or.inr ⟨_,hi,rfl⟩

lemma floats (i : E.Node) : (cabinet I E).ink (.inr i)= Opacity.key S i.val:= rfl
lemma coins (i:Lyric I) : (cabinet I E).ink (.inl i)= disc S i.val := rfl

end Drawing

section backward
variable {c f C F:Side} {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices}
  (hC:C.val=c.val*M) (he : 2≤ c.val) {T: Tube G (stepped Q h)} {T':Tube G (stepped Q H)}
  {R : RG.Rep G f} {R':RG.Rep G F} {I : Cash W s a L₀ X o U T R} {I' : Cash W s a L₀ X o u T' R'}
  {D : Cabinet ι I b} {A : Cabinet χ I' b}
local notation "B" => radiusB s
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H

structure Relay (Z : χ → ι) : Prop where
  lift : Nest (Deck.divides hC) Z A.site D.site
  hold i : D.hold (Z i) = A.hold i
  pitch i : D.foot (Z i)= (A.foot i).image ((L).low.cut)
  grant {E : Forest (stepped Q h).ratio} {F' : Forest (stepped Q H).ratio}
      {C₁:Coat T E} {C₂:Coat T' F'} (_ : Stellar hC he K s C₁ C₂) (k k':Finset ℕ) (z : Air f G) (i : χ) :
    C₂.vertex R' X.table W o.a k X.halo (Stellar.blow (L) z) (A.ink i) = C₁.vertex R X.table W o.a k' X.halo z (D.ink (Z i))

namespace Drawing
variable (hp:R'.path=R.path)
include hp
lemma verses (i : Music C F) : verse R.path (Stellar.verse_down (L) i)= verse R'.path i := by
  rw [hp]; rcases i with i|i|i|i <;> rfl

def down (i : Lyric I') : Lyric I:= ⟨Stellar.verse_down (L) i.val,((verses hC he hp i.val)).trans_le i.property⟩
lemma arbors : Nest (Deck.divides hC) (down hC he hp) (fun i: Lyric I'=> pace (Y) i.val) (fun i: Lyric I => pace (S) i.val) := by
  have ht:= Stellar.nest_mint (Q:=Q) (hC:=hC) (he:=he) (h:=h) (H:=H); refine ⟨fun i=> ht.footing _,fun x i hx=>?_,fun i j hh hu=>Subtype.ext (ht.firm _ _ (congr_arg Subtype.val hh) hu)⟩
  obtain ⟨y,hz,hy⟩:= ht.extend x i.val hx; exact ⟨⟨y,(verses hC he hp y).symm.trans_le (hz.symm ▸ i.property)⟩,Subtype.ext hz,hy⟩
variable (E : Ribbon R n) (E' : Ribbon R' n) {Z : Ribbon.Node E' → Ribbon.Node E}
lemma relay (hr : Ribbon.Drops E E' (Deck.fineP h H hC) Z) (hR:R'.p=R.p) (hb:R'.beta=R.beta)
    (hk:2*(Mint.width X.halo (radiusB s) (radiusB s+n)+3)<c.val) :
    Relay (A:=Drawing.cabinet I' E') (D:=Drawing.cabinet I E) hC he (Sum.map (Drawing.down hC he hp) Z) := by
  refine ⟨(arbors hC he hp).sum (Ribbon.pouring (h:=h) (H:=H) E E' hC he hr),fun i=>?_, fun i=>?_,fun A k k' z i=>?_⟩
  · rcases i with i|i
    · change Meadow.held (Stellar.verse_down (L) i.val)=Meadow.held i.val
      rcases i with ⟨(i|i|i|i),hh⟩<;> rfl
    exact (hr.size i).symm
  · have he : 4<f.val := by have hs:= I.laws.data.room.buys; have hm := P.L.property; have hh:c.val≤ f.val:= h ▸ Nat.le_mul_of_pos_right _ hm; omega
    rcases i with i|i
    · exact (Meadow.contempt (I:=I) (I':=I') hC (by assumption) hp i.val).2
    exact Ribbon.descentZ (h:=h) (H:=H) E E' hC (by assumption) hr X.halo B i he
  rcases i with i|i
  · exact A.granted hp hR hb o.a z X.table i.val i.property W X.halo k k'
  exact Ribbon.Vertex E E' hC he hr A hb i (by unfold Mint.width at *; omega) o.a W z X.table k k' X.halo
end Drawing
end backward
end YM.RGComparison01
