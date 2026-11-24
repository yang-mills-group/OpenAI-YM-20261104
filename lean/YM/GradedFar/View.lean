import YM.GradedFar.Coalesce
import YM.OPE.Orbits.System
/-!
# HorizonFork: each fixed row sees *the whole* exterior through all phases, LogTrace price

Phase and shadow truncation. Still fixed on physical basis labels at this stage (purchase
extended by multilinearity later). Same p's tokens in every row.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Fork
open Finset Filter Function Set Spec Table Extraction OPE OPE.Arboreal OPE.Log Node
open OPE.Orbits hiding whole
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
    {I J:Type} [Fintype I] [Fintype J] {P:Prescription F.sector.derivatives}
local notation "spots" => Fork.position
local notation "nearSet" => Fork.near I J
local notation "outerSet" => Fork.outer I J
local notation "tree'" => Fork.tree I J
local notation "T" => Node I J

def namesake (u : I → C.book.Token) (w : J → C.book.Token) : T → C.book.Token
  | leaf i => u i
  | far j => w j
  | _ => C.book.one 0

def writeIn (i:I) : ↥nearSet := ⟨leaf i, by simp [Fork.near]⟩
def enroll : I ≃ ↥nearSet := Equiv.ofBijective writeIn ⟨by
  intro i j h; exact leaf.inj (congrArg Subtype.val h),by
  rintro ⟨p,hp⟩; rcases mem_map.mp hp with ⟨i,_,rfl⟩; exact ⟨i,rfl⟩⟩

def writeLayout (t:I⊕J) : ↥(tree').leaves := match t with
  | Sum.inl i => ⟨leaf i, by simp [leaves,Fork.near]⟩
  | Sum.inr j => ⟨far j, by simp [leaves,broad]⟩
def layout : I⊕J ≃ ↥(tree').leaves := Equiv.ofBijective writeLayout ⟨by
  intro i j h; obtain h' := congrArg Subtype.val h; cases i <;> cases j <;> simp_all [writeLayout], by
  rintro ⟨p,hp⟩; rw [leaves] at hp; rcases mem_union.mp hp with hp|hp
  · rcases mem_map.mp hp with ⟨i,_,rfl⟩; exact ⟨.inl i,rfl⟩
  rcases mem_map.mp hp with ⟨i,_,rfl⟩; exact ⟨.inr i,rfl⟩⟩
def writeReplace (t:Unit⊕J) : ↥outerSet := match t with
  | Sum.inl _ => ⟨child, by simp [Fork.outer]⟩
  | Sum.inr j => ⟨far j, by simp [Fork.outer,broad]⟩
def replace : Unit⊕J ≃ ↥outerSet := Equiv.ofBijective writeReplace ⟨by
  intro i j h; obtain h' := congrArg Subtype.val h; cases i <;> cases j <;> simp_all [writeReplace], by
  rintro ⟨p,hp⟩; rcases mem_insert.mp hp with hp|hp
  · subst p; exact ⟨.inl (),rfl⟩
  rcases mem_map.mp hp with ⟨i,_,rfl⟩; exact ⟨.inr i,rfl⟩⟩

lemma renameRead {A B:Type}[Fintype A][Fintype B] (e:A≃B) {x:A→E4} {z:B→E4}
    {L:Register G} {v:A→L.Token} {w:B→L.Token} {U:Table L} (hU:U.Symmetric)
    (hx:Injective x)(he: z ∘ e=x) (hy: w ∘ e=v) : observe U x v= observe U z w :=
  ((by rw [show z=x ∘ e.symm by rw [← he]; exact (funext (fun i=>by simp)).symm]
       rw [show w=v ∘ e.symm by rw [← hy]; exact (funext (fun i=>by simp)).symm]; exact perm_observe U hU e.symm v hx): observe U z w=observe U x v).symm

lemma renameWrite {A B:Type} [Fintype A][Fintype B] (e:A≃B) {x:A→E4} {z:B→E4}
    {L:Register G} {v:A→L.Token} {w:B→L.Token} {U:Table L} (hU:U.Symmetric)
    (hx:Injective x) (he:z ∘ e=x) (hy:w ∘ e=v) : observe U x v=observe U (beside z vacant) (beside w bare) := by
  let f : A ≃ B⊕Fin 0 := e.trans (Equiv.sumEmpty B (Fin 0)).symm
  exact renameRead f hU hx (show _=x from funext fun i=> congrFun he i)
    (show _=v from funext fun i=> congrFun hy i)

section
variable {d:I→ℕ} {e:J→ℕ} (u : Labels S d) (w : Labels S e)
local notation "p" => namesake (C:=C) (names u) (names w)
lemma treeWhole (o:E4) {x:I→E4}{y:J→E4} {r s:ℝ} {U:Table C.book} (hx:Injective (beside (move o r x) (move o s y)))(hU:U.Symmetric):
    Orbits.whole U (move o r x) u (move o s y) w = whole U (tree').leaves (spots o r s x y) p vacant bare := by
  rw [whole_observed]; exact renameWrite layout hU hx (funext (fun i=>by cases i<;> rfl))
    (funext (fun i=>by cases i<;>rfl))

variable {M δ:ℝ}(mn:0≤M)(dp:0<δ) (bank:LogTrace F P)
omit [Fintype I] in
lemma treeParent (a:Mode F.sector.derivatives) (o:E4)(x:I→E4){y:J→E4} (r:ℝ){s:ℝ}{U:Table C.book}
    (hx:Injective (beside (sole o) (move o s y)))(hU:U.Symmetric) :
    observe U (beside (sole o) (move o s y)) (beside (sole (P.letter a)) (names w))=
      whole U outerSet (spots o r s x y) (update p child (P.letter a)) vacant bare := by
  apply renameWrite Fork.replace hU hx
  · exact funext (fun i=>by cases i<;> rfl)
  · funext i; cases i <;> simp [Fork.replace,writeReplace,crop,namesake, sole]

omit [Fintype J] in
lemma treeKernel (a:Mode F.sector.derivatives) (o:E4)(x:I→E4)(y:J→E4) (r s:ℝ):
    P.ope a (move o r x) (names u) o = coalesce P nearSet (spots o r s x y) p child a :=
  P.coefficient_perm (x:=crop (spots o r s x y) nearSet) (z:=o) (crop p nearSet) F.room.kernel.laws.toSymmetric enroll a

include bank mn dp
lemma phase_basis (hG : G.Simple) : ∃k:ℕ,∀ᶠs:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(y:J→E4),0<r → r ≤ s →
    Setting M δ x y → r*M ≤ s*δ → ∀ v:Viewers F,
      (r^(∑i,d i)*s^(∑j,e j))*‖Orbits.whole (spectator F v) (move o r x) u (move o s y) w -
        Orbits.whole S (move o r x) u (move o s y) w‖ ≤ 2*(badge s*badge r)^k*s := by
  obtain ⟨k,h⟩:= phase F P hG bank p mn dp; refine ⟨k,h.mono ?_⟩
  intro s hs r o x y hr hsr hx hrg v; have hh:=full_layout o hx dp hr hsr hrg
  rw [treeWhole u w o hh (spectate F v).laws.toSymmetric,treeWhole u w o hh F.room.kernel.laws.toSymmetric]
  exact hs r o x y hr hsr hx hrg v

lemma approximate_basis (hG : G.Simple) (h:ℕ):
    ∃(b:ℝ)(K:ℕ),0≤b ∧ ∀ᶠs:ℝ in 𝓝[>]0,∀(r:ℝ)(o:E4)(x:I→E4)(y:J→E4),
      0<r → r ≤ s → Setting M δ x y → r*M ≤ s*δ → ∀v:Viewers F,
        let Z:=shadowOld P h (move o r x) o u
        (r^(∑i,d i)*s^(∑j,e j))*‖Orbits.whole (spectator F v) (move o r x) u (move o s y) w -
            upon (spectator F v) h o (move o s y) w Z‖ ≤
        b*(badge s*badge r)^K*(s+(r/s)^(h+1)):=by
  obtain ⟨b,k,hb,H⟩:= sum_shadow F P hG bank p h mn dp; refine ⟨b,k,hb,H.mono ?_⟩
  intro s hs r o x y hr hsr hx hrg v; have hh:=full_layout o hx dp hr hsr hrg
  have hy := center_layout o (hr.trans_le hsr) dp hx.away hx.zclear
  have hU := spectate F v
  have he: upon (spectator F v) h o (move o s y) w (shadowOld P h (move o r x) o u)=
      ∑a∈bands F.sector.derivatives h, coalesce P nearSet (spots o r s x y) p child a *
        whole (spectator F v) outerSet (spots o r s x y) (update p child (P.letter a)) vacant bare := by
    rw [upon_observe _ _ hU (spectate_respects F v) hy, shadowOld,
      compatible_shadows _ _ hU (spectate_respects F v) (spectate_ready F v) _ hy]
    exact Finset.sum_congr rfl fun a _ => congrArg₂ (·*·) (treeKernel F u w a o x y r s)
      (treeParent F u w a o x r hy hU.laws.toSymmetric)
  dsimp only; rw [he,treeWhole u w o hh hU.laws.toSymmetric]; exact hs r o x y hr hsr hx hrg v
end
end YM.Integration.GradedFar.Fork
