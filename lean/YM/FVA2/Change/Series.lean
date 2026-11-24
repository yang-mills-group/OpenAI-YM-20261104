import YM.FVA2.Wick.Formal
import YM.MS.Menus.Mark
/-!
# Substitution and scalars in the *given* diagram series algebra

Cost functions are ordinary g-series. Reuse the MS definitions of formal products and composition.
The marks will be sums of reexpressed Wilson stencils with `oil` weights; these outer scalars
are in the public parameter and we don't need to invert the regulator parameter to apply them.
Every statement is formal. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change
open Function Set Filter Finset
open MS MS.Koszul MS.Plane MS.Orbit Cog MS.Swirl MS.Book Convolve Program
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open Wick (pull)
open Wick.Formal (overlay)
open scoped BigOperators Topology ContDiff
variable {A B I X J E : Type}

abbrev Ser := T ℂ

section convolve
variable [AddCommGroup E] [Module ℂ E] [AddCommGroup X] [Module ℂ X] [AddCommGroup B][Module ℂ B]
variable {K:E→ₗ[ℂ] X→ₗ[ℂ] B}
abbrev scale (E:Type)[AddCommGroup E][Module ℂ E] := pairW (LinearMap.lsmul ℂ E)
lemma scale_l {v : Ser} (x:T E) (y:T X) : pairW K (scale E v x) y=scale B v (pairW K x y) := by rw [flips, Menus.olio, flips K.flip]; rfl -- inspect
lemma scale_r {v : Ser} (x:T E) (y:T X) : pairW K x (scale X v y)=scale B v (pairW K x y) := Menus.olio ..
lemma promote_scale {v:Ser}(x:T E)(L:E→ₗ[ℂ]X): promote L (scale E v x)=scale X v (promote L x) := by funext i; rw [promised, scale, paired, map_sum]; exact Finset.sum_congr rfl fun _ _=> map_smul L _ _
lemma sub_module (a : Cn) {u:T E} (x:Submodule ℂ E) (h:u∈allIndex x ℕ) : substitute a u∈allIndex x ℕ  := by intro k _; change substitute a u k ∈ x; rw [rules]; exact x.sum_mem fun i _=> x.smul_mem _ (h i (Set.mem_univ _))
lemma scale_module {v:T ℂ} {u:T E} (x:Submodule ℂ E)(h:u∈allIndex x ℕ): scale E v u∈allIndex x ℕ := by intro k _; change pairW (LinearMap.lsmul ℂ E) v u k ∈ x; rw [paired]; refine x.sum_mem fun i _=>?_ ; exact x.smul_mem (v i.1) (h i.2 (Set.mem_univ _))

-- exp0 under subν
variable (t : Cn) (h : Rooted t)(p:Sector A)
local infixl:70 " ★ " => overlay p
local notation "M" => PermV p
local notation "R" => Raw A ℂ
local notation "Φ" => substitute (P:=Raw A ℂ) t
lemma sub_core (X Y:T R) (h:Rooted t) : Φ (X ★ Y)= Φ X ★ Φ Y := ( substitute_pair h X Y (product p))|>.symm
lemma sub_cons (v:E): substitute t (useN.refineV v)=useN.refineV v:= by
  funext i; by_cases he:i=0; · rw [he,pay0]
  rw [rules]
  unfold SplitP.refineV; rw [if_neg (show i≠ useN.origin from he), Finset.sum_eq_zero]; intro x _; split
  next hx=> rw [show x=0 from hx, Program.cut]; simp [he]
  next _=> exact smul_zero ..
include h
lemma sub_tether : Tether Φ M M := ⟨sub_cons t (coin 1),fun x y=>sub_core t p x y h⟩
lemma sub_exp {V: T R}(hx:V 0=0): substitute t (exp0 p V)=exp0 p (substitute t V):= by
  funext i
  change _= (M).cheers (Φ V) i i; rw [← (sub_tether t h p).cheersV ]
  rw [rules,rules]; apply Finset.sum_congr rfl; intro k hk; rw [← show ( M ).cheers V i k = exp0 p V k from overbook (actor p) useN V hx (Finset.mem_Iic.mp hk)]

variable {P V: T (Raw A ℂ)} {Z:Ser} [Fintype A] (H : Grain A)
local notation "U" => ℶV H
local infixl:70 " ● " => Actors.core Trunk
lemma sub_views (hp:P 0=0)(hv:Endμ H p P V Z) : Endμ H p (Φ P) (Φ V) (substitute t Z) := by
  unfold Endμ
  have hw (v:T (Raw A ℂ)) : U (Φ v) = substitute t (U v) := Program.comm t v _
  rw [← sub_exp t h p hp, ← show Φ _= _ from sub_core t p (exp0 p P) V h,hw,hv,hw]; exact (substitute_pair h _ _ Toy.core)|>.symm
omit h
lemma End_scale {v:Ser}(hv:Endμ H p P V Z): Endμ H p P (scale _ v V) (v ● Z):= by
  unfold Endμ; have h (V:T R)(k:Ser) : exp0 p P ★ scale (Raw A ℂ) k V = scale _ k (exp0 p P ★ V) := Menus.olio ..
  have hx (V:T R): U (scale _ v V) = scale ℂ v (U V):= promote_scale V (View H)
  rw [h,hx,hv]; exact (scale_r _ _).symm -- projection elaboration
lemma End_tab_sum {V:J→ T R}{F:J→Ser}(s:Finset J)(h:∀ i∈s, Endμ H p P (V i) (F i)): Endμ H p P (∑ i∈s,V i) (∑ i∈s,F i) := by unfold Endμ; rw [map_sum,map_sum,map_sum]; exact Finset.sum_congr rfl h
omit [Fintype A] in
lemma scale_slot (x y:T R)(v:Ser) : (scale R v x ★ y)=scale _ v (x ★ y) := scale_l .. -- types
omit [Fintype A] in
lemma scale_slot_r (x y:T R)(v:Ser) : (x ★ scale R v y)=scale _ v (x ★ y) := scale_r ..
end convolve
end YM.FVA2.Change
