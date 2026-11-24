import YM.XSpace.Vanilla
/-!
# Missing (disconnected) sectors vanish in the leading channel
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Rose
open Function Set Filter MeasureTheory Trace Graph3 Maxwell Maxwell.Free Maxwell.Wick Photo Cirrus Normalize Tornado Chiral Structure1 AxesTangent Angle Season Lattice Relief Finale
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{x:Points 3}(W:Initialize G)(g:G.Simple)(h:x∈conf 3)
local notation "A"=> leaf G 6
local notation "Q"=> tag G
local notation "χ"=> missing (tag G)
abbrev Badge := Finset (Fin 3)
@[simp] lemma full (G:Gauge): missing (tag G) Finset.univ=tag G:= funext fun i=>by simp [missing]
lemma rising (S:Badge): ∀ i:Fin 3,i≠0→hinge 6 (χ S i)= χ S i:=by
  intro i H; unfold missing; split; · fin_cases i <;> first | exact False.elim (H rfl)| exact u_even
  exact hinge_leaf ..
lemma begin (s:Badge)(h:0∉s): hinge 6 ∘ χ s=χ s:=by funext i; by_cases hx:i=0; simp [hx,h,missing,hinge_leaf]; exact rising s i hx
lemma bud (Q':Badge)(h:0∈Q'): SlotOdd (χ Q'):=by
  let L:=χ Q'; intro F; rw [show hinge 6 ∘ L=update L 0 (-L 0) from ?_, MultilinearMap.map_update_neg, Function.update_eq_self]
  funext i; by_cases he:i=0; subst i; simp only [h,L,missing,t_odd,tag,peg₀,update_self,comp_apply, ↓reduceIte]; rw [update_of_ne he]; exact rising Q' i he
lemma juror (s:Badge): reel 6 ∘ χ s=χ s:=by
  have hh(t:Fin 3): reel 6 (Q t) = Q t:=by fin_cases t; exact t_real; all_goals exact Rose.u_real
  funext i; change reel 6 (χ s i)=_; unfold missing; split; exact hh _
  exact Subtype.ext (map_one (realForm (G:=G)))
include W g h
lemma silent (s:Badge)(hs:s.Nonempty): scene x 6 (χ s)=0:=by
  by_cases H:0∈s; exact even_zero x _ h (bud _ H)
  have count (p:Sec G 6): scene x 6 (trip p (tin G) (tin G))=0:=by
    let f : Fin 3→ℂ:= trip 1 ((↑Rose.f:ℂ)^2) ((↑Rose.f:ℂ)^2); let t:=trip p (Tuk G) (Tuk G); rw [show trip p (tin G) (tin G)=(fun i=>f i • t i) from funext fun i=> by fin_cases i; exact (one_smul ℂ _).symm; all_goals rfl,MultilinearMap.map_smul_univ, reaches W g p x h,smul_zero]
  have he: s={1,2}∨∃ i: Fin 3,i≠0∧s={i}:= by
    have HE : ∀ s: Badge,s.Nonempty→¬ (0:Fin 3)∈s→ s={1,2}∨∃ i: Fin 3,i≠0∧ s={i}:= by decide
    exact HE s hs H
  rcases he with he|⟨i,hi,rfl⟩; · subst s; rw [show χ ({1,2}:Badge) = trip A (tin G) (tin G) from funext fun i=>by fin_cases i<;> simp [tag,trip, missing]]; exact count _
  let p: WickPol G:= (tin G).val; let u:= fun _:Fin 3=> (1: WickPol G); let M:= moment G x
  have ht (q:Name G):M (update u i (lens false q *lens false q))=0:=by
    let v:= lens false q; let P:= update u i v; rw [show update u i _=update P i (v* P i) from (by unfold P; rw [update_self, update_idem])]; unfold M v lens; rw [moment_one _ _ _ h]; apply Finset.sum_eq_zero; intro j hj; have hv: P j=1:= update_of_ne (Finset.mem_erase.mp hj).1 ..; rw [hv,Derivation.map_one_eq_zero]; exact MultilinearMap.map_coord_zero _ (i:=j) (Function.update_self ..) -- lens unfolding
  have hb: Q i=tin G:=by fin_cases i <;> first | exact False.elim (hi rfl) | rfl
  change M (fun j=> (χ ({i}:Badge) j).val)=0; rw [show (fun j=> (χ ({i}:Badge) j).val)=update u i p from funext fun j=>by unfold p missing; by_cases e:j=i; subst j; simp only [if_pos (Finset.mem_singleton_self _), hb,update_self]; rw [if_neg (fun h=> e (Finset.mem_singleton.mp h)), update_of_ne e]; rfl,show p=_ from frontier G,MultilinearMap.map_update_smul,MultilinearMap.map_update_sum]; rw [Finset.sum_eq_zero (fun i (_:i∈Finset.univ)=>ht i),smul_zero]
end YM.XSpace.Rose
