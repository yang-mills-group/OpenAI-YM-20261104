import YM.Integration.WilsonPrecontactSeparatedLamps
import YM.Next.MULTISOURCE.Formal
import YM.QuadraticLocal.Manifold

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalOneColor
open Function Finset Lattice Wilson RG Ac Marker QuadraticLocal Push.Corrected Push.AbsoluteSums MeasureTheory
open Multi WilsonPrecontactSeparatedLamps
open Push RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached
open scoped Classical BigOperators
variable {V:Type} [DecidableEq V] [Fintype V] {R:Census V}
variable {G:Gauge} {n:Side} {T ι:Type} {o:V→Site n} {p:BudgetPoint}
variable {F:ℕ→ForcedAddress G n} {K:Code G n}

def visible (v:V) (s:R.Mode):Prop:=s.val⊆{v}
def turn (v i:V):ℂ:=if i=v then 1 else 0
def cut (v:V):Poly R→ₐ[ℂ]Poly R:=Multi.dilation R (turn v)

omit [Fintype V] in
theorem coefficient (v:V) (s:R.Mode):
    (∏i∈s.val,turn v i)=if visible v s then 1 else 0:=by
  by_cases yes:visible v s
  · rw [if_pos yes]
    exact Finset.prod_eq_one fun i hi=>if_pos (Finset.mem_singleton.mp (yes hi))
  · rw [if_neg yes]
    obtain ⟨i,hi,no⟩:∃i∈s.val,i≠v:=by
      by_contra! all
      exact yes (fun i hi=>Finset.mem_singleton.mpr (all i hi))
    exact Finset.prod_eq_zero hi (if_neg no)

omit [Fintype V] in
theorem part (v:V) (x:Poly R) (s:R.Mode):(cut v x).part s=if visible v s then x.part s else 0:=by
  rw [cut,Multi.dilation_part,coefficient]
  split <;> simp

omit [Fintype V] in
theorem quiet (v:V) (x:Poly R):(cut v x).part R.quiet=x.part R.quiet:=by
  rw [part,if_pos]
  exact Finset.empty_subset _

omit [Fintype V] in
theorem own (v:V) (x:Poly R):(cut v x).part (R.fire v)=x.part (R.fire v):=by
  rw [part,if_pos];exact subset_rfl

omit [Fintype V] in
theorem smaller (v:V) (x:Poly R) (w:V→ℝ) (pos:∀i,0<w i):
    Poly.price w (cut v x)≤Poly.price w x:=by
  apply Finset.sum_le_sum
  intro s _
  apply mul_le_mul_of_nonneg_left _ (Poly.worth pos s).le
  rw [part];split <;> simp

def seats (v:V) (A:Lamps T ι G p o R):Set ι:={i|visible v (A.mode i)}
abbrev lamps (v:V) (A:Lamps T ι G p o R):=portion A (seats v A)

omit [Fintype V] in
theorem regular (v:V) (A:Lamps T ι G p o R) {w:V→ℝ} {B:ℕ} {a r:ℝ} (paid:A.Paid w B a r):
    (lamps v A).Paid w B a r:=charged A _ paid

def hard (v:V) (H:Hard T p F K o R):Hard T p F K o R where
  hard t i U:=cut v (H.hard t i U)
  locality t i:=by
    have cont:Continuous (cut (R:=R) v):=continuous_pi (fun s=>continuous_const.mul (Poly.get s).continuous)
    refine ⟨fun a U=>congrArg (cut v) ((H.locality t i).gauge a U),
      cont.measurable.comp (H.locality t i).borel,
      fun U U' read hf=>congrArg (cut v) ((H.locality t i).reads U U' read hf),?_⟩
    intro U s live
    apply (H.locality t i).carry U s
    intro gone;apply live;rw [part,gone];simp
  charged t i U live:=H.charged t i U (fun h=>live (by rw [h,map_zero]))
  quiet t i U:=(quiet v _).trans (H.quiet t i U)

omit [Fintype V] in
theorem paid (v:V) (H:Hard T p F K o R) {w:V→ℝ} (pos:∀i,0<w i) {B:ℕ} {a r:ℝ}
    (has:H.Paid w B a r):(hard v H).Paid w B a r:=by
  obtain ⟨f,covers,wage⟩:=has.wages
  refine ⟨fun i=>cut v (f i),?_,?_⟩
  · intro i t U s
    change ‖(cut v (H.hard t i U)).part s‖ ≤ ((cut v (f i)).part s).re ∧ ((cut v (f i)).part s).im=0
    simp only [part]
    split
    · exact covers i t U s
    · simp
  intro u
  apply budget_mono (wage u)
  · intro i;split
    · exact mul_nonneg (Poly.nonnegative pos _) (Real.exp_nonneg _)
    · exact le_rfl
  · intro i;split
    · exact mul_le_mul_of_nonneg_right (smaller v (f i) w pos) (Real.exp_nonneg _)
    · exact le_rfl

end YM.Integration.WilsonOriginalOneColor
end
