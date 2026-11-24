import YM.RG11Proof.Rigidity.Prism.Volume

/-!
# The invariant sample only sees paired data
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Prism
open scoped BigOperators InnerProductSpace Topology Classical
open Function Set MeasureTheory Metric Maxwell.Free
variable {I : Type} [Fintype I]

local notation "X"=> Desk I
local notation "K"=> (inner ℝ (E:=X))

def meets : ℕ→ℝ
  | 0=>1
  | n+1=> (2*(n:ℝ)+1)*meets n
lemma meets_pos (n) : 0<meets n := by induction n with |zero=> exact zero_lt_one|succ n h=> unfold meets; positivity

lemma replicate_cost (n : ℕ) (a : X) : pairCost K (List.replicate (2*n) a)=meets n * ‖a‖^(2*n) := by
  induction n with
  | zero=> simp [pairCost,meets]
  | succ n ih=>
    rw [show 2*(n+1)=(2*n+1)+1 by omega,List.replicate_succ, pair_step]
    unfold pulls
    have he (i : Fin ((List.replicate (2*n+1) a).length)) : (List.replicate (2*n+1) a).eraseIdx i.val=List.replicate (2*n) a := by
      have hk : List.Perm ((List.replicate (2*n+1) a).get i :: (List.replicate (2*n+1) a).eraseIdx i.val) (List.replicate (2*n+1) a) := by simpa using List.getElem_cons_eraseIdx_perm (l:=List.replicate (2*n+1) a) i.isLt
      -- strip common a then equality.
      rw [List.get_eq_getElem,List.getElem_replicate] at hk
      conv_rhs at hk=> rw [List.replicate_succ]
      apply List.perm_replicate.mp ((List.perm_cons a).mp hk)
    simp_rw [List.get_eq_getElem,List.getElem_replicate,he,ih,real_inner_self_eq_norm_sq]
    simp [List.length_replicate,meets,pow_succ]; ring

def north (i : I) : X := haveI := Classical.decEq I; EuclideanSpace.basisFun I ℝ i
lemma compactGauge (i : I) : ‖north i‖=1 := OrthonormalBasis.norm_eq_one ..

def pace (i : I) (n : ℕ) := tour (List.replicate (2*n) (north i))/meets n

lemma sheet_meter (i : I)(n : ℕ)(l : List X)(h : l.length=2*n) : tour l=pace i n * pairCost K l := by
  apply Weight.polarize _ (tour_law (I:=I)) (B:=fun l:List X=>pace i n * pairCost K l) _ _ _ h
  · exact ⟨fun ht=> congr_arg (pace i n * ·) (pair_law.swappable ht),
       fun a b l=> by rw [pair_law.plus,mul_add],
       fun t a l=> by rw [pair_law.ratio,mul_left_comm]⟩
  intro a
  obtain ⟨R,hR⟩ := transitive a (‖a‖ • north i) (by simp [norm_smul,compactGauge])
  rw [← rotate (List.replicate (2*n) a) R, List.map_replicate, hR,circle_scale, replicate_cost,pace]
  field_simp [(meets_pos n).ne']

lemma odd_meter (n : ℕ) (l : List X) (h : l.length=2*n+1) : tour l=0 := by
  apply tour_law.from_diag _ _ _ h
  intro a
  have he := rotate (List.replicate (2*n+1) a) (LinearIsometryEquiv.neg ℝ (E:=X))
  have ht : ∀ x : X,hue (List.map (LinearIsometryEquiv.neg ℝ) (List.replicate (2*n+1) a)) x= -hue (List.replicate (2*n+1) a) x := by
    intro x
    simp only [hue,List.map_replicate,List.prod_replicate]
    change inner ℝ (-a) x^(2*n+1)=_
    rw [inner_neg_left (𝕜:=ℝ),pow_succ,pow_mul]
    simp [pow_succ,pow_mul]
  unfold tour at he ⊢; simp_rw [ht,integral_neg] at he; linarith

end YM.RG11.Rigidity.Prism
