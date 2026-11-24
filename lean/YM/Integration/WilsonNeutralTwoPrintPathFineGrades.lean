import YM.Integration.WilsonReceivedCoverFaces

/-! Causality of the ordinary squarefree exponential on a specified finite
board, for a single chosen occupied subset and each of its actual subfaces. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonNeutralTwoPrintPathFineGrades
open Function Filter Finset Lattice Wilson RG
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Soil WilsonCoeffUV.Mer WilsonCoeffUV.Wheel
open Precision WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonReceivedCoverGrade (Through)
open scoped Classical BigOperators
variable {G:Gauge}{I V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{X:Side}{e:ℕ}

private theorem scaled (c:ℝ){P Q:Era G V}(h:Through e (P.1 X) (Q.1 X)):
    Through e ((c • P).1 X) ((c • Q).1 X):=by
  intro a ha
  change c • P.1 X a=c • Q.1 X a
  rw [h a ha]

omit [NormedSpace ℝ V] in
private theorem census (S:Finset I){P Q:I→Era G V}(h:∀i∈S,Through e ((P i).1 X) ((Q i).1 X)):
    Through e ((∑i∈S,P i).1 X) ((∑i∈S,Q i).1 X):=by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty];exact fun _ _=>rfl
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    intro a ha
    change (P i).1 X a+(∑j∈S,P j).1 X a=(Q i).1 X a+(∑j∈S,Q j).1 X a
    rw [h i (Finset.mem_insert_self ..) a ha,ih (fun z hz=>h z (Finset.mem_insert_of_mem hz)) a ha]

variable [DecidableEq I]{D:I→ℕ}

private theorem paired {A S:Finset I}(j:A⊆S){P Q:Era G (Pen D A)}{M N:Era G (Pen D (S\A))}
    (h:Through e (P.1 X) (Q.1 X))(l:Through e (M.1 X) (N.1 X)):
    Through e ((waxV j P M).1 X) ((waxV j Q N).1 X):=by
  intro i hi
  change foam j (P.1 X) (M.1 X) i=foam j (Q.1 X) (N.1 X) i
  unfold foam
  apply Finset.sum_congr rfl
  intro u hu
  have index:=Finset.HasAntidiagonal.mem_antidiagonal.mp hu
  rw [h u.1 (by omega),l u.2 (by omega)]

theorem ordinary {P Q:family G D}(A:Finset I)(entries:∀T⊆A,Through e ((P T).1 X) ((Q T).1 X)):
    Through e ((levelsO P A).1 X) ((levelsO Q A).1 X):=by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases z:A=∅
    · subst A;rw [empty_level,empty_level];exact fun _ _=>rfl
    rw [levelsO.eq_def P A,levelsO.eq_def Q A,dif_neg z,dif_neg z]
    refine scaled (G:=G) (V:=Pen D A) (X:=X) (A.card:ℝ)⁻¹ ?_
    refine census (G:=G) (V:=Pen D A) (X:=X) A.powerset ?_
    intro T _
    split_ifs with hj
    · exact scaled (G:=G) (V:=Pen D A) (X:=X) _
        (paired (G:=G) (D:=D) (X:=X) hj.1 (entries _ hj.1)
          (ih _ (sh_k hj.1 hj.2) (fun U inc=>entries U (inc.trans Finset.sdiff_subset))))
    · exact fun _ _=>rfl

end YM.Integration.WilsonNeutralTwoPrintPathFineGrades
end
