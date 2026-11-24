import YM.Integration.WilsonReceivedCoverGrade
/-! Causal coupling degrees on the entire native marked exponential, logarithm,
and sum over independent child positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCoverFaces
open WilsonCoeffUV
open Lattice RG Wilson Precision WilsonCoeffUV.Blue WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonReceivedCoverGrade
open scoped Classical BigOperators

variable {G:Gauge}{V W I:Type}[NormedAddCommGroup V][NormedSpace ℝ V]
  [NormedAddCommGroup W][NormedSpace ℝ W] {e:ℕ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem self (P:Era G V):Same e P P:=fun _ _=>rfl
omit [NormedSpace ℝ V] in
theorem add {P Q X Y:Era G V}(h:Same e P X)(x:Same e Q Y):Same e (P+Q) (X+Y):=by
  intro i hi
  change P.2 i+Q.2 i=X.2 i+Y.2 i
  rw [h i hi,x i hi]

omit [NormedSpace ℝ V] in
theorem sub {P Q X Y:Era G V}(h:Same e P X)(x:Same e Q Y):Same e (P-Q) (X-Y):=by
  intro i hi
  change P.2 i-Q.2 i=X.2 i-Y.2 i
  rw [h i hi,x i hi]

theorem scaled (c:ℝ){P Q:Era G V}(h:Same e P Q):Same e (c • P) (c • Q):=by
  intro i hi
  change c • P.2 i=c • Q.2 i
  rw [h i hi]

omit [NormedSpace ℝ V] in
theorem census (S:Finset I){P Q:I → Era G V}(h:∀j∈S,Same e (P j) (Q j)):
    Same e (∑ j∈S,P j) (∑ j∈S,Q j):=by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact self _
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha]
    exact add (h _ (Finset.mem_insert_self ..)) (ih fun j w=>h _ (Finset.mem_insert_of_mem w))

theorem tuft (T:V→L[ℝ]W){P Q:Era G V}(h:Same e P Q):Same e (tuftV T P) (tuftV T Q):=by
  intro i hi
  change cloaks T.toLinearMap (P.2 i)=cloaks T.toLinearMap (Q.2 i)
  rw [h i hi]

variable [DecidableEq I]{J S:Finset I}{D:I→ℕ}
theorem paired (j:J⊆S){P Q:Era G (Pen D J)}{M N:Era G (Pen D (S\J))}(h:Same e P Q)(l:Same e M N):
    Same e (waxV j P M) (waxV j Q N):=by
  intro i hi
  change (foam j P.2 M.2) i=(foam j Q.2 N.2) i
  unfold foam
  apply Finset.sum_congr rfl
  intro t ht
  have ht':=Finset.HasAntidiagonal.mem_antidiagonal.mp ht
  rw [h t.1 (by omega),l t.2 (by omega)]

theorem ordinary {P Q:family G D}(h:∀S,Same e (P S) (Q S))(S:Finset I):
    Same e (levelsO P S) (levelsO Q S):=by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases z:S=∅
    · subst S; rw [empty_level,empty_level]; exact self _
    rw [levelsO.eq_def P S,levelsO.eq_def Q S,dif_neg z,dif_neg z]
    refine scaled (G:=G) (V:=Pen D S) (e:=e) (S.card:ℝ)⁻¹ ?_
    refine census (G:=G) (V:=Pen D S) (e:=e) S.powerset ?_
    intro j _
    split_ifs with hj
    · exact scaled (G:=G) (V:=Pen D S) (e:=e) _ (paired (G:=G) (D:=D) (e:=e) hj.1 (h _) (ih _ (sh_k hj.1 hj.2)))
    · exact self _

theorem connected {P Q:family G D}(h:∀S,Same e (P S) (Q S))(S:Finset I):
    Same e (reverseO P S) (reverseO Q S):=by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases z:S=∅
    · subst S; rw [empty_reverse,empty_reverse]; exact self _
    rw [reverseO.eq_def P S,reverseO.eq_def Q S,dif_neg z,dif_neg z]
    apply sub (G:=G) (V:=Pen D S) (e:=e) (h _)
    refine scaled (G:=G) (V:=Pen D S) (e:=e) (S.card:ℝ)⁻¹ ?_
    refine census (G:=G) (V:=Pen D S) (e:=e) S.powerset ?_
    intro j _
    split_ifs with hj
    · exact scaled (G:=G) (V:=Pen D S) (e:=e) _ (paired (G:=G) (D:=D) (e:=e) hj.1 (ih _ (lt_of_le_of_ne hj.1 hj.2)) (h _))
    · exact self _

theorem step (H:Levels G)(L:ChartRatio G)(m N:ℕ)(K k:I→ℕ){P Q:Outerm G D}
    (h:∀x S,Same e (P x S) (Q x S))(x:I → Cover)(S:Finset I):
    Same e (stout H L m N K k P x S) (stout H L m N K k Q x S):=by
  change Same e (unite _ K _ x S) (unite _ K _ x S)
  unfold unite
  refine census (G:=G) (V:=Pen D S) (e:=e) Finset.univ ?_
  intro j _
  unfold portV
  refine scaled (G:=G) (V:=Pen D S) (e:=e) _ ?_
  refine tuft (G:=G) (V:=Pen D S) (W:=Pen D S) (e:=e) _ ?_
  unfold logO
  apply connected
  intro s
  exact verse H L m N _ (ordinary (h _) s)

end YM.Integration.WilsonReceivedCoverFaces
