import YM.Integration.WilsonVacuumPreResetWindingPolynomial
import YM.WilsonCoeffUV.Marked.Step.LogStep

/-! Interpolation in the complete old quiet and marked tables in a
single native finite-period connected Wilson step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedPolynomialTable
open Function Finset Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Soil WilsonCoeffUV.Embroider
open AnalyticNext.QuarticMatch.Sheets WilsonCoeffUV.Embroider.Canvas WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open scoped BigOperators Classical
variable {ι U:Type} [DecidableEq ι] {D:ι→ℕ} {G:Gauge} {f c:Side}

private def Table (d:ℕ)(F:ℝ→Pal ℝ U):Prop:=
  ∀e,WilsonVacuumPreResetWindingPolynomial.Entries (e+d) (fun t=>F t e)

private theorem product {a b:ℕ}{P Q:ℝ→Pal ℝ U}
    (hp:Table a P)(hq:Table b Q):Table (a+b) (fun t=>woad (P t) (Q t)):=by
  intro e r x
  simp only [woad,Finset.sum_apply]
  apply WilsonVacuumPreResetWindingPolynomial.sums
  intro j hj
  have coup:j.1+j.2=e:=by simpa using hj
  have fee:(j.1+a)+(j.2+b)=e+(a+b):=by omega
  apply WilsonVacuumPreResetWindingPolynomial.swirled
  intro y
  simp only [Finset.sum_apply]
  apply WilsonVacuumPreResetWindingPolynomial.sums
  intro i hi
  have slots:i.1+i.2=r:=by simpa using hi
  simp only [webT,dif_pos slots]
  exact fee ▸ WilsonVacuumPreResetWindingPolynomial.mul (hp j.1 _ _) (hq j.2 _ _)

private def slot (A:Case D)(I:Finset ι)(n:Side)(e r:ℕ)(x:Fin r→Woods G n):
    Era G (Pen D I) →ₗ[ℝ] ℝ where
  toFun p:=touch A I (p.1 n e r x)
  map_add' _ _:=(touch A I).map_add _ _
  map_smul' _ _:=(touch A I).map_smul _ _

private def point (A:Case D)(I:Finset ι)(h e r:ℕ)(x:Fin r→U):
    Layers (Pen D I) U →ₗ[ℝ] ℝ where
  toFun p:=touch A I (p h e r x)
  map_add' _ _:=(touch A I).map_add _ _
  map_smul' _ _:=(touch A I).map_smul _ _

private theorem weighed (A:Case D)(I:Finset ι)(K:ℝ→family G D)(n:Side)
    (original:∀J:Finset ι,J.Nonempty→Table J.card (fun t=>pPly A J ((K t J).1 n))):
    Table I.card (fun t=>pPly A I ((levelsO (K t) I).1 n)):=by
  induction I using Finset.strongInduction with
  | H I ih=>
    by_cases empty:I=∅
    · subst I
      intro e r x
      simp only [empty_level]
      exact WilsonVacuumPreResetWindingPolynomial.constant _ _
    · intro e r x
      conv in levelsO (K _) I => rw [levelsO,dif_neg empty]
      change WilsonVacuumPreResetWindingPolynomial.At (e+I.card) (fun t=>
        slot A I n e r x ((I.card:ℝ)⁻¹ • ∑J∈I.powerset,
          if w:J⊆I∧J≠∅ then (J.card:ℝ) • waxV w.1 (K t J) (levelsO (K t) (I\J)) else 0))
      simp only [map_smul,smul_eq_mul]
      apply WilsonVacuumPreResetWindingPolynomial.scale
      simp only [map_sum]
      apply WilsonVacuumPreResetWindingPolynomial.sums
      intro J _
      split
      next w=>
        simp only [map_smul,smul_eq_mul]
        apply WilsonVacuumPreResetWindingPolynomial.scale
        change WilsonVacuumPreResetWindingPolynomial.At _ (fun t=>pPly A I (foam w.1 ((K t J).1 n)
          ((levelsO (K t) (I\J)).1 n)) e r x)
        simp only [fp]
        have seats:J.card+(I\J).card=I.card:=by
          rw [Finset.card_sdiff_of_subset w.1];have h:=Finset.card_le_card w.1;omega
        exact seats ▸ product (original J (Finset.nonempty_iff_ne_empty.mpr w.2))
          (ih (I\J) (sh_k w.1 w.2)) e r x
      next =>exact WilsonVacuumPreResetWindingPolynomial.constant _ _

private theorem heated (A:Case D)(K:ℝ→family G D)(I:Finset ι)
    (S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P V:PChart G f)
    (income:∀J:Finset ι,J.Nonempty→Table J.card (fun t=>pPly A J ((K t J).1 f))):
    ∀h,Table I.card (fun t=>pPly A I (oven S F H Q O (P+t•V) (K t) I h)):=by
  intro h e r x
  have move(t:ℝ):pPly A I (oven S F H Q O (P+t•V) (K t) I h)=
      srShade S F H Q O (P+t•V) (pPly A I ((levelsO (K t) I).1 f)) h:=
    congrFun (peelR S F H Q O (P+t•V) ((levelsO (K t) I).1 f) A) h
  simp only [move]
  exact WilsonVacuumPreResetWindingPolynomial.companion S F H Q O P V _
    I.card (weighed A I K f income) h e r x

private theorem connected (A:Case D)(X:ℝ→thalamus D U)(I:Finset ι)
    (income:∀J h,Table J.card (fun t=>pPly A J (X t J h))):
    ∀h,Table I.card (fun t=>pPly A I (turnTLog (X t) I h)):=by
  induction I using Finset.strongInduction with
  | H I ih=>
    intro h e r x
    by_cases zero:I=∅
    · subst I
      conv in turnTLog (X _) _ => rw [turnTLog,dif_pos rfl]
      exact WilsonVacuumPreResetWindingPolynomial.constant _ _
    · conv in turnTLog (X _) I => rw [turnTLog,dif_neg zero]
      change WilsonVacuumPreResetWindingPolynomial.At _ (fun t=>point A I h e r x
        (X t I-(I.card:ℝ)⁻¹ • ∑J∈I.powerset, if w:J⊆I ∧ J≠I then
           (J.card:ℝ) • foamT w.1 (turnTLog (X t) J) (X t (I\J)) else 0))
      simp only [map_sub,map_smul,map_sum,smul_eq_mul]
      apply WilsonVacuumPreResetWindingPolynomial.sub (income I h e r x)
      apply WilsonVacuumPreResetWindingPolynomial.scale
      apply WilsonVacuumPreResetWindingPolynomial.sums
      intro J _
      by_cases w:J⊆I∧J≠I
      · simp only [dif_pos w,map_smul,smul_eq_mul]
        apply WilsonVacuumPreResetWindingPolynomial.scale
        have view(t:ℝ):pPly A I (foamT w.1 (turnTLog (X t) J) (X t (I\J)) h)=
            tassel (fun u=>pPly A J (turnTLog (X t) J u)) (fun u=>pPly A (I\J) (X t (I\J) u)) h:=
          congrFun (fpT w.1 (turnTLog (X t) J) (X t (I\J)) A) h
        change WilsonVacuumPreResetWindingPolynomial.At _ (fun t=>pPly A I
          (foamT w.1 (turnTLog (X t) J) (X t (I\J)) h) e r x)
        simp only [view,tassel,Finset.sum_apply]
        apply WilsonVacuumPreResetWindingPolynomial.sums
        intro uv _
        have seats:J.card+(I\J).card=I.card:=by
          rw [Finset.card_sdiff_of_subset w.1];have z:=Finset.card_le_card w.1;omega
        exact seats ▸ product (ih J (lt_of_le_of_ne w.1 w.2) uv.1) (income (I\J) uv.2) e r x
      · simp only [dif_neg w,map_zero]
        exact WilsonVacuumPreResetWindingPolynomial.constant _ _

private theorem extend {a b:ℕ}{F:ℝ→ℝ}(paid:WilsonVacuumPreResetWindingPolynomial.At a F)
    (le:a≤b):WilsonVacuumPreResetWindingPolynomial.At b F:=by
  obtain ⟨p,degree,read⟩:=paid
  exact ⟨p,degree.trans le,read⟩

omit [DecidableEq ι] in
private theorem finish {U':Type} [Fintype U] [Fintype U'] (A:Case D)(I:Finset ι)
    (X:ℝ→Layers (Pen D I) U)(a l:ℕ)(C:Cost)(M:Matrix U U' ℝ)
    (income:∀h,Table a (fun t=>pPly A I (X t h))):
    Table a (fun t=>pPly A I (Blue.mix C (fun i=>fade M (finalZ (X t) l i)))):=by
  intro e r x
  change WilsonVacuumPreResetWindingPolynomial.At (e+a) (fun t=>touch A I
    (Blue.mix C (fun i=>fade M (finalZ (X t) l i)) e r x))
  simp only [Blue.mix,Finset.sum_apply,Pi.smul_apply,map_smul,map_sum,smul_eq_mul]
  apply WilsonVacuumPreResetWindingPolynomial.sums
  intro j hj
  have eligible:j≤e:=by simpa using hj
  apply WilsonVacuumPreResetWindingPolynomial.scale
  apply extend (a:=j+a) _ (by omega)
  have move(t:ℝ):touch A I (fade M (finalZ (X t) l j) r x)=
      fade M (cloaks (touch A I).toLinearMap (finalZ (X t) l j)) r x:=
    congrFun (congrFun (cloak_fade (touch A I).toLinearMap M (finalZ (X t) l j)) r) x
  simp only [move]
  apply WilsonVacuumPreResetWindingPolynomial.folded
  intro v y
  change WilsonVacuumPreResetWindingPolynomial.At _ (fun t=>touch A I (finalZ (X t) l j v y))
  simp only [finalZ,Finset.sum_apply,map_sum]
  exact WilsonVacuumPreResetWindingPolynomial.sums _ _ fun h _=>income h j v y

/-- All old quiet and all old connected marked rows can vary at once on
one genuine finite Wick step. The complete occupied coefficient is
tested multilinearly on its original label set, at every angular rank. -/
theorem original (S:StepData c f)(F:Forest S.ratio)(H:FreeResolvent.FaceRow)
    (Q:Matrix (Body 1 f) (Body 1 c) ℝ)(O:ChartRatio G)(P V:PChart G f)
    (K B:family G D)(C:Cost)(k:ι→ℕ)(A:Case D)(I:Finset ι)(e r:ℕ)(x:Fin r→Woods G c):
    WilsonVacuumPreResetWindingPolynomial.At (e+I.card)
      (fun t=>touch A I (mist S F H Q O (P+t•V) (fun J=>K J+t•B J) C k I e r x)):=by
  let M(t:ℝ)(J:Finset ι):=K J+t•B J
  have incoming(J:Finset ι)(live:J.Nonempty):Table J.card (fun t=>pPly A J ((M t J).1 f)):=by
    intro i v y
    change WilsonVacuumPreResetWindingPolynomial.At _ (fun t=>slot A J f i v y (K J+t•B J))
    simp only [map_add,map_smul,smul_eq_mul]
    exact WilsonVacuumPreResetWindingPolynomial.affine (by have:=live.card_pos;omega) _ _
  let heat(t:ℝ):thalamus D (Joint G f c):=oven S F H Q O (P+t•V) (M t)
  have allHeat(J:Finset ι)(h:ℕ):Table J.card (fun t=>pPly A J (heat t J h)):=
    heated A M J S F H Q O P V incoming h
  exact finish A I (fun t=>turnTLog (heat t) I) I.card (mass k I) C plug
    (connected A heat I allHeat) e r x

/-- One polynomial joins the proposed reference to the actual finite
logO on its own old finite vacuum, official kinetic reset and all
original marked proper faces. -/
theorem finite (L:Levels G)(O:ChartRatio G)(m N:ℕ)(live:m<N)(simple:G.Simple)
    (localRatio:LocalRatio O)(n:Side)(P:PChart G (n*(ll L m).L))(K B:family G D)
    (k:ι→ℕ)(law:Eu k K)(A:Case D)(I:Finset ι)(e r:ℕ)(x:Fin r→Woods G n):
    let S:=stepAt (ll L m) L.clock.kernel n
    let F:=xree (ll L m) L.clock.kernel n
    let Fk:=freeForms L N (m+1)
    let Q:=roam L N m n
    let T:=(story L O N (m+1)).1 (n*(ll L m).L)
    let C:=ratioHigh L O N m
    ∃p:Polynomial ℝ,p.natDegree ≤ e+I.card ∧
      p.eval 0=touch A I (mist S F Fk Q O P B C k I e r x) ∧
      p.eval 1=touch A I ((logO L O m N K k I).1 n e r x) ∧
      ∀t:ℝ,p.eval t=touch A I (mist S F Fk Q O (P+t•(T-P)) (fun J=>B J+t•(K J-B J)) C k I e r x):=by
  intro S F Fk Q T C
  obtain ⟨p,hp,values⟩:=original S F Fk Q O P (T-P) B (fun J=>K J-B J) C k A I e r x
  refine ⟨p,hp,?_,?_,values⟩
  · simpa only [zero_smul,add_zero] using values 0
  · rw [feeleg L O m N K k live simple localRatio law n I]
    simpa only [one_smul,add_sub_cancel] using values 1

end YM.Integration.WilsonVacuumPreResetMarkedPolynomialTable
end
