import YM.Integration.WilsonMarkedOrdinaryJointProduct

/-! Rootwise finite-versus-cover comparison for the full ordinary capture.
All proper factors use one angular chart and one set of named source lifts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedOrdinaryCaptureGap
open Function Finset Lattice RG
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Winding WilsonCoeffUV.Mer
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonMarkedOrdinaryLocalConvolution WilsonMarkedOrdinaryJointProduct
open scoped Classical BigOperators
variable {G:Gauge}{V:Type}[NormedAddCommGroup V][NormedSpace ℝ V]{ι:Type}[DecidableEq ι]{D:ι→ℕ}
variable {n:Side}{good:YForest G→Prop}{E R:ℕ}{δ A B:ℝ}{S:Finset ι}

def Within (n:Side)(good:YForest G→Prop)(E R:ℕ)(δ A:ℝ)(P:Era G V):Prop:=
  Sheet good (fun t=>(wrap n t.1,t.2)) E R δ A (P.1 n) P.2

omit [NormedSpace ℝ V] in
theorem Within.zero (n:Side)(good:YForest G→Prop)(E R:ℕ)(δ:ℝ):
    Within n good E R δ 0 (0:Era G V):=fun _ _ _ _=>Node.zero good (fun t:YForest G=>(wrap n t.1,t.2)) δ

theorem Within.scale {P:Era G V}(paid:Within n good E R δ A P)(c:ℝ):
    Within n good E R δ (‖c‖*A) (c•P):=fun i hi r hr=>(paid i hi r hr).scale c

omit [NormedSpace ℝ V] in
theorem Within.sum {t:Type}(S:Finset t)(P:t→Era G V)(C:t→ℝ)(paid:∀i∈S,Within n good E R δ (C i) (P i)):
    Within n good E R δ (∑i∈S,C i) (∑i∈S,P i):=by
  intro i hi r hr
  simpa only [Prod.fst_sum,Prod.snd_sum,Finset.sum_apply] using Node.sum S (fun j=>(P j).1 n i r)
    (fun j=>(P j).2 i r) C (fun j h=>paid j h i hi r hr)

omit [DecidableEq ι] in
theorem blank (n:Side)(good:YForest G→Prop)(E R:ℕ)(δ:ℝ)(rate:0≤δ):
    Within n good E R δ ‖ochre D‖ (puff D G):=by
  intro e he r hr x hx
  have bound:‖(puff D G).2 e r x‖≤‖ochre D‖:=by
    simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one] using (pillowPrice D G (σ:=0) (by simp) e r).2 x
  have same:(puff D G).1 n e r ((fun t : YForest G=>(wrap n t.1,t.2)) ∘ x)=(puff D G).2 e r x:=by cases r <;> rfl
  rw [same];exact ⟨bound,bound,by rw [sub_self,norm_zero];exact mul_nonneg (norm_nonneg _) rate⟩

/-- The multiplier depends on the working angular rank and coupling grade. -/
def tariff (D:ι→ℕ)(E R:ℕ)(S:Finset ι):ℝ:=
  if S=∅ then ‖ochre D‖ else
    ‖(S.card:ℝ)⁻¹‖*∑J∈S.powerset,if _w:J⊆S ∧ J≠∅ then
      ‖(J.card:ℝ)‖*(gross E R*tariff D E R (S\J)) else 0
termination_by S.card
decreasing_by exact Finset.card_lt_card (sh_k _w.1 _w.2)

theorem positive (D:ι→ℕ)(E R:ℕ)(S:Finset ι):0≤tariff D E R S:=by
  induction S using Finset.strongInduction with
  | H S ih=>
    rw [tariff];split;next=>exact norm_nonneg _
    refine mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun J hJ=>?_);split
    next w=>exact mul_nonneg (norm_nonneg _) (mul_nonneg (by unfold gross;positivity) (ih _ (sh_k w.1 w.2)))
    exact le_rfl

theorem ordinary (n:Side)(good:YForest G→Prop)(S:Finset ι)(P:family G D)(E R:ℕ)(δ B:ℝ)(rate:0≤δ)(bill:0≤B)
    (proper:∀J⊆S,Within n good E R δ (B^J.card) (P J)):
    Within n good E R δ (tariff D E R S*B^S.card) (levelsO P S):=by
  classical
  induction S using Finset.strongInduction with
  | H S ih=>
    by_cases empty:S=∅
    · subst S;rw [empty_level,tariff,if_pos rfl,Finset.card_empty,pow_zero,mul_one];exact blank _ _ _ _ _ rate
    let amount (J:Finset ι):ℝ:=if _w:J⊆S∧J≠∅ then
      ‖(J.card:ℝ)‖*(gross E R*tariff D E R (S\J)) else 0
    let term (J:Finset ι):Era G (Pen D S):=if w:J⊆S∧J≠∅ then
      (J.card:ℝ)•waxV w.1 (P J) (levelsO P (S\J)) else 0
    have one (J:Finset ι):Within n good E R δ (amount J*B^S.card) (term J):=by
      unfold amount term;split
      next w=>
        have u:=proper J w.1
        have v:=ih _ (sh_k w.1 w.2) (fun K sub=>proper K (sub.trans Finset.sdiff_subset))
        have h:Within n good E R δ (gross E R*(B^J.card*(tariff D E R (S\J)*B^(S\J).card)))
            (waxV w.1 (P J) (levelsO P (S\J))):=product w.1 u v (pow_nonneg bill _) (mul_nonneg (positive ..) (pow_nonneg bill _)) rate
        have lengths:J.card+(S\J).card=S.card:=by rw [add_comm,Finset.card_sdiff_add_card_eq_card w.1]
        convert h.scale (J.card:ℝ) using 1
        rw [←lengths,pow_add];ring
      rw [zero_mul];exact Within.zero n good E R δ
    have total:Within n good E R δ (∑J∈S.powerset,amount J*B^S.card) (∑J∈S.powerset,term J):=
      Within.sum S.powerset term _ (fun J _=>one J)
    rw [levelsO,dif_neg empty,tariff,if_neg empty]
    change Within n good E R δ (‖(S.card:ℝ)⁻¹‖ * (∑J∈S.powerset,amount J) * B^S.card) ((S.card:ℝ)⁻¹ • (∑J∈S.powerset,term J))
    rw [mul_assoc,Finset.sum_mul];exact total.scale _

end YM.Integration.WilsonMarkedOrdinaryCaptureGap
end
