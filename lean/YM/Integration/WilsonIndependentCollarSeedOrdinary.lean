import YM.Integration.WilsonIndependentCollarSeedProduct

/-! Initial ordinary faces of an externally prescribed finite stencil family.
Each edge of a tensor product is summed around the front of its own factor. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarSeedOrdinary
open Function Finset Lattice RG Wilson Precision Work.F08
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer
open WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Soil
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard WilsonIndependentCollarSeedProduct
open scoped Classical BigOperators
variable {G:Gauge} {ι:Type} [DecidableEq ι] {D k:ι→ℕ} {e K:ℕ}

def unitCost (D:ι→ℕ) (G:Gauge) (e:ℕ):ℝ:=1+∑q∈Finset.range (e+1),‖(puff D G).2 q 0 default‖

omit [DecidableEq ι] in
private lemma empty (D:ι→ℕ) (G:Gauge) (e K:ℕ):Total e K (puff D G).2 (unitCost D G e):=by
  intro q hq r _
  have pos:0≤unitCost D G e:=by unfold unitCost;positivity
  cases r with
  | zero=>
    apply invoice.mpr
    refine ⟨fun _=>norm_nonneg _,Summable.of_finite,?_⟩
    rw [tsum_fintype,Fintype.sum_unique]
    exact (Finset.single_le_sum (fun t _=>norm_nonneg ((puff D G).2 t 0 default))
      (show q∈Finset.range (e+1) by simp;omega)).trans (by unfold unitCost;linarith)
  | succ r=>
    have clear:(puff D G).2 q (r+1)=0:=by
      funext x; change uband (U:=YForest G) 1 q (r+1) x • ochre D=_
      unfold uband;rw [shine_dark (by omega)];simp
    rw [clear];exact Fruit.zero.more pos

def cost (D:ι→ℕ) (G:Gauge) (e K:ℕ) (S:Finset ι):ℝ:=
  if S=∅ then unitCost D G e else
    ‖(S.card:ℝ)⁻¹‖*∑j∈S.powerset,if h:j⊆S∧j≠∅ then
      (j.card:ℝ)*(((e:ℝ)+1)*((K:ℝ)+1))*cost D G e K (S\j) else 0
termination_by S.card
decreasing_by exact Finset.card_lt_card (sh_k h.1 h.2)

lemma nonneg (D:ι→ℕ) (G:Gauge) (e K:ℕ) (S:Finset ι):0≤cost D G e K S:=by
  induction S using Finset.strongInduction with
  | H S ih=>rw [cost];split
            next _=>unfold unitCost;positivity
            next _=>apply mul_nonneg (norm_nonneg _) (Finset.sum_nonneg _);intro j _;split
                    next h=>have :=ih (S\j) (sh_k h.1 h.2);positivity
                    next=>exact le_rfl

theorem original (M:family G D) (A:ℝ) (hp:0≤A)
    (connected:∀s:Finset ι,s.Nonempty → Total e K (M s).2 (A^s.card)) (S:Finset ι):
    Total e K (levelsO M S).2 (cost D G e K S*A^S.card):=by
  induction S using Finset.strongInduction with
  | H S ih=>
    by_cases occ:S=∅
    · subst S;rw [empty_level,cost,if_pos rfl,Finset.card_empty,pow_zero,mul_one];exact empty D G e K
    intro q hq r hr
    let P (j:Finset ι):=if h:j⊆S∧j≠∅ then (j.card:ℝ) • waxV h.1 (M j) (levelsO M (S\j)) else 0
    let bill (j:Finset ι):ℝ:=if _h:j⊆S∧j≠∅ then (j.card:ℝ)*(((e:ℝ)+1)*((K:ℝ)+1))*cost D G e K (S\j) else 0
    have paid j:Fruit 0 0 0 ((P j).2 q r) (bill j*A^S.card):=by
      dsimp only [P,bill];split
      next s=>
        have child:=ih (S\j) (sh_k s.1 s.2)
        have A0:=nonneg D G e K (S\j)
        have h:=product s.1 (pow_nonneg hp _) (mul_nonneg A0 (pow_nonneg hp _))
          (connected j (Finset.nonempty_iff_ne_empty.mpr s.2)) child q hq r hr
        have card:j.card+(S\j).card=S.card:=by rw [Finset.card_sdiff_of_subset s.1];have :=Finset.card_le_card s.1;omega
        apply (h.μ (j.card:ℝ)).more
        rw [abs_of_nonneg (by positivity),←card,pow_add];apply le_of_eq;ring
      next _=>change Fruit 0 0 0 (0:Ten (Pen D S) (YForest G) r) (0* _);rw [zero_mul];exact Fruit.zero
    rw [levelsO,dif_neg occ]
    have total:= (Fruit.sum (S:=S.powerset) (fun j _=>paid j) (by norm_num)).μ (S.card:ℝ)⁻¹
    change Fruit 0 0 0 ((S.card:ℝ)⁻¹ • ((∑j∈S.powerset,P j).2 q r)) _
    simp only [Prod.snd_sum,Finset.sum_apply]
    apply total.more
    rw [cost,if_neg occ,←Finset.sum_mul,←mul_assoc,Real.norm_eq_abs]

end YM.Integration.WilsonIndependentCollarSeedOrdinary
end
