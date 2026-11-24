import YM.WilsonCoeffUV.Marked.Capture.AtSensor
/-!
# Root sphere budget on log to CAPTURE

All addresses inside box, any mixed regular profile. NOT rolling arbitrarily
coarse using estimate. Reserve for masks must be requested separately.
 -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Wheel.Flooring
open Wheel.Mark Function PowerSeries Blue Mer Lattice RG Embroider Embroider.Canvas Soil Bank Laurent Cosmos Filter Gauge Power Matrix Precision Wilson Tree Exterior AnalyticNext.QuarticMatch.Sheets Bloch FreeResolvent Work.F08 Shard Realm PathCost MeasureTheory Set Real
open Fountain Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {ι α β U:Type}{J I S T:Finset ι}{D k K':ι→ℕ}{o:ι}{c:Side}{i j i' j' a e r h N n m b b' l:ℕ}{G:Gauge}{σ τ u g B C x y z ρ:ℝ}{E W V' U':Credit}
variable [DecidableEq ι]
omit [DecidableEq ι] in
lemma cLeaf [NormedAddCommGroup U](p:ι→Cover)(w':o∈S){P:Ten U (Cloth α) r}(v:(Bank.terrain.gap 0 (p o):ℝ) ≤ z)(w:0≤σ)(h:Wig Bank.terrain p σ B S P): Cork Bank.terrain 0 σ (B*exp (σ*z)) P:=by
    have hp:= h.to_cork w w'
    refine ⟨mul_nonneg hp.1 (by positivity),fun x=> (hp.2 x).trans (mul_assoc B _ _ ▸ ?_)⟩
    rw [← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ hp.1; apply Real.exp_le_exp.mpr; have H:= move_cap Bank.terrain 0 (p o) x; let Z:=p o; let a':=(tread Bank.terrain 0 x:ℝ); let b':=(tread Bank.terrain Z x:ℝ); have hc:a'≤ b'+(Bank.terrain.gap 0 Z:ℝ):= by unfold a' b' Z; exact_mod_cast H
    linarith [mul_le_mul_of_nonneg_left (hc.trans (add_le_add_right v b')) w]
lemma corkV {P:Ten (Pen D J) (Cloth α) i}{Q:Ten (Pen D (S\J)) (Cloth α) j}(h:J⊆ S)(p:Cork Bank.terrain 0 σ B P)(t:Cork Bank.terrain 0 σ C Q)(q:0≤σ): Cork Bank.terrain 0 σ (B*C) (cobT h P Q (i+j)):=by
    refine ⟨mul_nonneg p.1 t.1,fun y=>?_⟩; rw [cobT,dif_pos rfl,waveJoy]; let v:=y∘ Fin.castAdd j; let u:= y ∘ Fin.natAdd i; apply (joy_norm h (P v) (Q u)).trans; refine (mul_le_mul (p.2 _) (t.2 _) (norm_nonneg _) ((norm_nonneg _).trans (p.2 _))).trans ?_; rw [mul_mul_mul_comm,←Real.exp_add,←mul_add,← Nat.cast_add]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Nat.cast_le.mpr (webT_tread Bank.terrain 0 rfl _)) (neg_nonpos.mpr q))) (mul_nonneg p.1 t.1)
lemma foamBudget (D:ι→ℕ)(h:J⊆ S)(P:Pal (Pen D J) (YForest G))(Q:Pal (Pen D (S\J)) (YForest G))(p:∀ i≤e,∀ r,Cork Bank.terrain 0 σ B (P i r))(t:∀ i≤e,∀ r,Cork Bank.terrain 0 σ C (Q i r))(v:0≤σ)(w:i≤e): Cork Bank.terrain 0 σ ( (i+1:ℕ)*( (r+1:ℕ)*(B*C))) (foam h P Q i r):=by
    unfold foam; rw [Finset.sum_apply,show ((i+1:ℕ):ℝ)*_ = ∑ _j∈Finset.antidiagonal i,(r+1:ℕ)*(B*C) by simp]; apply Cork.sum; intro l hl; have he:=Finset.mem_antidiagonal.mp hl
    apply Twig.swirl; rw [show ((r+1:ℕ):ℝ)*_=∑ _j∈Finset.antidiagonal r,B*C by simp]; apply Cork.sum; intro j hj; have hz:=Finset.mem_antidiagonal.mp hj
    obtain ⟨a,b⟩:=j; change a+b=r at hz; subst r; exact corkV h (p _ (by omega) _) (t _ (by omega) _) v

-- currency payout constants uniform all σ positive up to one, cannot project hearts of α arbitrary without buds
abbrev trueKnots (P:family G D)(S:Finset ι)(σ B:ℝ)(e:ℕ):Prop:=∀ J⊆S,∀ i≤e,∀ r,Cork Bank.terrain 0 σ (B^J.card) ((P J).2 i r)
omit [DecidableEq ι] in
lemma pillowPrice (D:ι→ℕ)(G:Gauge)(_x:0≤σ)(i r): Cork Bank.terrain 0 σ (‖ochre D‖) ((puff D G).2 i r):=by
    refine ⟨norm_nonneg _,fun y=>?_⟩; change ‖uband (1: Cost) i r (y:Fin r→ YForest G) • ochre D‖ ≤ _
    cases r
    · simp only [uband,shine_lit]; rw [coeff_one]; split <;> simp [tread,league,Bank.terrain]
    simp only [uband,shine_dark (show 0 ≠ _+1 by omega),Pi.zero_apply,zero_smul,norm_zero]; positivity

theorem formalO (G:Gauge)(D k:ι→ℕ)(S:Finset ι)(e):∃ A:ℝ,0≤ A∧ ∀ (B σ:ℝ),0≤ B →0≤σ →∀ P:family G D,Eu k P→ trueKnots P S σ B e →∀ i≤e,∀ r,Cork Bank.terrain 0 σ (A*B^S.card) ((levelsO P S).2 i r):=by
   induction S using Finset.strongInduction with
   | H S ih=>
      by_cases he:S=∅; · subst S; refine ⟨‖ochre D‖,norm_nonneg _,fun _ _ _ h P _ _ i _ r=>?_⟩; rw [empty_level,Finset.card_empty,pow_zero,mul_one]; exact pillowPrice D G h i r
      let t (J:Finset ι):=J⊆ S∧J≠∅
      choose V hV p using fun J (v:t J)=>ih _ (sh_k v.1 v.2);
      let Gv:= mass k S+e
      let C (J:Finset ι) := if g:t J then (J.card:ℝ)*((e+1:ℕ)*((Gv+1:ℕ)*V J g)) else 0
      let T:=∑ J∈ S.powerset,C J; have ht:0≤T:=by
          apply Finset.sum_nonneg; intro i _; unfold C; split; next g=> have hx:=hV i g; positivity
          exact le_rfl
      refine ⟨‖(S.card:ℝ)⁻¹‖*T,by positivity,fun B σ h u P y q i h' r=>?_⟩; have hv:0≤B^S.card:= by positivity
      by_cases v:r ≤ Gv
      · have hx J (w:t J) : Cork Bank.terrain 0 σ (((i+1:ℕ):ℝ)*( (r+1:ℕ)*( B^J.card*(V J w*B^(S\J).card)))) ((waxV w.1 (P J) (levelsO P (S\J))).2 i r):=foamBudget D w.1 _ _ (q _ w.1) (p J w B σ h u P y (fun J g=>q J (g.trans Finset.sdiff_subset))) u h'
        let A j: Era G (Pen D S):= if w:t j then (j.card:ℝ) • waxV w.1 (P j) (levelsO P (S\j)) else 0
        have hb j:Cork Bank.terrain 0 σ (C j*B^S.card) ((A j).2 i r):=by
            unfold A C; split; next w=>
                have hQ:j.card+(S\j).card=S.card:= by rw [add_comm]; exact Finset.card_sdiff_add_card_eq_card w.1
                apply ((hx j w).μ (j.card:ℝ)).cost; rw [abs_of_nonneg (by positivity :0≤(j.card:ℝ)), ← mul_assoc, show B^j.card*(V j w*B^(S\j).card) = V j w*B^S.card by rw [←hQ,pow_add,mul_left_comm]]; have hh:=hV j w; apply le_trans (b:=((j.card:ℝ)*(e+1:ℕ))*(((Gv+1:ℕ):ℝ)*(V j w*B^S.card))) ?_ (le_of_eq (by ring)); gcongr
            rw [zero_mul]; exact Cork.zero
        rw [levelsO,dif_neg he]; change Cork _ _ _ _ (((S.card:ℝ)⁻¹) • (∑ j∈ S.powerset, A j).2 i r); rw [Prod.snd_sum,Finset.sum_apply,Finset.sum_apply]; unfold T; rw [mul_assoc,Finset.sum_mul]; exact (Cork.sum fun i _=> hb i).μ _
      rw [(placedO P y S).coverN i r (by unfold Gv at v; omega)]; apply Cork.zero.cost; positivity
end YM.WilsonCoeffUV.Wheel.Flooring
