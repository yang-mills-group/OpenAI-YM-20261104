import YM.FormalBulk08.Plait.Cheap

/-! Costed stationary interpretation for an arbitrary on-shell case
and proof of first loop readout. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Plait
open Function Filter Wick Orb Series Jets PowerSeries Lava Gorge Mesa Broc
open Matrix (of)
open scoped BigOperators Topology Classical Matrix ContDiff
variable {V I:Type*} [Fintype V][Fintype I][DecidableEq V]

def baseP (S L:Jets.Rays (V⊕I)→ℝ):Pap (V⊕I):= -afterX (paste S) 2 + paste L
def originH (q:Saddle ℝ V)(S:Jets.Rays (V⊕I)→ℝ): Hull V I:=⟨q,-coeff 2 (paste (S ∘ scalpel V I)),0⟩
variable {q:Saddle ℝ V}{S L:Jets.Rays (V⊕I)→ℝ}
lemma veget (p:Pap (V⊕I))(i): coeff i (toInk (originH q S) p)= chord p i:= by
    rw [fuel_emer,coeff_map]; unfold lever;rw [show (MvPolynomial.aeval (R:=ℝ) (Sum.elim (fun i => MvPolynomial.X (Sum.inl i) + MvPolynomial.rename Sum.inr ((originH q S).drift i)) (fun j=>MvPolynomial.X (Sum.inr j)))) = AlgHom.id ℝ _ from ?_,coeff_map]; rfl
    ext i; cases i <;> simp [originH] -- rename.
omit [DecidableEq V] in
lemma cube_base (i): chord (baseP S L) i= -chord (paste S) (i+2)+ chord (paste L) i := by rw [chord,baseP,map_add,map_neg,after_one,map_add,map_neg,add_comm 2];rfl
lemma origin_proof (h:ContDiffAt ℝ ∞ S 0)(ht:Chilly S)(hl:L 0=0)(hp:dimR (gateP S) 0= q.P): Solved (originH q S) (baseP S L):= by
    unfold Solved; rw [veget,cube_base,chord_center S h ht, show chord (paste L) 0=0 by rw [chord,paste_first, hl,map_zero,map_zero],add_zero,add_comm];
    have he: fort (litR (gateP S)) 0= (variation q I).P:= by ext i j v; simp only [fort,litR,Matrix.of_apply,paste_first,variation,RingHom.mapMatrix_apply,Matrix.map_apply]; rw [show gateP S i j 0=_ from congr_fun (congr_fun hp i) j]
    rw [he]; rfl
omit [DecidableEq V] in
lemma bubbles_bake (h:ContDiffAt ℝ ∞ S 0)(ht:Chilly S)(j:ℕ):
     ∃ T:Pairs V I, -chord (paste S) (j+3)= MvPolynomial.C (-coeff (j+3) (paste (S∘ scalpel V I))) + (rect (fort (litR (gateP S)) (j+1))+ T) ∧ Rental T j:= by
    let n:=j+1; let P:= chord (paste S) (j+3); let E:= MvPolynomial.C (σ:=V) (coeff (j+3) (paste (S ∘ scalpel V I))); let Q:= fort (litR (gateP S)) n; let X:=rect Q; let Y:= -(P-E)-X
    have hx:= Tally.base (V:=V) (paste_grade (S ∘ scalpel V I) (j+3)); have hr:Tally X (j+3):= Tally.rect (n:=j+1) (fun i k=> paste_grade (gateP S i k) (j+1))
    have hq': Qᵀ=Q:= chord_gate S h n
    refine ⟨Y,?_, tip_bottom (((Tally.neg ((chord_sym S h (j+3)).sub hx))).sub hr) ?_ ?_ ?_⟩
    · rw [map_neg]; change -P=-E+(X+Y); unfold Y; abel
    · change MvPolynomial.constantCoeff Y=0; unfold Y P E X; rw [map_sub,map_neg,map_sub,chord_root S h,MvPolynomial.constantCoeff_C,rect_corner,sub_self,neg_zero,sub_zero]
    · intro i; change MvPolynomial.constantCoeff (MvPolynomial.pderiv i Y)=0; unfold Y P E X; simp only [map_neg,map_sub,MvPolynomial.pderiv_C,sub_zero,unpaid S h ht i (j+2), rect_trim hq',neg_zero]
    intro i k; change MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv k Y))=0; unfold Y P E X; simp only [map_neg,map_sub,MvPolynomial.pderiv_C,sub_zero, chord_money S h (j+1), rect_cease hq',map_neg,MvPolynomial.constantCoeff_C]; exact sub_self _
omit [DecidableEq V] in
lemma bubbles_pay (h: ContDiffAt ℝ ∞ S 0)(p:Chilly S)(hl:ContDiffAt ℝ ∞ L 0)(n): ∃ T:Pairs V I, chord (baseP S L) (n+1)= MvPolynomial.C (-coeff (n+3) (paste (S ∘ scalpel V I))+ coeff (n+1) (paste (L ∘ scalpel V I))) + (rect (fort (litR (gateP S)) (n+1))+ T)∧ Rental T n := by
    obtain ⟨U,H,K⟩:= bubbles_bake h p n;let f:=chord (paste L) (n+1);let X:=MvPolynomial.C (σ:=V) (MvPolynomial.constantCoeff f)
    refine ⟨U+(f-X),?_,K.add (chord_sym L hl _).centers⟩; rw [cube_base,H,map_add (MvPolynomial.C)]; unfold f X; rw [chord_root L hl]; abel
omit [DecidableEq V] [Fintype I] in
lemma rect_size {M:Matrix V V (TypeR I)}{n:ℕ}(h:∀ i j, (M i j).totalDegree≤n): Rental (rect M) n:= by
    rw [rect]; intro d; rw [MvPolynomial.coeff_neg,MvPolynomial.coeff_sum,←Finset.sum_neg_distrib];simp_rw [MvPolynomial.coeff_sum, ←Finset.sum_neg_distrib]
    refine graded_price _ _ (fun i _=> graded_price _ _ (fun j _=>?_)); rw [show MvPolynomial.C (σ:=V) (halve (M i j))*MvPolynomial.X i * MvPolynomial.X j=MvPolynomial.monomial (Finsupp.single i 1+ Finsupp.single j 1) (halve (M i j)) from ?_, MvPolynomial.coeff_monomial]; split
    · rw [show -halve (M i j)=MvPolynomial.C (-1)*halve (M i j) by simp]; exact (MvPolynomial.totalDegree_mul ..).trans (by rw [MvPolynomial.totalDegree_C,zero_add];exact charge_half _ n (h i j))
    · simp
    rw [mul_assoc,MvPolynomial.X,MvPolynomial.X,MvPolynomial.monomial_mul,MvPolynomial.C_mul_monomial];simp
lemma thermal_anchor (f:Jets.Rays I→ℝ)(h: ContDiffAt ℝ ∞ f 0): paste (fun i=>-(1/2:ℝ)*f i)=C (MvPolynomial.C (-(1/2:ℝ)))*paste f:= by
   change paste ((fun i:Jets.Rays I=>-(1/2:ℝ))*f)=_; rw [paste_mul _ _ (contDiffAt_const (c:=(-(1/2:ℝ)))) h,paste_flat]

def thermalD (S L:Jets.Rays (V⊕I)→ℝ): Jets.Rays I→ℝ:= (L ∘ scalpel V I)+ fun x=> -(1/2:ℝ)*Real.log (dimR (gateP S) x).det
lemma thermal_view (h:ContDiffAt ℝ ∞ S 0)(p:dimR (gateP S) 0=q.P)(hp:0<q.P.det)(hl:ContDiffAt ℝ ∞ L 0):
     coeff 2 (paste (thermalD S L))= coeff 2 (paste (L ∘ scalpel V I))+ curve (originH q S) (fort (litR (gateP S)) 1) (fort (litR (gateP S)) 2):= by
    let F:=gateP S; have hv: 0<(dimR F 0).det:= p.symm ▸ hp; let L':=fun x=> Real.log (dimR F x).det; have he: ContDiffAt ℝ ∞ L' 0:= (paint_a F (gale_caps S h)).log hv.ne'; have hs:= (deter_lux (originH q S) F (gale_caps S h) p hv)
    rw [thermalD]; rw [paste_sum _ _ (ContDiffAt.comp (g:=L) (f:=scalpel V I) 0 (by rw [map_zero];exact hl) (scalpel V I).contDiff.contDiffAt) (show ContDiffAt ℝ ∞ (fun x=> -(1/2:ℝ)*L' x) 0 from contDiffAt_const.mul he),thermal_anchor L' he,map_add,coeff_C_mul]; unfold curve; unfold L';rw [hs]
    rw [←Matrix.mul_assoc (rhoq _*_)]; congr 1; simp only [halve]; have hx : (algebraMap ℚ (TypeR I)) (1/2)=MvPolynomial.C (1/2:ℝ):= by rw [IsScalarTower.algebraMap_apply ℚ ℝ]; congr; norm_num
    rw [hx,map_neg]; ring
lemma first_pages (h: ContDiffAt ℝ ∞ S 0)(p: Chilly S)(e:dimR (gateP S) 0=q.P)(hp: 0<q.P.det)(hl:ContDiffAt ℝ ∞ L 0)(hz:L 0=0) :
    let a:= baseP S L; let T:= originH q S; let f:= S∘ scalpel V I; let g:= thermalD S L
    Solved T a ∧ coeff 0 (out T a)= -coeff 2 (paste f) ∧
        MvPolynomial.homogeneousComponent 3 (coeff 1 (out T a))= -coeff 3 (paste f) ∧
        MvPolynomial.homogeneousComponent 2 (coeff 2 (out T a))= coeff 2 (paste g) ∧
        MvPolynomial.homogeneousComponent 4 (coeff 2 (out T a))= -coeff 4 (paste f) := by
    intro a T f g; have hS:= origin_proof h p hz e;refine ⟨hS,out_main T a hS,?_⟩
    obtain ⟨W,H,H'⟩:= bubbles_pay h p hl 0; obtain ⟨M,U,U'⟩:=bubbles_pay h p hl 1
    let g':= L ∘ scalpel V I; let A:=fort (litR (gateP S)) 1; let B:=fort (litR (gateP S)) 2
    have hA i j: MvPolynomial.IsHomogeneous (A i j) 1:= paste_grade (gateP S i j) _
    obtain ⟨u,v,hu,hv,hQ,hF⟩:=mixed_rate T a hS A B (-coeff 3 (paste f)+coeff 1 (paste g')) (-coeff 4 (paste f)+coeff 2 (paste g')) W M ((veget (q:=q) (S:=S) a 1).trans H) ((veget (q:=q) (S:=S) a 2).trans U) (chord_gate S h 1) H' U' (rect_size (fun i j=>(hA i j).totalDegree_le))
    let Q:= halve ((rhoq q.q*A).trace)
    have hTr: MvPolynomial.IsHomogeneous Q 1:= tally_half _ _ (trace_grade _ _ (beacon T A _ hA))
    rw [hQ,hF]; change MvPolynomial.homogeneousComponent 3 (-_+ coeff 1 (paste g') - Q+ u)= _ ∧_;
    rw [add_assoc (-coeff 4 (paste f)) (coeff 2 (paste g')) _, show coeff 2 (paste g')+curve T A B= coeff 2 (paste g) from (thermal_view h e hp hl).symm]
    simp only [map_add,map_sub, map_neg,MvPolynomial.homogeneousComponent_of_mem (paste_grade _ _), MvPolynomial.homogeneousComponent_of_mem hTr]; rw [MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega : MvPolynomial.totalDegree u<3),MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega : MvPolynomial.totalDegree v<2), MvPolynomial.homogeneousComponent_eq_zero _ _ (by omega : MvPolynomial.totalDegree v<4)]; norm_num
end YM.FormalBulk08.Plait
