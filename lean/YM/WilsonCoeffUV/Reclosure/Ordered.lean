import YM.WilsonCoeffUV.Reclosure.CurlTorus
/-!
# Ordered path representation exactly the PERIODIZED scalar kernels
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Mosaic
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Stationary
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{c:Side}{N M e m i k r t:ℕ}{α:Type*}
variable {F:post G t}{s S a A:ℝ}

section star
variable (F) (p:Fin (t+1) → Site c)(v:Haze G (t+1))(i: Run (t+1))

def caseX (x: Site c) (w:Shift (Keys t)): stars G t c:=fun j=> (x+wrap c (feetP w j),i j,v j)
lemma case_head (x:Site c)(w:Shift (Keys t)):caseX v i x w 0=(x,i 0,v 0):=by simp [caseX,feetP]
lemma case_fit (x:Site c)(w:Shift (Keys t)): trope (caseX v i x w) w:=by intro j; rw [case_head]; change x+_-x=_; abel
lemma case_flair (x : Site c) (w): flair (caseX v i x w) F w=plantern F v i w:= by rw [flair_hit (case_fit v i x w)]; rfl

def wavePower (X:stars G t c): ℂ:= ∏ j,glyph p v i j (X j)

lemma verse (S:Finset (Fin (t+1)))(b:Site c) : ∏ i∈S, cell (p i) b=cell (∑ i∈S,p i) b:=by
   induction S using Finset.induction_on with
   | empty=> simp [cell]
   | @insert j S h ih=> rw [Finset.prod_insert h, Finset.sum_insert h,ih, cell_duality (p j+_) b,cell_add,cell_duality b,cell_duality b]
lemma verse_prod (w:Shift (Keys t)): ∏ j,cell (p j) (wrap c (feetP w j)) = mode (outphase p) w:=by
   rw [Fin.prod_univ_succ]; simp_rw [cell_wrap]; simp only [feetP,Fin.cons_zero,mode_zero,Fin.cons_succ,one_mul]
   unfold mode; rw [Fintype.sum_prod_type, Finset.mul_sum, Complex.exp_sum]; rfl
lemma wave_price (w)(x:Site c): wavePower p v i (caseX v i x w)=cell (∑ j,p j) x * mode (outphase p) w:=by
    unfold wavePower; rw [← verse_prod,← verse, ← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro j _; unfold glyph relay tune caseX; simp [cell_add]
lemma nub (X:stars G t c)(w) (h:flair X F w≠0)(e: wavePower p v i X≠0) : X= caseX v i (X 0).1 w:=by
   have he:trope X w:= by by_contra hr; exact h (flair_miss hr)
   funext j; refine Prod.ext ?_ ?_
   · change _=(X 0).1+ _; rw [← he]; abel
   by_contra H; apply e; apply Finset.prod_eq_zero (Finset.mem_univ j); unfold glyph relay tune; simp only [Pi.single_apply]; rw [if_neg (show ¬(X j).2=(i j,v j) from H),mul_zero]
lemma buyers (w:Shift (Keys t)): ∑ X:stars G t c, wavePower p v i X*(flair X F w:ℂ)=(∑ x:Site c,cell (∑ j,p j) x)*(mode (outphase p) w * (plantern F v i w:ℂ)) := by
    let b (i':Site c):= caseX v i i' w
    let f (x:stars G t c):= wavePower p v i x*(flair x F w:ℂ)
    have he: Injective b:=fun i j e=>by have H:= congr_fun e 0; unfold b at H; simp_rw [case_head] at H; exact congr_arg Prod.fst H
    change ∑ i,f i=_; calc
      _ = ∑ i∈Finset.univ.image b, f i:= Eq.symm (Finset.sum_subset (Finset.subset_univ _) (fun x _ H=>?_))
      _ = _:=by rw [Finset.sum_image (fun _ _ _ _ q=> he q), Finset.sum_mul]; apply Finset.sum_congr rfl; intro i' _; unfold f; rw [ show b i'=caseX v i i' w from rfl, wave_price,case_flair]; ring
    by_cases h:wavePower p v i x=0; · unfold f; simp [h]
    by_cases e:flair x F w=0; · unfold f; simp [e]
    exact False.elim (H (Finset.mem_image.mpr ⟨(x 0).1, Finset.mem_univ _, (nub F p v i x w e h).symm⟩))
lemma polar (h:Amber terrain s A F)(he:0<s) : recording (ι:=Fin (t+1)) (fun i=>(lagoon F c i:ℂ)) (glyph p v i)=collected (pictures F) p v i:=by
    have hK (x:stars G t c): Summable (fun w=> (flair x F w:ℂ)) := Complex.ofRealCLM.summable ((flair_cost h he x).summable (hinge_paid he _).le)
    rw [recording_apply]; change ∑ x:stars G t c, wavePower p v i x * ((∑' w, flair x F w):ℝ)= _
    simp_rw [Complex.ofReal_tsum, ← tsum_mul_left]; rw [← Summable.tsum_finsetSum (f:=fun x w=> wavePower p v i x*(flair x F w:ℂ)) (fun x _=> (hK x).mul_left _)]; simp_rw [buyers]; rw [tsum_mul_left,collected]; split <;> rename_i hp
    · rw [hp]; simp [cell]; rfl
    rw [sum_cell hp,zero_mul]
end star
lemma ink_etched [NeZero t]{P:Skin G t}(hp:0<S)(h:Amber terrain s A F)(he:0<s)(g:Shades P (pictures F) S a)(m:Side): enlarge (volumeInk m (issue P)).toMultilinearMap= recording (ι:=Fin (t+1)) (fun j=>(lagoon F m j:ℂ)):= by
    apply relay_ext; intro p; let c j:= (p j).2
    exact (notesPath hp g (fun i=> (p i).1) (fun i=> (c i).2) (fun i=> (c i).1)).trans (polar F _ _ _ h he).symm
lemma records_unit {X α:Type}[Fintype α][DecidableEq α]{ι:Type}[Fintype ι][DecidableEq ι][CommSemiring X](A:(ι→α)→X)(v:ι→α): recording A (fun j=> Pi.single (v j) 1)= A v:=by
    rw [recording_apply,Finset.sum_eq_single v]; · simp
    · intro i _ p
      obtain ⟨j,hj⟩:= not_forall.mp (mt funext p)
      rw [Finset.prod_eq_zero (Finset.mem_univ j),zero_mul]
      rw [Pi.single_eq_of_ne hj]
    simp
-- inkBeat consistency in ordered grammar (Tensor.sym will cost permutation only if not symmetric F)
lemma vial [NeZero t]{P:Skin G t}(hp:0<S)(h:Amber terrain s A F)(he:0<s)(g: Shades P (pictures F) S a)(m:Side): (volumeInk m (issue P)).toMultilinearMap = recording (ι:=Fin (t+1)) (lagoon F m):=by
    apply enlarge_inj
    rw [ink_etched hp h he g m]; congr 1; funext i; rw [records_unit]

-- real tensor corr
lemma ink_part {k:ℕ} {I:Type}[Fintype I][DecidableEq I]{Q:Ten ℝ I k} {X:_root_.YM.Tensor.T (Lawn I) ℝ k}(h:Blue.Smooth Q)(p:X.toMultilinearMap=recording Q) : _root_.YM.Tensor.symmetrize X=X:=by
    ext1 v; unfold Tensor.symmetrize; rw [_root_.smul_apply, _root_.sum_apply];
    have he j: X v = X.domDomCongr j v:=by
        change X.toMultilinearMap v = X.toMultilinearMap (v ∘ j); rw [p,recording_apply,recording_apply]; simp only [Function.comp_apply]; rw [← Equiv.sum_comp (Equiv.arrowCongr j.symm (Equiv.refl I)) (fun i=> (∏ a:Fin k, v (j a) (i a))*Q i)]
        apply Finset.sum_congr rfl; intro i _; change (∏ a, v a (i a))*Q i=(∏ a,v (j a) (i (j a)))*Q (i ∘ j); rw [h]; exact congr_arg (· * Q i) ((Equiv.prod_comp j (fun a=> v a (i a))).symm)
    simp_rw [← he]; simp only [Finset.sum_const, Finset.card_univ]; rw [← Nat.cast_smul_eq_nsmul ℝ,inv_smul_smul₀ (by positivity)]
lemma fiscal_vol (z : Lawn (Woods G c) →ℝ)(r)(x: Fin r→ Woods G c): rye z r x= Tensor.coeff z r 0 (fun i=> Pi.single (x i) 1):=by unfold rye Tensor.coeff; rw [_root_.smul_apply]; congr; ext1 i; funext j; by_cases h:j=x i<;>simp [Blue.pebble,h]
lemma proof_marks [NeZero t]{P:Skin G t}(hp:0<S)(h:Amber terrain s A F)(he:0<s)(p:Blue.Smooth F)(hx:stroll F)(g: Shades P (pictures F) S a)(n:Side): rye (seriesScore n (issue P)) (t+1)=lagoon F n:=by
    funext x; have hu:= total_ink n (issue P) hp (artery_funded g).1
    rw [fiscal_vol,hu, ink_part (lagoon_smooth F p hx n) (vial hp h he g n)]
    change ((volumeInk n (issue P)).toMultilinearMap _)=_; rw [vial hp h he g,records_unit]
end YM.WilsonCoeffUV.Bank.Mosaic
