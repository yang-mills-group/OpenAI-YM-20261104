import YM.WilsonCoeffUV.Thermo.CoarsePacking
/-! Finite reshape (counting). -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Precision Stationary
open scoped Topology BigOperators
variable {U α β W V ι : Type*}{k r l j:ℕ}
variable (q:U≃α)(v:V≃β)
variable [AddCommGroup W][Module ℝ W]
omit [Module ℝ W] in
lemma bend_sever (x : U)(P:Gen W U): bend q (sever x P)=sever (q x) (bend q P):=by
  unfold bend; funext i y; simp only [turnTen,sever,Pi.smul_apply,prune]; congr 2; rw [← comps_head]; simp
lemma bend_swirl (P:Ten W U r): turnTen q (swirl P)=swirl (turnTen q P):=by funext i; simp only [turnTen,Blue.swirl,Pi.smul_apply, Finset.sum_apply]; rfl
lemma bend_spore (P:Gen ℝ U)(Q:Gen W U): bend q (spore P Q) = spore (bend q P) (bend q Q):=by
  funext i x; simp only [spore,bend,turnTen, Finset.sum_apply]; apply Finset.sum_congr rfl; intro j _; simp only [interweave,dif_pos (Finset.mem_antidiagonal.mp ‹_›)]; rfl
omit [Module ℝ W] in
lemma bend_sum (s:Finset ι)(P:ι→ Gen W U): bend q (∑ i∈s,P i)=∑ i∈s,bend q (P i):=by funext i x; simp only [bend,turnTen,Finset.sum_apply]
lemma bend_smul (p: Gen W U) (c:ℝ): bend q (c•p)= c•bend q p:=rfl
omit [Module ℝ W] in
lemma bend_add (P P': Gen W U): bend q (P+P')= bend q P+bend q P':= rfl
-- use matrix submatrix everywhere to pack.
abbrev allotM (K:Matrix U V ℝ) := K.submatrix q.symm v.symm
variable [Fintype U] [Fintype α]
lemma bend_ripple (G:Matrix U U ℝ)(P:Gen W U): bend q (ripple G P)=ripple (allotM q q G) (bend q P):=by
  unfold ripple; rw [← Equiv.sum_comp q (fun a:α=> _), bend_sum]; apply Finset.sum_congr rfl; intro i _; rw [← Equiv.sum_comp q (fun b:α=> _),bend_sum]; simp_rw [bend_smul,bend_sever,allotM, Matrix.submatrix_apply,Equiv.symm_apply_apply]
lemma bend_arbor (G:Matrix U U ℝ)(P:Gen ℝ U)(Q:Gen W U): bend q (arbor G P Q) = arbor (allotM q q G) (bend q P) (bend q Q):=by
  unfold arbor; rw [← Equiv.sum_comp q (fun a:α=> _), bend_sum]; apply Finset.sum_congr rfl; intro i _; rw [← Equiv.sum_comp q (fun b:α=> _),bend_sum]; simp_rw [bend_smul,allotM, Matrix.submatrix_apply,Equiv.symm_apply_apply]
  apply Finset.sum_congr rfl; intro j _; congr 1; ext1 r
  change turnTen q (swirl _) = _
  rw [bend_swirl]; congr 1; exact congr_fun (by rw [bend_spore,bend_sever,bend_sever] : bend q (spore (sever i P) (sever j Q))=_) _
lemma bend_ravel (G:Matrix U U ℝ)(P:Layers ℝ U)(Q:Layers W U)(h e:ℕ): bend q (ravel G P Q h e)= ravel (allotM q q G) (fun j i=> bend q (P j i)) (fun j i=> bend q (Q j i)) h e:=by simp_rw [ravel,bend_sum,bend_arbor]
lemma bend_abr (G:Matrix U U ℝ)(P:ℕ→Gen ℝ U)(h e): bend q (abr G P h e)=abr (allotM q q G) (fun i=>bend q (P i)) h e := by
  induction h using Nat.strong_induction_on generalizing e with
  | h n ih=>
    cases n with
    | zero=> rw [abr_zero,abr_zero]
    | succ n=>
      have he:= ravel_eq (allotM q q G) (fun j i=> bend q (abr G P j i)) (abr _ (fun i=>bend q (P i))) (fun j i=> bend q (abr G P j i)) (abr _ (fun i=>bend q (P i))) (k:=n) (e:=e) (fun i hi j _=> ih i (by omega) j) (fun i hi j _=> ih i (by omega) j)
      rw [abr_next,bend_smul,bend_add,bend_ripple,bend_ravel,ih n n.lt_succ_self,he,abr_next]
lemma bend_fade (M:Matrix U V ℝ)(P:Gen W U): bend v (fade M P)= fade (allotM q v M) (bend q P):=by
  funext i x; unfold bend turnTen fade; apply Fintype.sum_equiv ((Equiv.refl _).arrowCongr q); intro j;
  change (∏ k,M (j k) (v.symm _)) • P i _= (∏ k, M (q.symm (q (j k))) _) • P i (q.symm ∘ q ∘ j); simp [←Function.comp_assoc]

section Jet
-- pure reindexes rye using literal finite relabel permutation. `r`
lemma rye_gather (f:Lawn U→ℝ)(P:Green f)(k): turnTen q (rye f k)= rye (fun x:Lawn α=> f (x ∘ q)) k:=by
  classical
  let b : Matrix U α ℝ:= Matrix.of fun i j=> if j=q i then 1 else 0
  have hm (x:Lawn α): b *ᵥ x=x ∘ q:=by ext i; unfold Matrix.mulVec dotProduct; rw [Finset.sum_eq_single (q i)]; all_goals simp +contextual [b]
  let F:Gen ℝ U:=shine (rye f k)
  rw [show turnTen q (rye f k)=fade b F k from ?hf, ← show (fun u : Lawn α=> f (b*ᵥ u))= (fun x:Lawn α=> f (x ∘ q)) from ?hk]
  case hk=> simp_rw [hm]
  · have he : Green fun u:Lawn α=> f (b*ᵥ u):=by simp_rw [hm]; exact P.comp (f:=fun u : Lawn α=>u ∘ q) 0 (contDiffAt_pi.mpr fun _=>contDiffAt_apply ℝ ℝ _ _)
    refine unique_kernel (fade_pure (shine_pure (rye_sym P _)) _ _) (rye_sym he _) ?_
    unfold F; rw [fade_one, ← jet_apply,← loom_jet b f P,shine_lit,← jet_apply,loom,PowerSeries.coeff_map]; rfl
  case hf=>
    funext x; unfold fade; let z:=q.symm ∘ x; change _=∑ y,(∏ i,b (y i) (x i)) • F k y
    rw [Finset.sum_eq_single z];
    · have he i : b (z i) (x i)=1:= by unfold b z; simp
      simp_rw [he,show F k=_ from shine_lit _]; simp; rfl
    · intro i _ hh; obtain ⟨j,hj⟩:= Function.ne_iff.mp hh
      have he : b (i j) (x j)=0:= by unfold b; rw [Matrix.of_apply,if_neg]; intro ha; apply hj; simp [z,ha]
      rw [Finset.prod_eq_zero (Finset.mem_univ j) he,zero_smul]
    simp
omit [AddCommGroup W] [Module ℝ W] [Fintype U] [Fintype α] in
lemma lit_bend (P:Ten W U k) [Zero W]: bend q (@shine W U k _ P)=shine (turnTen q P):= by funext i; by_cases h:k=i <;> first | subst k; unfold bend; rw [shine_lit,shine_lit] | unfold bend; rw [shine_dark h,shine_dark h]; rfl
lemma bend_sprig (P:Lawn U→ℝ)(k e)(h:Green P): bend q (sprig P k e)= sprig (fun x:Lawn α=> P (x ∘ q)) k e:=by rw [sprig,sprig,lit_bend,rye_gather _ _ h]
end Jet
end YM.WilsonCoeffUV.Bank
