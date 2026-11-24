import YM.OPE.Compatible.Docks.Bout
/-!
# determinant gain from cofinal contours, allows singular n problem on test shelves. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yolk
open MeasureTheory Function Filter Set
open Lattice RG Wilson Source Labels Source.Drops
open Pill Asymptotics
open Module Finset
open scoped Topology BigOperators Classical ContDiff
variable {I E F J X:Type}{k:ℕ} {f:Filter I}{β p:I→ℝ}{s:ℝ}
section
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
-- finite spectator detection for Kx.M. Guard basis
omit [FiniteDimensional ℝ F] in
lemma GripF (p:J→ E→L[ℝ] F)(h:∀ x:E,(∀ j,p j x=0) →x=0):∃ s:Finset J,Injective (ContinuousLinearMap.pi (fun j:↥s=>p j.val)):=by
       let Q(s:Finset J):E→L[ℝ] ((i:↥s)→ F):= ContinuousLinearMap.pi (fun j:↥s=>p j.val); let C (s:Finset J):= LinearMap.ker (Q s).toLinearMap; have hz(v w:Finset J)(hx:v⊆w): C w ≤ C v:=fun _ hp=> (show Q v _=0 from funext fun i=> congr_fun hp (⟨i.val,hx i.property⟩:↥w))
       let U n:=∃ s:Finset J,finrank ℝ (C s)=n; have he:∃ n:ℕ,U n:= ⟨_,∅,rfl⟩; obtain ⟨u,hu⟩:= (show U (Nat.find he) from Nat.find_spec he); have hp(x:E)(hx:x∈ C u):x=0:=h x (fun i=>by
            let v:=insert i u; have he:C v=C u:=Submodule.eq_of_le_of_finrank_le (hz u v (subset_insert ..)) (hu.trans_le (Nat.find_min' he ⟨v,rfl⟩)); rw [← he] at hx; exact congr_fun (show Q v x=0 from hx) (⟨i,mem_insert_self ..⟩:↥v))
       exact ⟨u,LinearMap.ker_eq_bot.mp (le_antisymm (fun i hi=> (Submodule.mem_bot ℝ).mpr (hp i hi)) bot_le)⟩
omit [FiniteDimensional ℝ F] in
lemma Pointζ (p : I→ E→L[ℝ] F)(q:E→L[ℝ] F)(h:∀ x:E,Tendsto (fun i=>p i x) f (𝓝 (q x))): Tendsto p f (𝓝 q):=by
      let B:= Module.finBasis ℝ E; let T (v:E→L[ℝ] F)(j:Fin (finrank ℝ E)):= (B.coord j).toContinuousLinearMap.smulRight (v (B j)); have hv(w:E→L[ℝ]F): (∑ j,T w j)=w:=by apply ContinuousLinearMap.ext; intro i; rw [_root_.sum_apply]; apply Eq.trans _ (congr_arg w (B.sum_repr i)); rw [map_sum]; simp only[map_smul];rfl
      have hs(j): Tendsto (fun i=> T (p i) j) f (𝓝 (T q j)):= by let S:F→L[ℝ] (E→L[ℝ]F):= ContinuousLinearMap.smulRightL ℝ E F ((B.coord j).toContinuousLinearMap); exact S.continuous.continuousAt.tendsto.comp (h (B j))
      simpa only [hv] using tendsto_finsetSum (s:=univ) (f:=fun j i=>T (p i) j) fun j _=>hs j
lemma WarmInv {x:E→L[ℝ] E}(hx:‖x-ContinuousLinearMap.id ℝ E‖ ≤ 1/2): ∃ v:E≃L[ℝ] E, v.toContinuousLinearMap=x ∧ ‖v.symm.toContinuousLinearMap‖ ≤ 2:=by
       have he(a:E): ‖a‖≤2*‖x a‖:=by
            have ht:= ((x-ContinuousLinearMap.id ℝ E).le_opNorm a).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _)); change ‖x a-a‖ ≤ _ at ht; rw[norm_sub_rev] at ht; linarith only [ht,norm_sub_norm_le a (x a)]
       have hp:Injective x.toLinearMap:= LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.2 fun i h=> norm_le_zero_iff.mp ((he i).trans_eq (by rw [show x i=0 from h,norm_zero,mul_zero])))
       let v:= (LinearEquiv.ofBijective x.toLinearMap ⟨hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hp⟩).toContinuousLinearEquiv
       refine ⟨v,ContinuousLinearMap.ext (fun i=>rfl),v.symm.toContinuousLinearMap.opNorm_le_bound (by norm_num) fun i=>?_ ⟩; exact (he (v.symm i)).trans_eq (by rw [show x (v.symm i)=i from v.apply_symm_apply i])
lemma rayCou (hx:Tendsto β f atTop)(p:J→ I→ F→L[ℝ] ℝ)(X:I→ E→L[ℝ] F) (Q:J→ E→L[ℝ] ℝ) (h:∀ j, Wax β f (p j) 0)(he:∀ x:E, (∀ j,Q j x=0)→x=0) (hp:∀ x:E,∀ j,Tendsto (fun i=>p j i (X i x)) f (𝓝 (Q j x))) (ht:Nonempty (E≃ₗ[ℝ] F)): ∃ U:I→ F→L[ℝ] E, Wax β f U 0 ∧∀ᶠ i in f, (U i).comp (X i)= ContinuousLinearMap.id ℝ E ∧ (X i).comp (U i)=ContinuousLinearMap.id ℝ F:=by
       obtain ⟨s,hS⟩:= GripF Q he; let z:E→L[ℝ] (↥s→ℝ):= ContinuousLinearMap.pi (fun i:↥s=>Q i.val); let U(i:I): F→L[ℝ] (↥s→ℝ):= ContinuousLinearMap.pi fun j:↥s=>p j.val i; let C: (↥s→ℝ)→L[ℝ] E:= z.toLinearMap.leftInverse.toContinuousLinearMap; have hv(x:E):C (z x)=x:= LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hS) _
       let Y(i:I):= C ∘L (U i ∘L X i); have hh: Tendsto Y f (𝓝 (ContinuousLinearMap.id ℝ E)):= Pointζ Y _ fun x=> by
            apply (show Tendsto C _ _ from ?_).comp (show Tendsto (fun i:I=>U i (X i x)) f (𝓝 (z x)) from tendsto_pi_nhds.mpr (fun i=>hp x i.val)); have he:= C.continuous.tendsto (z x); rw [hv] at he; exact he
       have hY:∀ᶠ i in f, ‖Y i-ContinuousLinearMap.id ℝ E‖≤ 1/2:= (hh.sub_const _|>.norm).eventually (ge_mem_nhds (by simp)) -- orient
       classical
       choose! V hV hu using fun (i:I)(h:‖Y i - ContinuousLinearMap.id ℝ E‖≤1/2)=> WarmInv h; let A(i):=if ‖Y i-ContinuousLinearMap.id ℝ E‖≤1/2 then (V i).symm.toContinuousLinearMap else 0; let U'(i):= A i ∘L (C ∘L U i); have hA: ∀ᶠ i in f,‖A i‖≤ 2:=hY.mono fun i hi=>by unfold A; split; exact hu i hi; contradiction
       have hC:=carth hx; have hU:Wax β f U 0:= RateLE.of_norm_le (RateLE.sum (S:=Finset.univ) (f:=fun i:↥s=>fun j=>‖p i.val j‖) hC (fun i _=> (h i.val).norm)) (Eventually.of_forall fun i=>?_); rotate_left
       · -- π bound
         exact (U i).opNorm_le_bound (show 0 ≤ ∑ j:↥s,‖p j.val i‖ from Finset.sum_nonneg fun _ _=> norm_nonneg _) (fun x=> (pi_norm_le_iff_of_nonneg (mul_nonneg (sum_nonneg fun _ _=>norm_nonneg _) (norm_nonneg _))).2 (fun j=> ((p j.val i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (single_le_sum (f:=fun j:↥s=> ‖p j.val i‖) (fun _ _=> norm_nonneg _) (mem_univ j)) (norm_nonneg _))))
       refine ⟨U', ?_, ?_⟩; · simpa only [add_zero] using Paintζ A (Paintζ (fun _=>C) hU _ (RateLE.const C hC)) 0 (RateLE.absBound _ hC hA)
       filter_upwards [hY] with i hi; let Z:= V i; have h₀(j):U' i (X i j)=j:=by unfold U'; rw [ContinuousLinearMap.comp_apply,show A i=Z.symm.toContinuousLinearMap from if_pos hi]; exact Eq.trans (congr_arg Z.symm ((show Z (show E from j)=Y i j from DFunLike.congr_fun (hV i hi) j).symm)) (Z.symm_apply_apply j)
       have hs: Surjective (X i).toLinearMap:=(LinearMap.injective_iff_surjective_of_finrank_eq_finrank ht.some.finrank_eq).mp (LeftInverse.injective h₀)
       refine ⟨ContinuousLinearMap.ext h₀,ContinuousLinearMap.ext fun j=>?_⟩; obtain ⟨j,rfl⟩:=hs j; exact congr_arg (X i) (h₀ j)
end
end YM.OPE.Yolk
