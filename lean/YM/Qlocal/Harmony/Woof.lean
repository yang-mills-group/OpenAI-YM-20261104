import YM.Push.ABSOLUTE_SUMS.Array
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Absolute convergence for marker inventories.

These lemmas will be used to resolve an analytic kernel **before** knowing the values of tests
on it. Need convergence even for infinite layouts / projections not actively being probed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony
open Set Filter Function Finset RG Push.AbsoluteSums
open scoped Classical BigOperators Topology
variable {I : Type*} [Fintype I] [DecidableEq I] {α : I→Type*}

lemma inventory (c:∀ i,α i→ℝ) {h:I→ℝ} (H:∀ i,SumBudget (c i) (h i)):
    SumBudget (fun x:∀ i,α i => ∏ i,c i (x i)) (∏ i,h i):= by
 let f (x:∀ i,α i):= ∏ i,c i (x i)
 have he (x): 0 ≤ f x:= prod_nonneg (fun i _=>(H i).1 _)
 refine budget_of_sum he ?_
 intro S
 change ∑ i∈S,f i ≤ _
 let C (i:I):= S.image (fun x=> x i)
 refine (sum_le_sum_of_subset_of_nonneg (f:=f) (s:=S) (t:=Fintype.piFinset C) (fun x hx=> Fintype.mem_piFinset.mpr fun i=> mem_image_of_mem _ hx) (fun i _ _=> he i)).trans ?_
 unfold f; rw [← prod_univ_sum]
 exact Finset.prod_le_prod (fun i _=> sum_nonneg (fun j _=> (H i).1 j)) (fun i _=> budget_sum (H i) _)

section
variable {E:I→Type*} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℝ (E i)]
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [∀ i, FiniteDimensional ℝ (E i)]

-- Same argument as `SchemeBridge.Formal.canvased`, without any uniformity claim in dimension.
lemma continuous_poly (T: MultilinearMap ℝ E V): Continuous T:= by
 let a(i):=Module.finBasis ℝ (E i)
 let f(i)(j:Fin (Module.finrank ℝ (E i))) : E i→ₗ[ℝ]ℝ:= (a i).coord j
 have hx(x): T x=∑ y:∀ i, Fin (Module.finrank ℝ (E i)), (∏ i,f i (y i) (x i)) • T (fun i=>a i (y i)):= by
    conv_lhs=> rw [show x=(fun i=> ∑ j,f i j (x i)•a i j) from funext (fun i=> ((a i).sum_repr (x i)).symm)]
    rw [T.map_sum (fun i j=> f i j (x i) • a i j)]; exact Finset.sum_congr rfl fun i _=>T.map_smul_univ _ _
 rw [funext hx]; apply continuous_finsetSum; intro i _; refine Continuous.smul ?_ continuous_const
 apply continuous_finsetProd; intro j _; exact (f j (i j)).continuous_of_finiteDimensional.comp (continuous_apply _)

lemma resolves [CompleteSpace V] (T:MultilinearMap ℝ E V) (v:∀ i, α i→ E i)
    {x:∀ i,E i} (h:∀ i,HasSum (v i) (x i)) :
    HasSum (fun j:∀ i, α i=> T (fun i=> v i (j i))) (T x):= by
 -- Rectangles are cofinal, but since signs vary, need *absolute* convergence first.
 let p (C:∀ i,Finset (α i)):= Fintype.piFinset C
 have hp:Tendsto p atTop atTop:= by
    refine tendsto_atTop_atTop.mpr fun t=> ⟨fun i=>t.image fun f=>f i,fun s hs=>?_⟩
    intro x hx; exact Fintype.mem_piFinset.mpr fun i=> hs _ (mem_image_of_mem (fun x=>x i) hx)
 let w (i):=fun j: α i=> ‖v i j‖
 let A(j:∀ i, α i):= T (fun i=>v i (j i))
 have he(i): Summable (w i):= summable_norm_iff.mpr (h i).summable
 have hw(i): SumBudget (w i) (∑' j, w i j):= ⟨fun j=>norm_nonneg _,he _,le_rfl⟩
 let U: ContinuousMultilinearMap ℝ E V:= ⟨T,continuous_poly T⟩
 have ht: Summable A:= Summable.of_norm_bounded ((inventory w hw).2.1.mul_left ‖U‖) (fun j=> U.le_opNorm _)
 let f (t:∀ i,Finset (α i))(i:I):= ∑ j∈t i, v i j
 have hf:Tendsto f atTop (𝓝 x):= tendsto_pi_nhds.mpr (fun i => ?_)
 · have hA:Tendsto (fun i:∀ j,Finset (α j)=>∑ j∈ p i,A j) atTop (𝓝 (∑' i,A i)):= ht.hasSum.comp hp
   have hC:Tendsto (fun i=> T (f i)) atTop (𝓝 (T x)) := ((continuous_poly T).tendsto x).comp hf
   have hx(x:∀ i,Finset (α i)): T (f x)=∑ j∈p x,A j:= MultilinearMap.map_sum_finset T v x
   exact (tendsto_nhds_unique (hC.congr hx) hA).symm ▸ ht.hasSum
 refine (show Tendsto (fun t:Finset (α i)=>∑ j∈t,v i j) atTop (𝓝 (x i)) from h i).comp ?_
 refine tendsto_atTop_atTop.mpr fun j=> ⟨Function.update (fun k=> ∅) i j,fun t ht=>?_⟩
 exact (by simpa only [Function.update_self] using ht i : j⊆t i)

/-- Multilinear inventory factorizing through finite jets. -/
lemma distribute [CompleteSpace V] {X:Type*} [AddCommGroup X] [Module ℝ X]
    (L: MultilinearMap ℝ (fun _:I=>X) V) (v:∀ i, α i→ X) (f:∀ i:I,X→ₗ[ℝ] E i)
    (he:∀ (x y:I→X), (∀ i,f i (x i)=f i (y i))→ L x=L y)
    (a:∀ i, α i →ℝ) (x:I→X) (h:∀ i,HasSum (fun j=>a i j • f i (v i j)) (f i (x i))) :
    HasSum (fun z:∀ i,α i=> (∏ i:I,a i (z i)) • L (fun i=> v i (z i))) (L x):= by
 let P i:= (f i).rangeRestrict
 have hs(j:I): HasSum (fun i=> a j i • (P j (v j i))) (P j (x j)):= by
    apply (Submodule.isEmbedding_subtype (LinearMap.range (f j))).tendsto_nhds_iff.mpr
    exact (h j).congr (fun _=> by rw [Function.comp_apply,map_sum]; rfl)
 choose g hg using fun (j:I)=> (P j).exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
 let M:= L.compLinearMap g
 have hx (Y:I→X): M (fun j=> P j (Y j))= L Y:= he (fun j=>g j (P j (Y j))) Y (fun j=> congr_arg Subtype.val (LinearMap.congr_fun (hg j) (P j (Y j))))
 have hM:= resolves M _ hs; rw [hx x] at hM; exact hM.congr_fun (fun z=> (by change _=M _; rw [MultilinearMap.map_smul_univ (c:=fun i:I=>a i (z i)) (m:=fun j=>P j (v j (z j))), hx (fun i=>v i (z i))]))
end

-- Collect finite outer labels. (One of the factors can be the void family.)
section
variable {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    {κ:Type*}
omit [DecidableEq I]
lemma assemble_sigma {f: Sigma α→V}{g:I→V}
    (h:∀ i,HasSum (fun j:α i=>f ⟨i,j⟩) (g i)): HasSum f (∑ i,g i):= by
 have hb(i:I):= summable_norm_iff.mpr (h i).summable
 let t(i:I):= ∑' j:α i,‖f ⟨i,j⟩‖
 have ht: Summable (fun i=> ‖f i‖):= (sigma_total (fun i=>‖f i‖) t (fun i=> ⟨fun j=>norm_nonneg _,hb _,le_rfl⟩) (budget_finite (fun i=> tsum_nonneg (fun _=> norm_nonneg _)) (le_refl _))).2.1
 have hf:= ht.of_norm
 rw [show (∑ i,g i)=(∑' j,f j) from ?_]; · exact hf.hasSum
 rw [Summable.tsum_sigma hf]; simp_rw [(h _).tsum_eq, tsum_fintype]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
lemma file_product {f:I×κ→ V}{g:κ→V}
    (h:Summable f) (hg:∀ j, (∑ i:I, f (i,j))=g j): HasSum g (∑' x,f x):= by
 let p:=Equiv.prodComm κ I
 have ht: Summable (f ∘ p):= h.comp_injective p.injective
 rw [← Equiv.tsum_eq p f]
 apply ht.hasSum.prod_fiberwise
 intro b
 change HasSum (fun i:I=> f (i,b)) _
 rw [←hg b]; exact hasSum_fintype ..
-- variant where given inner HasSum over first slot instead
lemma flatten_product {f:I×κ→V}{g:I→V}(H:∀ i,HasSum (fun j=> f (i,j)) (g i)): HasSum f (∑ i,g i):=
 ((Equiv.sigmaEquivProd I κ).hasSum_iff).1 (assemble_sigma (α:=fun _=>κ) H)
end
end YM.Qlocal.Harmony
