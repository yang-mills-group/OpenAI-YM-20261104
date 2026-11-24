import YM.AveragedStep.Recursion.Corona
/- Pinned cross table, volumes universal and OFF support entries. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
variable {c f:Side}{G:Gauge}{S:StepData c f}(h:S.patch.Branches S.kernel G)

abbrev Cabin (G:Gauge)(c:Side):= Edge (Site c)× G.ColorIndex
def hatch (x:Cabin G c):Ink G c f := (Sum.inr x.1,x.2)
abbrev fkey (F:Forest S.ratio)(i:Key F G): Ink G c f:= fieldKey F i.1 i.2
def bracken (S:StepData c f)(A:ChartRatio G)(F:Forest S.ratio)(k:Key F G)(j:Cabin G c):ℝ:=tier S A (Sum.inl k.1.val) (fingers G k.2) 0 (dart (hatch j))
def pin (F:Forest S.ratio)(Y:Hand G c f):Prop:=∀ e∈F.trunks,Y (Sum.inl e)=0
lemma chamber_pin (F:Forest S.ratio)(A:ChartRatio G)(Q:Cuff S.patch S.kernel A)(x:Site c)(τ:ℝ)(p:TopologyQ F G):pin F (hands F Q x τ p):=by
 intro e he
 change τ • Q.logC (F.drape p.1 e)=0
 rw [show F.drape p.1 e=1 from F.on_tree p.1 ⟨e,he⟩,← G.mat_lieExp_zero, Q.wind_id]
 · simp
 rw [norm_zero]; have ht:=Q.active; positivity
private lemma through (F:Forest S.ratio)(P:Edge (Site f)→ℝ)(he:∀ i∈F.trunks,P i=0):∑ i:F.Free,P i = ∑ i:Edge (Site f),P i:=by
 let T:=Finset.univ.filter (fun i:Edge (Site f)=>i∉F.trunks)
 let i:F.Free→ Edge (Site f):= Subtype.val
 refine Eq.trans (b:=∑ i∈T,P i) ?_ (Finset.sum_subset (Finset.subset_univ T) (fun x _ h=>?_))
 · refine Finset.sum_bij' (fun j _=>i j) (fun j hj=>⟨j,?_⟩) ?_ ?_ ?_ ?_ (fun _ _=>rfl)
   all_goals simp_all [T,i]
 exact he _ (by simpa only [T,Finset.mem_filter, Finset.mem_univ,true_and,not_not] using h)

include h in
lemma linear_out (A:ChartRatio G)(F:Forest S.ratio)(i:Key F G)(Y:Hand G c f)(hP:pin F Y) :tier S A (Sum.inl i.1.val) (fingers G i.2) 0 Y =
   (∑ j:Key F G,body A F i j * mon [fkey F j] Y)+(∑ j:Cabin G c, bracken S A F i j * mon [hatch j] Y):=by
 let z:=fkey F i
 let L := fderiv ℝ (fderiv ℝ (tabulate S (G:=G))) 0
 have he(X:Hand G c f):tier S A (Sum.inl i.1.val) (fingers G i.2) 0 X=L X (dart z):=(tab_price h A z X).trans (by rw [iteratedFDeriv_two_apply]; rfl)
 have hd:=congrArg (fun v=>L v (dart z)) (dart_sum Y)
 rw [map_sum,_root_.sum_apply] at hd
 simp_rw [map_smul,_root_.smul_apply,smul_eq_mul] at hd
 rw [he,← hd,Fintype.sum_prod_type,Fintype.sum_sum_type]
 dsimp only
 conv_rhs=> lhs; rw [Fintype.sum_prod_type]
 conv_rhs=> rhs; rw [Fintype.sum_prod_type]
 rw [← through F (fun x=>∑ i',dashMark (Y (Sum.inl x)) i' * L (dart (Sum.inl x, i')) (dart z)) (fun x hx=>by simp [hP x hx,dashMark])]
 apply congrArg₂
 · apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro i' _; unfold body fkey fieldKey
   rw [of_apply,he,back_take,mon_cons,mon_nil,mul_one]
   exact mul_comm ..
 apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro i' _; unfold bracken hatch; rw [he,mon_cons,mon_nil,mul_one]; exact mul_comm ..
include h in
lemma bracken_keeps (A:ChartRatio G)(F:Forest S.ratio)(k:Key F G)(j:Cabin G c)(hv:bracken S A F k j ≠ 0): Sum.inr j.1 ∈ home S (Sum.inl k.1.val):=by
 by_contra! he
 exact hv (by
    unfold bracken tier; rw [if_pos rfl,sub_zero]; apply Finset.sum_eq_zero
    intro p hp; rw [tooths h,dart]
    exact (by dsimp only [hatch]; rw [pick_zero p (fun h'=> he (home_owner S hp (own_need S h'))), map_zero]; rfl))
lemma bracken_bound (A:ChartRatio G)(P:Patch)(K:KernelChoices):∃ B:ℝ,0≤B∧ ∀{c f:Side}(S:StepData c f)(F:Forest S.ratio),S.patch=P→S.kernel=K→∀ (k:Key F G)(j:Cabin G c), |bracken S A F k j|≤B:=by
 choose B h hB using (fun i:G.ColorIndex=> tier_cost P K A (fingers G i) 0)
 refine ⟨∑ i,B i,Finset.sum_nonneg (fun i _=>h i),fun {c f} S F hP hK k j=>?_⟩
 exact le_trans (by simpa only [one_pow,mul_one,bracken] using (hB k.2 S hK hP (Sum.inl k.1.val) (dart (hatch j)) (r:=1) le_rfl (fun i _=> dart_unit ..))) (Finset.single_le_sum (fun i _=>h i) (Finset.mem_univ _))
end YM.AveragedStep
