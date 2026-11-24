import YM.WilsonCoeffUV.Wick.Identity
import YM.WilsonCoeffUV.Root.Gain.Polynomial
/-! More API for distinguished-root alias. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank.Carp
open Set Function Filter Lattice RG Laurent Exterior Bloch Metric Next.Free Precision Tree Soil
open Matrix FreeResolvent Blue Power Work.F08
open scoped Topology ContDiff BigOperators ComplexConjugate Classical
variable {U V P I:Type*}{G:Gauge}{j k m N:ℕ}{n:Side} {s t A B C:ℝ} {w:Cover}
section
variable [NormedAddCommGroup V]
lemma pegadd (F H: Ten V (Cloth P) j) (n:Side)(x): peglet (F+H) n x=peglet F n x + peglet H n x:=by funext y; unfold peglet; by_cases t:slideC n y=x<;>simp [t]
variable [Fintype P][CompleteSpace V]
omit [CompleteSpace V] in
lemma downA (F:Ten V (Cloth P) j)(h:Cork Bank.terrain w s A F)(hp:0<t)(hb:t<s)(n:Side) : Cork (tor n) (wrap n w) t (A*tiePay P j (s-t)) (plume F n) := by
    refine ⟨?_ ,fun y=> (norm_tsum_le_tsum_norm (clothBound h hp hb y).2.1).trans ((clothBound h hp hb y).2.2.trans_eq (by rw [mul_right_comm]))⟩
    exact mul_nonneg h.1 (by by_cases hx : j=0; · simp [hx,tiePay]
                             exact pow_nonneg (boardPay_nn (div_pos (sub_pos.mpr hb) (by positivity))) _)
lemma plume_add {F H: Ten V (Cloth P) j}(p:Cork Bank.terrain w s A F)(q:Cork Bank.terrain w t B H)(he:0<s)(hp:0<t)(n:Side): plume (F+H) n= plume F n+plume H n:= funext fun x=>by rw [plume,pegadd]; simp only [Pi.add_apply]; exact (creased p he n x).tsum_add (creased q hp n x)
omit [Fintype P] [CompleteSpace V] in
lemma sigma_cap (Q:I→ Ten V (Cloth P) j)(B:I→ℝ)(h:∀ i,Cork Bank.terrain w s (B i) (Q i))(_p:0<s)(q:SumBudget B A) : Cork Bank.terrain w s A fun x=>∑' i,Q i x:=by
    refine ⟨cap_nn q,fun x=>?_⟩
    let u:=Real.exp (-s*tread Bank.terrain w x); have hp:0≤u:=by unfold u; positivity
    have hu i: ‖Q i x‖≤B i *u:=(h i).2 _
    have hh:=q.2.1.mul_right u; have hv:= hh.of_nonneg_of_le (fun i=>norm_nonneg _) hu
    exact (norm_tsum_le_tsum_norm hv).trans ((hv.tsum_le_tsum hu hh).trans (by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right q.2.2 hp))
lemma plume_budget (Q:I→ Ten V (Cloth P) j)(B:I→ℝ)(h:∀ i,Cork Bank.terrain w s (B i) (Q i))(p:0<s)(q:SumBudget B A)(n:Side)(x): HasSum (fun i=> plume (Q i) n x) (plume (fun y=>∑' i,Q i y) n x):=by
    let u:=s/2; have hu:0<u:=half_pos p; have ht:u<s:=half_lt_self p
    let F: I × dock Cover P j → V:= fun i=> peglet (Q i.1) n x i.2
    have hh (i): SumBudget (fun y : dock Cover P j=> ‖F (i,y)‖) ((B i*Real.exp (-u*tread (tor n) (wrap n w) x))*tiePay P j (s-u)):=clothBound (h i) hu ht x
    have hg: Summable F:= by
       apply Summable.of_norm; apply (summable_prod_of_nonneg (fun y=>norm_nonneg (F y))).mpr; refine ⟨fun i=> (hh i).2.1,Summable.of_nonneg_of_le (fun i=>tsum_nonneg fun y=>norm_nonneg _) (fun i=>(hh i).2.2) ?_⟩; exact (q.2.1.mul_right _).mul_right _
    let Z:= Equiv.prodComm (dock Cover P j) I; have hz: Summable (F ∘ Z):= Z.summable_iff.mpr hg
    have hm : plume (fun y=>∑' i,Q i y) n x=tsum F:=by
       unfold plume; rw [← Z.tsum_eq]
       change _=tsum (F ∘ Z); rw [hz.tsum_prod]; apply tsum_congr; intro i
       unfold peglet F; simp only [Function.comp_apply, show ∀ j i,Z (j,i)=(i,j) from fun _ _=> rfl]; split<;>rename_i H
       · simp only [peglet,H,↓reduceIte]
       simp only [peglet,if_neg H,tsum_zero]
    rw [hm,hg.tsum_prod]; change HasSum (fun i=> plume _ n x) (∑' i,plume (Q i) n x); exact hg.prod.hasSum
variable {W:Type*}[NormedAddCommGroup W][NormedSpace ℝ V][NormedSpace ℝ W]
lemma plume_map (F:Ten V (Cloth P) j)(p:Cork Bank.terrain w s A F)(h:0<s)(L:V→L[ℝ]W)(n:Side): plume (L ∘ F) n=L ∘ plume F n:=by
   funext x; unfold plume; rw [Function.comp_apply, L.map_tsum (creased p h n x)]; refine tsum_congr fun i=>?_ ; unfold peglet; by_cases h:slideC n i=x<;>simp [h]
end
-- evaluations on pulled-back potentials. Ink reserve.
open Cosmos Stationary
variable [NormedAddCommGroup V][NormedSpace ℝ V][CompleteSpace V]
def caustic (T:Ten V (Co n P) j)(v:Fin j→(Co n P→ℝ))[Fintype P]:= ∑ x:Fin j→ Co n P,(∏ i,v i (x i)) • T x
lemma chordal (T:Ten V (YForest G) j)(p:Cork Bank.terrain 0 s A T)(h:0<s)(v:Fin j→Link G n) : caustic (plume T n) v=pluck T (fun i=>v i ∘ foldUnder n):=by
   unfold caustic plume; simp_rw [←tsum_const_smul''];
   rw [← Summable.tsum_finsetSum (fun i _=> (creased p h n i).const_smul _)]; refine tsum_congr fun y=> ?_
   rw [Finset.sum_eq_single (slideC n y)]; unfold peglet; rw [if_pos rfl]; rfl
   · intro i _ hi; rw [peglet, if_neg (Ne.symm hi), smul_zero]
   simp
end YM.WilsonCoeffUV.Bank.Carp
