import YM.OPE.Compatible.Aroma.Cord
/-! # Row gear and seams -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Maxwell Exterior Tensor WithLp Work.F08 Matrix Bloch Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical
variable {r d' m n j:ℕ}{b e s:ℝ}{I J W K:Type*} {L: Side}
namespace Script
open Page
variable {B: Row I J}
def meetsX (B:Row I J)(x:fieldX J): fieldX I:=fun p=>∑' j:Cover×J,B p.2 j.2 j.1*x (p.1+j.1,j.2)
section
variable [Fintype J]{v:fieldX J}
lemma meets_current (hp:Whole B)(h:Quiet v d') (z:Cover)(p:I): Summable fun j:Cover×J=> B p j.2 j.1*v (z+j.1,j.2):=by
    obtain ⟨s,b,hs,g⟩:=hp; obtain ⟨c,hc,H⟩:=h; exact (stintCost g hs _ (z,p) _ v hc H).2.1.of_norm
lemma meets_finite (hp:Whole B)(x:deck J L): meetsX B (unfoldX x)=unfoldX ((B.acts L) *ᵥ x):=by
    have he : Quiet (unfoldX x) 0:= ⟨‖x‖,norm_nonneg _, fun i=>(norm_le_pi_norm x _).trans_eq (by unfold poise; ring)⟩
    ext1 i; unfold meetsX unfoldX; erw [Matrix.mulVec, dotProduct,Fintype.sum_prod_type,sum_comm]; let v:=unfoldX x
    let f(z:Cover)(p:J):=B i.2 p z * v (i.1+z,p); have h : Summable (uncurry f):=meets_current hp he i.1 i.2; have hu : (∑' j, uncurry f j)=∑ p:J,∑' j,f j p:=by rw [h.tsum_prod]; change (∑' (v:Cover) (j:J), f v j)=_; rw [← h.tsum_comm,tsum_fintype]
    change (∑' i,uncurry f i)=_; rw [hu]; apply Finset.sum_congr rfl; intro p _ -- just calc
    let y(j:Site L):=x (j,p); calc
      _ = ∑' j:Cover,B i.2 p j * y (wrap L i.1+wrap L j):= tsum_congr fun z=> by unfold f v y unfoldX; simp
      _ = _:= (sift_action (hp.safe i.2 p).of_norm ..).symm
lemma meetings {φ:Filter K}{V:K→Side}{U:∀ j:K,deck J (V j)}(h:Realized V φ v U m) (hb:Whole B): Realized V φ (meetsX B v) (fun i:K=> B.acts (V i) *ᵥ (U i)) m:=by
    obtain ⟨b,hb',g⟩:=h.Once; obtain ⟨s,A,hs,hA⟩:= hb; let z(i:K):=unfoldX (U i); have hh(i:K)(p:Cover × I) := stintCost hA hs _ p b _ hb' (g i)
    constructor
    · let Q:ℝ:= Fintype.card J* (widthCost s m*A*b); refine ⟨max Q 0,le_max_right ..,fun i x=>?_⟩; rw [← meets_finite (show Whole B from ⟨_,_,hs,hA⟩) (U i)]; unfold meetsX; have he:= hh i x; apply (norm_tsum_le_tsum_norm he.2.1).trans; apply he.2.2.trans; rw [show ((Fintype.card J):ℝ)*(widthCost s m*A*(b*poise m x.1))= Q*poise m x.1 from by unfold Q; ring]; exact mul_le_mul_of_nonneg_right (le_max_left ..) (zero_le_one.trans (poise_one ..))
    intro y; erw [show (fun i=> unfoldX (B.acts (V i) *ᵥ U i) y)=(fun i=>meetsX B (z i) y) from funext fun i=>congr_fun (meets_finite (B:=B) ⟨_,_,hs,hA⟩ (U i) |>.symm) y]; unfold meetsX
    let W(i:Cover×J):=b * poise m i.1; have hv := stintCost hA hs _ y b W hb' (fun i=>by unfold W;rw [Real.norm_of_nonneg]; have ht : 0 ≤ poise m i.1:=zero_le_one.trans (poise_one ..); positivity)
    refine tendsto_tsum_of_dominated_convergence hv.2.1 (fun i=> Tendsto.const_mul _ (h.Onset _)) (Eventually.of_forall fun i x=> ?_); rw [norm_mul,norm_mul,Real.norm_of_nonneg (r:=W _)]; exact mul_le_mul_of_nonneg_left (g ..) (norm_nonneg _); unfold W poise; positivity
lemma proper (h: Whole B)(hp:Quiet v m): Quiet (meetsX B v) m:=by
   have hT:= meetings (received (V:=epochX) (show Tendsto (fun j=>(epochX j).val) atTop atTop from tendsto_add_atTop_nat 1) hp) h; obtain ⟨b,hb,H⟩:= hT.Once; exact ⟨b,hb,fun i=> le_of_tendsto ((hT.Onset i).norm) (Eventually.of_forall fun j=> H j i)⟩
lemma jointX {H:Row J W} [Fintype W](h:Whole B)(ht:Whole H)(x: fieldX W)(hp: Quiet x m): meetsX B (meetsX H x)=meetsX (composeRows B H) x:=by
    ext1 i; let f(n:ℕ):= closeX x (epochX n); have he : Realized epochX atTop x f m:= received (tendsto_add_atTop_nat 1) hp
    refine tendsto_nhds_unique_of_eventuallyEq ((meetings (meetings he ht) h).Onset i) ((meetings he (h.prod ht)).Onset i) (Eventually.of_forall fun j:ℕ=>?_); dsimp only; erw [Matrix.mulVec_mulVec, h.acts ht]; -- arithmetic
end
end Script
end YM.OPE.Flume
