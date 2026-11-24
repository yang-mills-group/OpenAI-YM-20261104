import YM.OPE.Compatible.Atrium.Calf
/-!
# Joint tensors in tile grammar
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Stationary Woody Next.Foundations Planned.PrimaryIntegral295.Carrier
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c f:Side}{S:StepData c f}{P:Patch}{K:KernelChoices} {r:ℕ}
namespace Script
open Virgin Page
-- generic
lemma volume_bill {l:Side}{I J:Type*}[Fintype J](A:Cross l I J)(h:Whole A)(p:Script I r)(n:ℕ){u:ℝ} (hp:soot n p u):∃ c,soot n (payVolume A p) c:=by
   obtain ⟨s,D,h,hx⟩:= h; exact ⟨_,Sack.finGather (B:=fun i:Site l=> _) _ _ (fun i _=> silt_cost (counterflow hx h p (lift i) hp)) (fun i=> zero_le_one.trans (payer n _))⟩
variable {u v s:ℝ} {R:PathData G} {p: Clip}
abbrev podium (P:Patch)(R:PathData G)(p:Clip)(r:ℕ):= payVolume (drip G P.L) (polyV R p r)
def Penna (P:Patch)(K: KernelChoices)(R:PathData G)(p:Clip)(r:ℕ):= podium P R p r+ stationCall P K G r
variable (S) (h:Odd S.ratio.count.val)
local notation "F" => forest S.ratio h
-- physical vertex direction
abbrev ribz : vertP S.ratio h G→L[ℝ] Bid.Dir G f:= (arm G f 1).toContinuousLinearMap ∘L Stationary.pad F ∘L ContinuousLinearMap.snd ℝ (Bid.Dir G c) (AxisChart G F)
abbrev rankVol (R:PathData G) (p:Clip):=swornV p R∘ ribz S h
lemma podiumTal (p:Clip)(R:PathData G)(r:ℕ)(hp:R.Bounds p s u v): Talent (podium S.patch R p r) (paintV S.ratio h G).toContinuousLinearMap (rankVol S h R p):=by
    have hx:=inkX R p f r hp; let A:= (spool G f).toContinuousLinearMap; let T:= (paintV S.ratio h G).toContinuousLinearMap; let M : Cross S.ratio.count _ _:= drip G S.ratio.count; intro i
    have he: ∀ j,installed S.ratio M *ᵥ (T (i j))=A (ribz S h (i j)):= fun j=> paintDrip S h _
    erw [show library c (podium S.patch R p r) (T∘i)=_ from volume_torque (g:=S.ratio) (A:=M) (drip_cash G _) _ (sootS (hx.2.1 0).choose_spec) (T∘i)]; simp_rw [Function.comp_apply,he]; exact talentMove A _ hx.2.2 ((chartK R p f hp).1.of_le le_top) (ribz S h) i
lemma penne_unit (R:PathData G)(p:Clip)(P:Patch)(K:KernelChoices)(h:R.Bounds p s u v)(r m:ℕ): ∃ c,soot m (Penna P K R p r) c:=by
     obtain ⟨c,hx⟩:=(inkX R p 1 r h).2.1 m; have hh:= (volume_bill (drip G P.L) (drip_cash G P.L) _ _ hx).choose_spec; have ht:= (callCost P K G r m).choose_spec; exact ⟨_, hh.splits ht (fun i=> zero_le_one.trans (payer m _))⟩
set_option maxHeartbeats 200000 in
lemma penne_at (H:S.patch.Branches S.kernel G)(t:S.Choices)(p: Clip)(R:PathData G)(hp:R.Bounds p s u v)(n:ℕ): ContDiffAt ℝ ω (pane F t p R) 0 ∧ Talent (Penna S.patch S.kernel R p n) (paintV S.ratio h G).toContinuousLinearMap (pane F t p R):=by
     let T:= rankVol S h R p; have he: ContDiffAt ℝ ω T 0:= by
         refine ContDiffAt.comp _ ?_ (ribz S h).contDiff.contDiffAt; rw [map_zero]; exact (chartK R p f hp).1
     have hz : pane F t p R= T+ groundFee S h t:=by
         funext i; have hf:T i=mainTerm p R (fieldF F i.2):=by rw [spoolP F]; rfl
         exact congr_arg (fun x:ℝ=>x+groundFee S h t i) hf.symm
     have hm:= luff S h t H n; rw [hz]; exact ⟨he.add hm.1, issueTal _ (podiumTal S h p R n hp) (sootS (volume_bill _ (drip_cash G S.patch.L) _ 0 (((inkX R p f n hp).2.1 0).choose_spec)).choose_spec) hm.2 (sootS (callCost S.patch S.kernel G n 0).choose_spec) (he.of_le le_top) (hm.1.of_le le_top)⟩
end Script
end YM.OPE.Flume
