import YM.WilsonCoeffUV.Thermo.WilsonStep
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Theme
/-!
# Root-frame penalty template. Pick takes ALL weighted rolls (no change on
wrap); even ViewCost not needed prior block. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Progress.StationaryScenes AnalyticNext.QuarticMatch.Sheets AnalyticNext.QuarticMatch.Radius.Model
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{c f L: Side}
abbrev Larvae (G:Gauge)(L:Side) := Co L (Hooks G)
abbrev Hinge (G:Gauge)(L:Side) := Larvae G L ⊕ Hooks G
abbrev weaveFine (g:Ratio c f) (G:Gauge) := splitCo g (Hooks G)
def weaveH (g:Ratio c f) (G:Gauge): Joint G f c≃ Co c (Hinge G g.count):= ((Equiv.sumCongr (weaveFine g G) (Equiv.refl _)).trans (Stationary.drawerC _ _ _))
lemma vaneL (g:Ratio c f) (x:Woods G f): weaveH g G (.inl x)= let i:=splitCo g (Hooks G) x; (i.1,.inl i.2):=rfl
lemma vaneR (g:Ratio c f) (x:Woods G c): weaveH g G (.inr x)= (x.1,.inr x.2):=rfl
-- natural patch core: finite ALL bonds at one centered template. score for edge stamp at zero.
abbrev AudienceK (P:Patch)(G:Gauge):= Joint G (native P) (marker P)

def debit (P:Patch)(K:KernelChoices)(v:Axis)(x:Lawn (AudienceK P G)):=
  let S:= stepAt P K (marker P); K.penalty* G.price (mantle (rightArm x) (0,v) * (S.prediction (mantle (leftArm x)) (tac S) (0,v))⁻¹)

-- pull as Theme.pick. no duplicate merge. Use all rightArm axes at exactly x, others blank.
def seat (P:Patch)(G:Gauge): Leads Cover (Hinge G P.L) (AudienceK P G) := Sum.elim
  (fun i=> if lift i.1 ∈ atEase P then
    let b:= (panel (P).L (Hooks G)).symm (lift i.1,i.2); some (b.1, Sum.inl b.2) else none)
  (fun i=> if i.1=0 then some (0, Sum.inr i.2) else none)

lemma panel_clock (g:Ratio c f){α:Type*}(z : Cloth α) (b:Site c):
    jog b (foldUnder c ((panel g.count α).symm z))=splitCo g α (wrap f z.1+g.embed b,z.2):=by
  apply (splitCo g α).symm.injective
  rw [Equiv.symm_apply_apply, split_move, ← panel_wrap,Equiv.apply_symm_apply]; exact Prod.ext (add_comm ..) rfl

section observation
variable (S:StepData c f)
local notation "P"=> S.patch
local notation "U'"=> (weaveH S.ratio G)
variable (v: Lawn (Co c (Hinge G S.patch.L)))
lemma atlas_seen (b:Site c) :
    (cloth G (native S.patch)).symm (leftArm (casement (seat S.patch G) b *ᵥ v))=pick S b ((cloth G f).symm (leftArm (v ∘ U'))):=by
  ext1 j; obtain ⟨p,j⟩:= j
  ext i
  unfold pick; rw [ContinuousLinearMap.pi_apply]; split
  · rename_i hx
    set a:=(panel (P).L (Hooks G)).symm (lift p,j,i)
    let w : Cloth (Hinge G (P).L):= (a.1, Sum.inl a.2)
    have hp: seat (P) G (.inl (p,j,i))=some w:=by unfold seat; rw [Sum.elim_inl,if_pos hx]
    change (casement (seat (P) G) b *ᵥ v) (.inl (p,j,i))= v (U' (.inl (wrap f (lift p)+ S.ratio.embed b,j,i)))
    rw [sight_step (seat (P) G) b (.inl (p,j,i)) w hp]
    have he : jog b (foldUnder c a)= splitCo S.ratio (Hooks G) (wrap f (lift p)+S.ratio.embed b,j,i):= panel_clock S.ratio (lift p,j,i) b
    exact congr_arg v (Prod.ext (congr_arg (fun t : Co c (Co (P).L (Hooks G))=> Prod.fst t) he) (congr_arg (fun t : Co c (Co (P).L (Hooks G))=> Sum.inl (β:=Hooks G) t.2) he))
  rename_i hx
  exact sight_none (seat (P) G) b (.inl (p,j,i)) (by simp [seat,hx]) v
lemma spiral_look (b:Site c)(w:Axis) :
    mantle (rightArm (casement (seat S.patch G) b*ᵥ v)) (0,w)=mantle (rightArm (v ∘ U')) (b,w):=by
  unfold mantle; rw [Work.F03.represent_link,Work.F03.represent_link]; apply congr_arg G.lieExp; ext i
  change (casement (seat (P) G) b*ᵥ v) (.inr (0,coord w,i))= v (U' (.inr (b,coord w,i)))
  rw [sight_step (seat (P) G) b (.inr (0,coord w,i)) (0,.inr (coord w,i)) (by simp [seat])]; congr 1; change (b+wrap c 0,_)=_; rw [map_zero,add_zero]; rfl

lemma debut_green (w:Axis)(e:S.patch.Branches S.kernel G) : Green (debit (G:=G) S.patch S.kernel w):=by
  let J:= stepAt S.patch S.kernel (marker S.patch); refine ContDiffAt.mul contDiffAt_const ?_
  apply Work.F03.price_smooth (A:=fun z:Lawn (AudienceK S.patch G)=> mantle (rightArm z) (0,w)*(J.prediction (mantle (leftArm z)) (tac J) (0,w))⁻¹);
  simp_rw [G.mat_mul,G.mat_inv]; apply ContDiffAt.mul
  · exact (mantle_green _).contDiffAt.comp _ (contDiffAt_pi.mpr fun _=>contDiffAt_apply ℝ ℝ _ _)
  have hv : Green (fun i:Lawn (AudienceK S.patch G)=>G.mat (J.prediction (mantle (leftArm i)) (tac J) (0,w))):= by
    unfold Green mantle; let t:=cloth G (native S.patch)
    have he : Green (fun i:Lawn (AudienceK S.patch G)=> t.symm (leftArm i)):=t.symm.contDiff.contDiffAt.comp _ (contDiffAt_pi.mpr fun _=>contDiffAt_apply ℝ ℝ _ _)
    have h : t.symm (leftArm (0:Lawn (AudienceK S.patch G)))=0:= by rw [show leftArm (0:Lawn (AudienceK S.patch G))=0 from rfl,map_zero]
    exact ContDiffAt.comp (g:=fun x=> G.mat (J.prediction (represent x) (tac J) (0,w))) (f:=fun i:Lawn (AudienceK S.patch G)=>t.symm (leftArm i)) 0 (by rw [h]; exact Push.prediction_cont J e (0,w) (tac J)) he
  exact (starL ℝ).contDiff.contDiffAt.comp _ hv

set_option maxHeartbeats 800000 in
lemma meter_clock (b:Site c)(w:Axis)(e:S.patch.Branches S.kernel G): ∀ᶠ v: Lawn (Co c (Hinge G S.patch.L)) in 𝓝 0,
    S.kernel.penalty * G.price (mantle (rightArm (v ∘ U')) (b,w)*(S.prediction (mantle (leftArm (v ∘ U'))) (tac S) (b,w))⁻¹)= debit (P) S.kernel w (casement (seat (P) G) b *ᵥ v):= by
  let t := stepAt S.patch S.kernel (marker S.patch)
  let h:= tac t
  let H (v : Lawn (Co c (Hinge G S.patch.L))) := (cloth G f).symm (leftArm (v ∘ U'))
  let X (v : Lawn (Co c (Hinge G S.patch.L))) := pick S b (H v)
  have hv : ContinuousAt X 0:= (pick S b).continuous.continuousAt.comp ((cloth G f).symm.continuous.continuousAt.comp (continuousAt_pi.mpr fun _=> (continuous_apply _).continuousAt))
  have hz:X 0=0:=by unfold X H; rw [show leftArm ((0:Lawn (Co c (Hinge G S.patch.L))) ∘ U')=0 from rfl,map_zero,map_zero]
  have hp : Tendsto X (𝓝 0) (𝓝 0):= hz ▸ hv
  filter_upwards [hp.eventually (eventually_all.mpr fun p : Site (marker P)=> Push.threshold t p),hp.eventually (eventually_best (S:=t) e h.1 (0,w))] with v hv he
  obtain ⟨_,hh⟩ := compiles S (tac S) e (b,w) (H v) h hv
  have hh : S.connector (represent (H v)) (tac S).1 (b,w)= t.connector (represent (X v)) h.1 (0,w):= hh
  have ha : S.prediction (mantle (leftArm (v ∘ U'))) (tac S) (b,w)= t.prediction (mantle (leftArm (casement (seat (P) G) b *ᵥ v))) h (0,w):=by
    rw [show mantle (leftArm (casement (seat (P) G) b *ᵥ v))=represent (X v) from congr_arg represent (atlas_seen S v b), show mantle (leftArm (v ∘ U'))=represent (H v) from rfl]; unfold StepData.prediction; rw [hh]; unfold Patch.predict; rw [if_pos he, if_pos he];
  rw [ha, ← spiral_look S v b w]; rfl
lemma pen_whistle (e:S.patch.Branches S.kernel G): ∀ᶠ v : Lawn (Co c (Hinge G S.patch.L)) in 𝓝 0,
    jointPen G S (v ∘ U')= ∑ j:Axis,∑ x:Site c,debit S.patch S.kernel j (casement (seat (P) G) x*ᵥ v):=by
  filter_upwards [eventually_all.mpr fun x=>eventually_all.mpr fun j=>meter_clock S x j e] with v hv
  unfold jointPen noiseTaylor; rw [Fintype.sum_prod_type,Finset.sum_comm]; simp_rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> hv ..
lemma pen_wear (e:S.patch.Branches S.kernel G): Green (fun v:Lawn (Co c (Hinge G S.patch.L))=> jointPen G S (v ∘ U')):= (penSmooth G S e).comp (f:=fun v:Lawn (Co c (Hinge G S.patch.L))=> v ∘ U') 0 (contDiffAt_pi.mpr fun _=>contDiffAt_apply ℝ ℝ _ _)
end observation
variable (P:Patch) (K:KernelChoices)
def warren (G:Gauge)(i:ℕ): Gen ℝ (Cloth (Hinge G P.L)):= ∑ j:Axis, sunflower (seat P G) (sprig (debit P K j) 2 i)
lemma tide_pay (G:Gauge)(t i:ℕ)(s:ℝ)(h:0≤s): ∃ A:ℝ, Amber terrain s A (warren P K G t i):=by
  choose A he using fun v: Axis=> it_cost (seat P G) (sprig (debit P K v) 2 t) i s h
  rw [warren,Finset.sum_apply]; exact ⟨_, Amber.sum _ (fun i _=>he i)⟩
set_option maxHeartbeats 400000 in
lemma pick_page (n:Side)(h:P.Branches K G)(i r:ℕ): bend (weaveH (ratioN P.L n) G) (sprig (jointPen G (stepAt P K n)) 2 i) r = sprig (fun u:Lawn (Co n (Hinge G P.L))=> jointPen G (stepAt P K n) (u ∘ weaveH (ratioN P.L n) G)) 2 i r:=
  congr_fun (bend_sprig (weaveH (ratioN P.L n) G) _ 2 i (penSmooth G (stepAt P K n) h)) _
lemma P_perch (h:P.Branches K G) (n:Side): let F := fun u:Lawn (Co n (Hinge G P.L))=> jointPen G (stepAt P K n) (u ∘ weaveH (ratioN P.L n) G); Green F ∧ ∀ᶠ u in 𝓝 0, F u=∑ j:Axis,∑ x:Site n,debit P K j (casement (seat P G) x*ᵥ u) := ⟨pen_wear (stepAt P K n) h,pen_whistle (stepAt P K n) h⟩
lemma shrubJ (h:P.Branches K G)(i r:ℕ): Yields (fun n=> sprig (fun u:Lawn (Co n (Hinge G P.L))=> jointPen G (stepAt P K n) (u ∘ weaveH (ratioN P.L n) G)) 2 i r) (warren P K G i r):= by
  unfold warren
  exact daisies (α:=Hinge G P.L) (I:=AudienceK P G) (J:=Axis) (b:=fun v=> debit (G:=G) P K v) (P:=fun n u => jointPen G (stepAt P K n) (u ∘ weaveH (ratioN P.L n) G)) (fun j=>debut_green (stepAt P K 1) j h) (fun _=> seat P G) (fun n=>(P_perch P K h n).2) (fun n=>(P_perch P K h n).1) 2 i r
lemma spew (h:P.Branches K G)(i r:ℕ): Yields (fun n=> bend (weaveH (ratioN P.L n) G) (sprig (jointPen G (stepAt P K n)) 2 i) r) (warren P K G i r) :=
  (shrubJ P K h i r).congr (Eventually.of_forall fun n=> (pick_page _ _ n h i r).symm)
end YM.WilsonCoeffUV.Bank
