import YM.Contacts.Milling.Garf
import YM.Next.FLUCTUATIONS.Prediction
namespace YM.Contacts.Milling.Garf
noncomputable section
/- With locality proof core reused from Next/FLUCTUATIONS/Prediction.
   Want a single stencil (TEMPLATE address coords) lowering to every torus.
   Only on germ of conditional unmarked map. -/
open Next.Fluctuations
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f}

section locality

variable (P : Patch) (o : Axis)

-- No particular geometric efficiency needed for this fixed-patch receipt.
private def frameSites : Finset Cover := univ.biUnion fun x : P.Points => univ.biUnion
  fun y : P.Points => univ.biUnion fun l : Lattice.Order => (visits x.val (route x.val y.val l)).toFinset

private def alongBond := List.replicate P.L.val (posDir o)
private def bondShift : Cover := centerRoot P (step o)

private def predSites := (frameSites P ∪ (frameSites P).image (· + bondShift P o)) ∪
  univ.biUnion (fun x : P.Points => (visits x.val (alongBond P o)).toFinset)

private lemma frame_eq (K : KernelChoices) (hb : P.Branches K G)
    (U W : CoverConfig G) (h : ∀ i : Edge Cover, i.1 ∈ frameSites P → U i = W i)
    (t : P.FrameTag) : P.frame K U t = P.frame K W t := by
  have he (x y : P.Points) (l : Lattice.Order) : travel U x.val (route x.val y.val l) =
      travel W x.val (route x.val y.val l) := by
    apply travel_local _ _ U W
    exact fun i hi _ => h i (mem_biUnion.mpr ⟨x,mem_univ x, mem_biUnion.mpr ⟨y,mem_univ y,
      mem_biUnion.mpr ⟨l,mem_univ l,List.mem_toFinset.mpr hi⟩⟩⟩)
  have hax (x : P.FrameTag) : P.axial U x = P.axial W x := funext fun i => he x.1 i x.2
  have hv (f : P.Frame G) : P.via f U = P.via f W := by funext x y l; rw [via, via, he]
  have hs : P.score U = P.score W := by funext r; simp only [score,hv]
  have hm : P.usesMin K U ↔ P.usesMin K W := by simp only [usesMin,hax,hv]
  unfold Patch.frame
  by_cases hh : P.usesMin K W
  · rw [if_pos hh, if_pos (hm.mpr hh)]
    have h' : P.minimizing W (P.selected U) := by
      simp only [minimizing, ← hs]
      exact (P.min_exists U).choose_spec
    exact (hb.frame_unique W hh).unique h' (P.min_exists W).choose_spec
  · rw [if_neg hh, if_neg (fun h => hh (hm.mp h)), hax]

-- Make the different evaluation origins into explicit finite-cover reads.
private def predictionAt (K : KernelChoices) (U : CoverConfig G) (l r : P.FrameTag) (j : P.Points) :=
  P.predict K (fun x => P.frame K U l x * travel U x.val (alongBond P o) *
    (P.frame K (translate (bondShift P o) U) r x)⁻¹) j

private lemma predAt_eq (K : KernelChoices) (hb : P.Branches K G) (U W : CoverConfig G)
    (h : ∀ i : Edge Cover, i.1 ∈ predSites P o → U i = W i)
    (l r : P.FrameTag) (j : P.Points) : predictionAt P o K U l r j = predictionAt P o K W l r j := by
  have he : P.frame K U l = P.frame K W l := frame_eq P K hb U W
    (fun i hi => h i (mem_union_left _ (mem_union_left _ hi))) l
  let y := bondShift P o
  have hh : P.frame K (translate y U) r = P.frame K (translate y W) r := frame_eq P K hb _ _ (by
    intro i hi; unfold Lattice.translate; apply h
    exact mem_union_left _ (mem_union_right _ (mem_image_of_mem _ hi))) r
  have hu (x : P.Points) : travel U x.val (alongBond P o) = travel W x.val (alongBond P o) :=
    travel_local _ _ U W fun i hi _ => h i <| mem_union_right _ (mem_biUnion.mpr
      ⟨x,mem_univ x,List.mem_toFinset.mpr hi⟩)
  unfold y at hh
  simp only [predictionAt, he, hh, hu]

private lemma reads_at (U : Config G f) (k : S.Choices) (q : Site c) (i : Axis) :
    S.prediction U k (q,i) = predictionAt S.patch i S.kernel (expandAt (S.ratio.embed q) U)
      (k.1 q) (k.1 (q+step i)) (k.2 (q,i)) := by
  have he := levels S q U (step i)
  rw [plank, wrap_step, add_comm] at he
  unfold predictionAt StepData.prediction StepData.connector StepData.frames bondShift alongBond; rw [he]

private lemma reference_exists : ∃ c₀ : Side, 1 < c₀.val ∧
    ∀ i : Axis, ∀ x ∈ predSites P i, lift (wrap (c₀*P.L) x) = x := by
  let M := univ.sup (fun i : Axis => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs)))
  let c₀ : Side := ⟨2*M+2, by omega⟩
  refine ⟨c₀, by change 1 < 2*M+2; omega,fun i x hx => lift_eq_iff.mpr ⟨rfl,fun a => ?_⟩⟩
  have hv : (x a).natAbs ≤ M := le_trans (le_sup (s:=univ) (f:=fun a => (x a).natAbs) (mem_univ a))
    (le_trans (le_sup (s:=predSites P i) (f:=fun x => univ.sup (fun a : Axis => (x a).natAbs)) hx)
      (le_sup (s:=univ) (f:=fun i => (predSites P i).sup (fun x => univ.sup (fun a : Axis => (x a).natAbs))) (mem_univ i)))
  have ht : 2*M < (c₀*P.L).val := lt_of_lt_of_le (b:=c₀.val) (by change _ < 2*M+2; omega)
    (by exact le_mul_of_one_le_right (Nat.zero_le _) P.L.property)
  omega

end locality
open Stationary Pulse Spine Larch Origin House
open PertExtension.Series Ion
open scoped NNReal
abbrev Mixed (G:Gauge)(P:Patch) := Dye G ⊕ Cellar G P.L
abbrev Yard (G:Gauge)(S:StepData c f):= Co c (Mixed G S.patch)
def father (S:StepData c f)(i:Lines G c 1): Yard G S := (i.1,.inl i.2)
def offspring (S:StepData c f)(i: Lines G f 1): Yard G S := let p:= splitCo S.ratio (Dye G) i; (p.1,.inr p.2)
def mature (S:StepData c f): House.Dir (Yard G S) →L[ℝ] Link G c:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (father S i)
def teen (S:StepData c f): House.Dir (Yard G S) →L[ℝ] Link G f:= ContinuousLinearMap.pi fun i=> ContinuousLinearMap.proj (offspring S i)
def art (S:StepData c f):S.Choices := (fun _=>(S.patch.center,1),fun _=> S.patch.center)
def piloted (S:StepData c f)(i:Site c)(x:House.Dir (Yard G S)) : ℝ:= ∑ o:Axis,S.kernel.penalty * G.price (input G c (mature S x) (i,o) * (S.prediction (input G f (teen S x)) (art S) (i,o))⁻¹)
def hot (S:StepData c f)(x:House.Dir (Yard G S)):ℝ:=∑ i,piloted S i x
lemma hot_spec (x:House.Dir (Yard G S)): hot S x=noiseTaylor S (input G c (mature S x)) (input G f (teen S x)) (art S):= by simp only [hot,piloted,noiseTaylor,Fintype.sum_prod_type,mul_sum]
lemma pilot_ana (h:S.patch.Branches S.kernel G)(i:Site c): AnalyticAt ℝ (piloted (G:=G) S i) 0:= by
  let l:= (arm G c 1).toContinuousLinearMap.comp (mature S); let r:= (arm G f 1).toContinuousLinearMap.comp (teen S); apply ContDiffAt.analyticAt (ContDiffAt.sum (fun j _=> ContDiffAt.mul (contDiffAt_const (c:=S.kernel.penalty)) ?_)); apply Work.F03.price_smooth; simp only [G.mat_mul,G.mat_inv]; refine ((Work.F03.represent_smooth _).comp l.contDiff).contDiffAt.mul (ContDiffAt.comp (g:=(show G.Mat≃L[ℝ]G.Mat from starL ℝ)) _ ((starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff.contDiffAt) (ContDiffAt.comp (f:=r) (g:=fun u=> G.mat (S.prediction (represent u) (art S) (i,j))) _ ?_ r.contDiff.contDiffAt)); rw [map_zero]; exact Push.prediction_cont S h _ (art S)
lemma hot_ana (h:S.patch.Branches S.kernel G): AnalyticAt ℝ (hot (G:=G) S) 0:= ContDiffAt.analyticAt (ContDiffAt.sum (fun i _=> (pilot_ana h i).contDiffAt))

-- canonical template torus as address board
def reference (P:Patch):Side:= (reference_exists P).choose
def station (P:Patch)(K:KernelChoices): StepData (reference P) ((reference P)*P.L) := ⟨P,K,rfl⟩
private abbrev Split (G:Gauge)(S:StepData c f) : Co f (Dye G)≃ Co c (Cellar G S.patch.L):= splitCo S.ratio (Dye G)
def crafts (S:StepData c f)(i:Yard G S) : Node (Mixed G S.patch):= i.2.elim (fun a=>(lift i.1,.inl a)) (fun b=>
  let r:= lift (((Split G S).symm (i.1,b)).1-S.ratio.embed 0); (rent S.patch.L r, .inr (wrap S.patch.L r,b.2)))
private lemma apprentice (x:Site c)(u:House.Dir (Yard G S))(h:S.patch.Branches S.kernel G) : let K:=station S.patch S.kernel; piloted S x u=piloted K 0 (load (crafts K) x u) := by
  intro K; let m:= reference S.patch; let n:= m*S.patch.L; let s:= S.ratio.embed x; let s₀:= K.ratio.embed 0; let F:= input G f (teen S u); let v:= (load (crafts K) x u); let F₀:= input G n (teen K v)
  have he(q:Cover)(j)(o:Axis)(hu:q∈predSites S.patch o): expandAt s F (q,j)=expandAt s₀ F₀ (q,j) := by
    have ht:= (reference_exists S.patch).choose_spec.2 o q hu; let y := wrap f q+s; let y₀:= wrap n q+s₀; let z:=rent S.patch.L q
    have hl : S.ratio.parent y= wrap c z+x := by
      have hh : y= wrap f (lift (wrap S.patch.L q))+ S.ratio.embed (wrap c z+x):= by
        unfold y; conv_lhs => rhs; skip
        conv_lhs=> lhs; rw [rent_balance S.patch.L q, map_add]
        rw [show S.ratio.embed (wrap c z+x)=_ from S.ratio.root.map_add (wrap c z) x]; change _=_+(S.ratio.embed _ +_); rw [S.ratio.embed_wrap]; exact add_assoc ..
      rw [hh,add_comm]; exact S.ratio.assemble_parent (wrap c z+x,wrap S.patch.L q)
    have ha:S.ratio.residue y=wrap S.patch.L q:= by
       unfold y; rw [map_add, Ratio.residue_wrap, show S.ratio.residue s=0 from S.ratio.residue_embed _,add_zero]; rfl
    change (input G f _ _)=(input G n _ _); simp only [encode_link]; refine congr_arg G.lieExp ?_; ext1 l; let b: Dye G:= (coord j,l); change u (offspring S (y,b))=u (road (crafts K (offspring K (y₀,b))) x); congr 1
    change offspring S _ = road (Prod.mk (rent _ _) _) x
    have hh : (splitCo K.ratio (Dye G)).symm (K.ratio.parent y₀,K.ratio.residue y₀,b)=(y₀,b) := by rw [show (K.ratio.parent y₀,K.ratio.residue y₀,b)=_ from (show (splitCo K.ratio (Dye G)) (y₀,b)=_ from split_co ..).symm, Equiv.symm_apply_apply] 
    simp only [offspring,Split,split_co]; erw [hh,show lift _ = q from Eq.trans (congr_arg lift (show y₀-K.ratio.embed 0=(wrap n) q from add_sub_cancel_right ..)) ht, ha, hl]; rfl
  have ha (j:Axis): S.prediction F (art S) (x,j)= K.prediction F₀ (art K) (0,j):= by
     rw [reads_at,reads_at]; exact predAt_eq S.patch j S.kernel h _ _ (fun ⟨b,i⟩ hp=> he _ _ j hp) _ _ _
  apply sum_congr rfl; intro j hj; congr! 2
  refine congr_arg₂ (·*·) ?_ (congr_arg Inv.inv (ha j)); rw [encode_link,encode_link]; refine congr_arg G.lieExp ?_; ext1 p; let a : Dye G:= (coord j,p); change u (x,.inl a) = u (wrap c (lift (0:Site m))+x,.inl a); rw [show lift (0:Site m)=0 from funext (fun a=> ZMod.valMinAbs_zero m.val),map_zero,zero_add]
abbrev fireworks (P:Patch)(K:KernelChoices)(G:Gauge)(r:ℕ) := aboard (crafts (station P K)) (words (piloted (G:=G) (station P K) 0) r)
def pilotWord (S:StepData c f)(G:Gauge)(r:ℕ) := ashore (crafts (station S.patch S.kernel)) (words (piloted (G:=G) (station S.patch S.kernel) 0) r) c
lemma woven {E V:Type}[NormedAddCommGroup V][NormedSpace ℝ V][NormedAddCommGroup E][NormedSpace ℝ E]{F:E→ℝ} (h:AnalyticAt ℝ F 0)(L:V →L[ℝ] E)(x:V)(k:ℕ): Radial.jet (F ∘ L) k x=Radial.jet F k (L x):= by unfold Radial.jet; rw [wired L ?_,map_zero]; rfl; rwa [map_zero]
lemma hot_craft (h:S.patch.Branches S.kernel G) (x : House.Dir (Yard G S))(k:ℕ): design (pilotWord S G k) x= Radial.jet (hot S) k x := by
  let K := station S.patch S.kernel; have he i:= (pilot_ana (S:=K) h i); let p:House.Dir (Yard G K)→ℝ:= piloted K 0; unfold pilotWord; rw [words_read]; change (∑ i, design (words p k) _) = _; unfold hot; rw [loan_sum _ (fun i _=> pilot_ana h i)]; apply sum_congr rfl; intro i hi; rw [hash, show piloted (G:=G) S i=p∘load (crafts K) i from funext fun x=> apprentice i x h]; exact (woven (he 0) (load (crafts K) i) x k).symm
open Radial Tested
lemma torch (h:S.patch.Branches S.kernel G)(x:House.Dir (Yard G S)): Tendsto (fun t:ℝ=> sample (hot S) x t) (𝓝[≠]0) (𝓝 (S.kernel.penalty * (∑ i : Body 1 c, ‖Work.F03.residual S (arm G c 1 ((mature S) x),arm G f 1 (teen S x)) i‖^2)/2)) := by
  let he:= Work.F03.noise_limit h (art S) (arm G c 1 (mature S x),arm G f 1 (teen S x)); simp_rw [real_inner_self_eq_norm_sq] at he; simp only [sample,hot_spec,map_smul,input]; exact he
-- extract from scaling T and constant flux
lemma torch_c {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X]{F:X→ℝ}(h:AnalyticAt ℝ F 0){C:X→ℝ}(H:∀ x,Tendsto (sample F x) (𝓝[≠]0) (𝓝 (C x))): Radial.Stationary F ∧ (∀ x,jet F 2 x=C x):= by
  have ha:∀ x:X, ContDiffAt ℝ ω (fun t:ℝ=> F (t• x)) 0 := fun x => ContDiffAt.comp (g:=F) (f:=fun t:ℝ=>t • x) _ (by rw [zero_smul]; exact h.contDiffAt) (by fun_prop) -- test
  have ht (x:X):= Work.F03.value_slope_of_sq_limit (ha x).continuousAt (H x)
  refine ⟨⟨h.contDiffAt,by simpa using (ht 0).1,fun i=>by rw [homogeneous_derivative F i 1 h.contDiffAt]; simp [(ht i).2.deriv]⟩,fun x=> ?_⟩
  have he:= tendsto_nhds_unique (H x) (Work.F03.taylor_limit_two (ha x|>.of_le le_top) (ht x).1 (ht x).2.deriv); rw [homogeneous_derivative F x 2 h.contDiffAt]; convert he.symm using 1; norm_num [div_eq_mul_inv,mul_comm]

end
end YM.Contacts.Milling.Garf
