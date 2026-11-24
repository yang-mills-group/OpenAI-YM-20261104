import YM.AveragedStep.Parcel.Layouts
import YM.Push.STATIONARY_UNIFORM.Wilson
/-! Port the cover stencil to a genuine period so local analytic facts can
consume the stationary supplies. Switch and tag readout remains literal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Function Filter Lattice Wilson RG Patch Pressure Precision Push Exterior
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{c f:Side}(S:StepData c f)

def native (i:S.Choices)(Y:Config G f): Prop:=
     (∀ x,S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) Y))∧
     ∀ e,S.patch.usesBest S.kernel (S.connector Y i.1 e)
lemma native_reports (h:S.patch.Branches S.kernel G):
    ∀ᶠ v:Push.In G f in 𝓝 0,∀ i:S.Choices,native S i (represent v):=by
  have hw : ∀ᶠ v:In G f in 𝓝 0,∀ x,S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) (represent v:Config G f)):= eventually_all.mpr
      fun x=>Push.threshold S x
  refine hw.mp ?_
  suffices ht: ∀ᶠ v:In G f in 𝓝 0,∀ (i:S.Choices) e,S.patch.usesBest S.kernel (S.connector (represent v) i.1 e) by
    exact ht.mono fun v ht hs i=> ⟨hs,ht i⟩
  refine eventually_all.mpr fun i=>eventually_all.mpr fun e=>?_
  have he : ContinuousAt (deck (G:=G) S e i.1) 0:= continuousAt_pi.mpr fun t=>
    (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
      (builds S h e i.1 t).continuousAt.tendsto
  apply (he.tendsto.eventually (S.patch.best_open.mem_nhds ?_))
  apply lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1)
  simpa [Patch.bondCost,Push.deck_zero S h e i.1] using S.kernel.predictor_cut_pos

variable (P:Patch)
def span (x:Cover):=Finset.univ.sup (fun i=> (x i).natAbs)
def ceiling := (domain P).sup span
def width : Side := ⟨4*(ceiling P+2),by omega⟩
def wideFine:= width P * P.L
def widest (K:KernelChoices):StepData (width P) (wideFine P):=⟨P,K,rfl⟩
@[simp] lemma wideL(K:KernelChoices): (widest P K).patch=P:=rfl
@[simp] lemma wideK(K:KernelChoices): (widest P K).kernel=K:=rfl
private lemma centre {x:Cover}(h:x∈domain P){i: Axis}:
    -(↑(wideFine P).val:ℤ)<2*x i ∧ 2*x i≤ (wideFine P).val:=by
  have ht: ceiling P≤((wideFine P).val)/4 - 1:=by
    have hh :4*(ceiling P+2)≤(wideFine P).val:=Nat.le_mul_of_pos_right (width P).val P.L.prop
    omega
  have he:(x i).natAbs≤ceiling P := (Finset.le_sup (s:=Finset.univ) (f:=fun i=>(x i).natAbs) (Finset.mem_univ i)).trans (Finset.le_sup (f:=span) h)
  have hh :4*(ceiling P+2)≤(wideFine P).val:=Nat.le_mul_of_pos_right (width P).val P.L.prop
  omega

private def finePort : Grounding P→ ↥(domain P) × Axis :=fun i=> (⟨i.val.1,i.prop⟩,i.val.2)
instance: Finite (Grounding P):=Finite.of_injective (finePort P) (fun ⟨⟨_,_⟩,_⟩ ⟨⟨_,_⟩,_⟩ he=>by simpa only [finePort,Prod.mk.injEq, Subtype.mk.injEq] using he)
instance: Fintype (Grounding P):=Fintype.ofFinite _
abbrev Vectors (G:Gauge):= Interior P → G.Color
open Laurent -- coord
private def dispatch (a:Axis)(v:Vectors P G)(o:Site (wideFine P)) :=
    if h:lift o∈domain P then v (some ⟨(lift o,a),h⟩) else 0
private def port (v:Vectors P G): In G (wideFine P):= fun i=> dispatch P (axisEquiv.symm i.2) v i.1
private lemma ports_smooth: ContDiff ℝ ω (port P (G:=G)):=by
  apply contDiff_pi.mpr
  intro i; change ContDiff _ _ (fun v=>dispatch P _ v _); unfold dispatch; split
  · exact contDiff_apply ..
  exact contDiff_const
private lemma empty : port P (0:Vectors P G)=0:=by funext i; unfold port dispatch; split <;> rfl
private def sail (v:Vectors P G): Values P G:= fun i=>G.lieExp (v i)
-- now exactly pretend ; if expanding outside domain, restrict ALL used forms to domain
private lemma shores (v:Vectors P G):
    let f:=wideFine P
    let U:=represent (port P v)
    let Z:Board G (width P) f:=(U,1)
    ∀ i: Grounding P, expandAt (0:Site f) Z.1 i.val = pretend P (sail P v) i.val := by
  intro f U Z i
  unfold expandAt pretend
  rw [add_zero]; unfold Z U; dsimp only; rw [Work.F03.represent_link]
  change G.lieExp (dispatch P (axisEquiv.symm (Exterior.coord i.val.2)) v _) = _
  have he:axisEquiv.symm (Exterior.coord i.val.2)= i.val.2:=axisEquiv.symm_apply_apply _
  have hf:lift (wrap f i.val.1)=i.val.1:=lift_eq_iff.mpr ⟨rfl,fun _=> centre P i.prop⟩
  rw [he,dispatch]; simp [hf,i.prop,sail]


def chip (K:KernelChoices)(a:Mold)(l:Leash P)(v:Vectors P G):= costume P K a l (sail P v)
def numberChip (K:KernelChoices)(a:Mold)(l:Leash P)(v:Vectors P G):= mark P K a l (sail P v)

variable (K:KernelChoices)
-- identities when fine addresses have been ported for the patch at site 0.
def anchor (a:Mold):Parcel (width P) (wideFine P):=a.elim (fun i=> Sum.inl (0,i)) (fun i=> Sum.inr (0,i))
lemma anchor_point (a:Mold):point (widest P K) (anchor P a)=0:=by
  rcases a with p|a; rfl; exact (widest P K).ratio.root.map_zero
@[simp] lemma anchor_sort(a:Mold): sort (anchor P a)=a:=by cases a <;> rfl
private def mount (v:Vectors P G):Board G (width P) (wideFine P):=(represent (port P v),fun _=>G.lieExp (v none))
private lemma gathers_fine (v:Vectors P G)(a:Mold)(i:Grounding P):
    gathers (widest P K) (anchor P a) (Sum.elim (mount P v).1 (mount P v).2) (some i) = sail P v (some i):=by
  rw [cursor,anchor_point]
  have he:=shores P v i
  unfold pretend at he; rw [dif_pos i.prop] at he; exact he
private lemma equal_chip (v:Vectors P G)(a:Mold)(l:Leash P):
    let Y:=gathers (widest P K) (anchor P a) (Sum.elim (mount P v).1 (mount P v).2)
    costume P K a l Y = chip P K a l v ∧ mark P K a l Y=numberChip P K a l v:=by
 intro Y; unfold chip costume mark numberChip
 have he:pretend P Y=pretend P (sail P v):= by
   funext e; unfold pretend; split; apply gathers_fine; rfl
 rw [he]
 rcases a with a|(_|a) -- unused cover none for station/cell
 · exact ⟨rfl,rfl⟩
 · exact ⟨rfl,rfl⟩
 exact ⟨rfl,rfl⟩ -- near none defeq

private lemma anchor_moves (a:Mold)(l:Leash P)(t:(widest P K).Choices)
    (hQ:∀ X:Values P G,costume P K a (leads (widest P K) t (anchor P a)) X = costume P K a l X ∧
      mark P K a (leads (widest P K) t (anchor P a)) X = mark P K a l X):∃ t:(widest P K).Choices,∀ v:Vectors P G,
    temperature (widest P K) t (anchor P a) (mount P v)=chip P K a l v ∧
    marked (widest P K) t (anchor P a) (mount P v)=numberChip P K a l v := by
  refine ⟨t,fun v=>?_⟩
  unfold temperature marked; rw [anchor_sort]; change costume P K _ _ _ = _ ∧ mark P K _ _ _ = _
  rw [(hQ _).1,(hQ _).2]; exact equal_chip P K v _ l
private lemma leases (a:Mold)(l:Leash P):
    ∃ t:(widest P K).Choices,∀ v:Vectors P G,
    temperature (widest P K) t (anchor P a) (mount P v)=chip P K a l v ∧
    marked (widest P K) t (anchor P a) (mount P v)=numberChip P K a l v:=by
 rcases a with a|(_|a)
 · refine anchor_moves _ _ _ l ((fun _=>l.1),fun _=>l.2.2) ?_; intro X
   dsimp only [costume,mark,temperatures,bands,Mold,Sum.elim_inl]; exact ⟨rfl,rfl⟩
 · refine anchor_moves _ _ _ l ((fun _=>l.1),fun _=>l.2.2) ?_; intro X
   dsimp only [costume,mark,temperatures,bands,Mold,Sum.elim_inr,Option.casesOn]; exact ⟨rfl,rfl⟩
 let t:(widest P K).Choices:=(fun i=>if i=0 then l.1 else l.2.1,fun _=>l.2.2)
 have hl:(step a:Site (width P)) ≠ 0 := by
   intro h; have hv:=congrFun h a; simp at hv
   haveI : Fact (1<(width P).val):= ⟨show 1<4*(ceiling P+2) by omega⟩
   change (1 : ZMod (width P).val)=0 at hv
   exact one_ne_zero hv
 refine anchor_moves _ _ _ l t ?_
 intro X; have he: leads (widest P K) t (anchor P (Sum.inr (some a)))=l:=by simp [anchor,leads,t,hl,Option.elim]
 rw [he]; exact ⟨rfl,rfl⟩

private lemma neat (l:S.Choices)(v:In G f)(H:native S l (represent v))(w:Axis)(o:Site c):
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed o) (represent v)) (l.1 o)=(Fintype.card S.patch.FrameTag:ℝ)⁻¹ ∧
    S.patch.predictorMass S.kernel (S.connector (represent v) l.1 (o,w)) (l.2 (o,w))=(Fintype.card S.patch.Points:ℝ)⁻¹ := by
  constructor; exact if_pos (H.1 o); exact if_pos (H.2 _)
private lemma neatly_same(l r:S.Choices)(v:In G f)(hl:native S l (represent v))(hr:native S r (represent v))(e:Edge (Site c)) :
    S.prediction (represent v) l e=S.prediction (represent v) r e:= by
  have he (t:S.Choices) (ht:native S t (represent v)): S.prediction (represent v) t e=S.patch.best (S.connector (represent v) t.1 e):= if_pos (ht.2 e)
  rw [he l hl,he r hr]; apply congr_arg; unfold StepData.connector StepData.frames; have hf(x:Site c)(i:S.SitesChoice): S.patch.frame S.kernel (expandAt (S.ratio.embed x) (represent v)) (i x)=S.patch.selected (expandAt (S.ratio.embed x) (represent v)):= if_pos (hl.1 x) -- placeholder
  simp_rw [hf]

private lemma tag_lemma (h:P.Branches K G)(l r:(widest P K).Choices)(a:Mold)(v:Vectors P G)(hl:native (widest P K) l (mount P v).1)(hr:native (widest P K) r (mount P v).1):
    temperature (widest P K) l (anchor P a) (mount P v)=temperature (widest P K) r (anchor P a) (mount P v) ∧
    marked (widest P K) l (anchor P a) (mount P v)= marked (widest P K) r (anchor P a) ((mount P v).1,1):=by
  let S:=widest P K
  have hh:S.patch.Branches S.kernel G:=h
  rcases a with i|(_|i)
  · exact ⟨(terrace_face S hh ..).1.trans (terrace_face S hh ..).1.symm,(terrace_face S hh ..).2.trans (terrace_face S hh ..).2.symm⟩ -- .. underconstrained
  · change temperature S l (.inr (0,none)) _=temperature S r (.inr (0,none)) _ ∧ marked S l (.inr (0,none)) _=marked S r (.inr (0,none)) _
    rw [(terrace_station S hh ..).1,(terrace_station S hh ..).1,(terrace_station S hh ..).2,(terrace_station S hh ..).2]
    exact ⟨rfl, (neat S l (port P v) hl 0 0).1.trans (neat S r (port P v) hr 0 0).1.symm⟩
  let q:Edge (Site (width P)) :=(0,i)
  obtain ⟨ht,hm⟩:= terrace_bond S hh l q (mount P v)
  have hv:= terrace_bond S hh r q (mount P v); have he:= (terrace_bond S hh r q ((mount P v).1,1)).2
  change temperature S l (.inr (0,some i)) _=temperature S r (.inr (0,some i)) _ ∧ marked S l (.inr (0,some i)) _=marked S r (.inr (0,some i)) _
  constructor
  · change temperature S l (.inr (q.1,some q.2)) _=temperature S r (.inr (q.1,some q.2)) _; rw [ht,hv.1]; unfold mount; rw [neatly_same S _ r _ hl hr]
  exact hm.trans <| ((neat S l _ hl i 0).2.trans (neat S r (port P v) hr i 0).2.symm).trans he.symm
attribute [local instance] Gauge.frobInner
private lemma price_smooth {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X]{x:X}{F:X→G.El}
    (h:ContDiffAt ℝ ω (fun x=>G.mat (F x)) x):ContDiffAt ℝ ω (fun x=>G.price (F x)) x:=by
 unfold Gauge.price Matrix.trace; simp_rw [Complex.re_sum]
 -- Frobenius norm matrix pi vs product topology: contDiff parts via CLM proj
 let Y (i:Fin G.repDim)(A:G.Mat):ℝ:=(A i i).re
 have he(i:Fin G.repDim): ContDiff ℝ ω (Y i):=by
   let f:G.Mat →ₗ[ℝ] ℝ:= {
     toFun:=Y i
     map_add':=by intro a b; unfold Y; rfl
     map_smul':=by intro c a; unfold Y; simp
   }
   exact f.toContinuousLinearMap.contDiff
 exact contDiffAt_const.sub ((ContDiffAt.sum (fun i _=> (he i).contDiffAt.comp x h)).div_const _)
private lemma smooth_launch (h:S.patch.Branches S.kernel G)(t:S.Choices)(a:Parcel c f):
    let Z (x:In G f× G.Color):Board G c f:=(represent x.1,fun _=>G.lieExp x.2)
    ContDiffAt ℝ ω (fun x=> temperature S t a (Z x)) 0 ∧ temperature S t a (Z 0)=0 :=by
  intro X; rcases a with p|⟨z,_|a⟩
  · simp_rw [(terrace_face S h ..).1,faceValue]
    constructor
    · exact price_smooth (Push.writes .. |>.comp (f:=Prod.fst) (0:In G f × G.Color) contDiffAt_fst)
    change G.price (travel (represent 0) _ _)=0; rw [Push.stroll_zero]; simp
  · simp_rw [(terrace_station S h ..).1]; exact ⟨contDiffAt_const,True.intro⟩
  simp_rw [(fun (x:In G f × G.Color)=> (terrace_bond S h t (z,a) (X x)).1)] -- z not clear?
  dsimp only [X,Prod.mk.eta]; let Y (x:In G f × G.Color):=S.prediction (represent x.1) t (z,a)
  change ContDiffAt ℝ ω (fun x=> _*G.price (G.lieExp x.2*(Y x)⁻¹)) 0 ∧ _
  constructor
  · refine contDiffAt_const.mul (price_smooth ?_)
    simp_rw [Gauge.mat_mul,Gauge.mat_inv]
    apply ContDiffAt.mul ((G.exp_jet.comp (contDiff_snd)).contDiffAt)
    exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _
       ((Push.prediction_cont S h (z,a) t).comp (f:=Prod.fst) (0:In G f × G.Color) contDiffAt_fst)
  change S.kernel.penalty * G.price (G.lieExp 0 * (S.prediction (represent 0) t (z,a))⁻¹)=0
  rw [Precision.link_one,G.mat_lieExp_zero,settled S h]; simp

lemma smooth_chip (h:P.Branches K G)(a:Mold)(l:Leash P):
    ContDiffAt ℝ ω (chip P K a l (G:=G)) 0 ∧ chip P K a l (0:Vectors P G) =0:=by
 obtain ⟨t,hf⟩:=leases (G:=G) P K a l
 let S:=widest P K
 obtain ⟨ht,he⟩:=smooth_launch S (show S.patch.Branches S.kernel G from h) t (anchor P a)
 dsimp only at ht he
 let q (v:Vectors P G):In G (wideFine P) × G.Color:=(port P v,v none)
 have hq:ContDiff ℝ ω q:=(ports_smooth P).prodMk (contDiff_apply ℝ _ _)
 have hz:q 0=0:= Prod.ext (empty P) rfl
 have hx := (show ContDiffAt ℝ ω (fun x=> temperature S t (anchor P a) ((represent (G:=G) x.1),fun _=>G.lieExp x.2)) (q 0) from hz.symm ▸ ht).comp (f:=q) 0 hq.contDiffAt
 change ContDiffAt ℝ ω ((fun v=> temperature S t _ (mount P v)) : Vectors P G→ℝ) _ at hx
 unfold S at hx; simp_rw [(fun v=>(hf v).1)] at hx
 exact ⟨hx,(hf _).1.symm.trans (by unfold mount; rw [empty]; exact he)⟩

private lemma ports_tend: Tendsto (port P (G:=G)) (𝓝 0) (𝓝 0):=by simpa only [empty] using (ports_smooth P (G:=G)).continuous.tendsto 0
lemma common_chip (h:P.Branches K G)(a:Mold)(l r:Leash P):
    chip P K a l (G:=G) =ᶠ[𝓝 0] chip P K a r := by
  let S:=widest P K
  obtain ⟨t,ht⟩:=leases (G:=G) P K a l
  obtain ⟨u,hu⟩:=leases (G:=G) P K a r
  filter_upwards [(ports_tend P).eventually (native_reports S h)] with v hv
  rw [← (hu v).1,← (ht v).1]; exact (tag_lemma P K h t u a v (hv _) (hv _)).1
lemma still_chip (h:P.Branches K G)(a:Mold)(l:Leash P):
    numberChip P K a l (G:=G) =ᶠ[𝓝 0] fun _ => numberChip P K a l (0:Vectors P G):=by
  let S:=widest P K
  have H:S.patch.Branches S.kernel G:=h
  obtain ⟨t,ht⟩:=leases (G:=G) P K a l
  have hz := native_reports S H
  filter_upwards [(ports_tend P).eventually hz] with v hv
  rw [← (ht v).2,← (ht 0).2]; have h0:native S t (represent (0:In G (wideFine P))):= mem_of_mem_nhds hz t
  unfold mount; rw [empty]
  rcases a with p|(_|i)
  · change marked S t (.inl _) _= marked S t (.inl _) _; rw [(terrace_face S H ..).2,(terrace_face S H ..).2]
  · let b:Site (width P):=0
    change marked S t (.inr (b,none)) _=marked S t (.inr (b,none)) _; rw [(terrace_station S H ..).2,(terrace_station S H ..).2]
    exact ((neat S t _ (hv _) 0 b).1).trans (neat S t _ h0 0 b).1.symm
  let q:Edge (Site (width P)):=(0,i)
  change marked S t (.inr (q.1,some q.2)) _=marked S t (.inr (q.1,some q.2)) _; rw [(terrace_bond S H t q _).2,(terrace_bond S H t q _).2]
  exact ((neat S t _ (hv _) i 0).2).trans (neat S t _ h0 i 0).2.symm
end YM.AveragedStep
