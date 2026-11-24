import YM.Contacts.Pulse.Binder
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Identity
namespace YM.Pulse.Spine.Origin
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Tree
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open scoped Classical Topology BigOperators NNReal ENNReal Matrix
noncomputable section
variable {G:Gauge}{L c f n:Side}{S: StepData c f}{P:Patch}{K:KernelChoices} {α β X Z:Type}
open FreeResolvent Larch
variable {s η:ℝ≥0}{a b C D ε:ℝ}{B B':Bed}{A: Stairs G P.L}
def bleed (G:Gauge) (R: voyage L): Row (Co L (Dye G)) (Dye G):= fun x y v=> if x.2.2=y.2 then R (x.1,x.2.1) y.1 v else 0
lemma bleed_strip {V:voyage L}(h:Row.strip V s a)(hc:0≤a): (bleed G V).strip s a:= by
  intro i j; unfold bleed; by_cases he:i.2.2=j.2; · simp only [bleed,he,↓reduceIte]; apply h
  simp only [bleed,if_neg he]; simpa [Width] using (budget_loosen (budget_zero (α:=Cover)) hc)
lemma bleeding {g:Ratio c f} (V:voyage g.count): installed g (bleed G V)=tensor G (installed g V):= by
  ext ⟨i,a,j⟩ ⟨z,b,k⟩; by_cases he:j=k <;> simp [installed,Row.acts,split_co, bleed,he,tensor]
lemma advance_bleed (V:voyage L)(l:List Axis) : advanceC L (bleed G V) l= bleed G (advanceC L V l):= by induction l with | nil=>rfl | cons i l ih=> rw [advanceC,ih]; ext ⟨r,a,b⟩ ⟨p,u⟩ z; by_cases h:b=u <;> simp [bleed,h,advanceC,forwardC]
def castProbe (P:Patch)(G:Gauge) : Cross P.L (Dye G) (Dye G):= bleed G (transRows (probeRow P))
lemma smock (S: StepData c f) : installed S.ratio (castProbe S.patch G)= (tensor G (probe S))ᵀ:= by
  apply (bleeding (g:=S.ratio) _).trans; rw [tensor_transpose]; congr 1; rw [block_probe,Matrix.transpose_submatrix,installed]; exact congr_arg (fun M=> M.submatrix (splitCo S.ratio _) id) (acts_trans _ c)
def stretch (P:Patch)(K:KernelChoices)(G:Gauge)(V:Stairs G P.L) : Cross P.L (Dye G) (Dye G):= composeRows (prom V) (scaleRows K.penalty (castProbe P G))
lemma widen (P:Patch)(K:KernelChoices)(G:Gauge)(V:Stairs G P.L) (h:V.strip (s:ℝ) a)(he:0≤a) : (stretch P K G V).strip (s:ℝ) ((Fintype.card (Cellar G P.L):ℝ)*(a*(‖K.penalty‖*(probe_ready P s s.property).choose))) := by
  obtain ⟨hc,hp⟩:= (probe_ready P s s.property).choose_spec; exact strip_compose s.property (brace V h he) (strip_scale (bleed_strip (strip_trans hp) hc) _)
local notation "T" => planting S.ratio S.patch.odd_side
lemma stretch_books (V:Stairs G S.patch.L) (h:Whole B.metric)(hp:Cabinet (brick G S.patch S.kernel.penalty B) V) (hv:V.strip (s:ℝ) a)(ha:0≤a): installed S.ratio (stretch S.patch S.kernel G V) = covariance G S T B.metric * (S.kernel.penalty • (tensor G (probe S))ᵀ):= by
  obtain ⟨hc,hU⟩:= (probe_ready S.patch s s.property).choose_spec
  have hl := acts_compose s.property (brace V hv ha) (strip_scale (P:=castProbe S.patch G) (bleed_strip (strip_trans hU) hc) S.kernel.penalty) c -- P ?
  let e:=splitCo S.ratio (Dye G)
  rw [issue h hp, ← smock, stretch,installed]; apply Eq.trans (congr_arg (fun X=>X.submatrix (e:Co _ _→ Co c (Cellar G S.patch.L)) id) hl); rw [acts_scale,installed]; exact (Matrix.submatrix_mul_equiv _ (S.kernel.penalty • (castProbe S.patch G).acts c) e e id).symm 
open PhysicalNext.RankCovariance
lemma rise_roll (V:Stairs G S.patch.L) (h:Whole B.metric)(hp:Cabinet (brick G S.patch S.kernel.penalty B) V)(hv:V.strip (s:ℝ) a)(ha:0≤a){R:voyage S.patch.L}(H:Inputs S (installed S.ratio R) (B.metric.acts f) (B'.metric.acts c)):
    installed S.ratio (stretch S.patch S.kernel G V) = tensor G (extracted S T (installed S.ratio R)):= by
  rw [stretch_books V h hp hv ha]; let C:= (probe S); let θ:= tensor G C; let J := installed S.ratio R; let r:= treeMatrix G S T B.metric
  let Q:= tensor G (extracted S T J); let F:= fullMatrix G S B.metric; let i:= insertion (plant (G:=G) T); let E:= reduce G S T
  have he := stationed T J (B.metric.acts f) _ H; set b:= S.kernel.penalty
  have hQ : F* Q = b • θᵀ:= by
    change tensor G _ * tensor G _=_; rw [show θ=tensor G C from rfl, tensor_transpose, ← promote_prod, ← promote_coeff]; congr 1
    unfold baseMatrix; rw [Matrix.add_mul,he.2,Matrix.smul_mul,Matrix.mul_assoc (probe S)ᵀ,he.1,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul, smul_sub, smul_smul, mul_inv_cancel₀ S.kernel.penalty_pos.ne',one_smul]; abel
  have hl : i * E * Q=Q := by
    apply Matrix.ext_iff_mulVec.mpr; intro v; rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]; apply projects T _; intro j; rw [show Q=tensor G _ from rfl,component_mul]; exact Precision.stays _ _ _
  let Y := treeInverse G S T B.metric 0
  have hI : Y * r = 1:= by
    unfold Y r; rw [inside h hp,front h]; let e:=aperture S.ratio S.patch.odd_side G; calc
      _ = ((V.acts c) * (brick G S.patch b B).acts c).submatrix e e:= (Matrix.submatrix_mul_equiv _ _ e e e)
      _ = _ := by
        have h : (V.acts c) * (brick G S.patch b B).acts c = 1:= by convert hp.l c using 1; any_goals congr!
        refine (congr_arg (fun q=>q.submatrix (e:Active G T→Co c (Loose G S.patch.L)) e) h).trans ?_; convert submatrix_one_equiv (α:=ℝ) e using 1; any_goals congr!
  rw [show S.kernel.penalty • _=b • θᵀ from rfl, ← hQ]
  change (i*Y*E)*(F*Q) = Q
  have hu : (E*F)*i=r:= FreeResolvent.insertion.compress ..
  calc
    _ = (i*(Y*(E*F*i)))*E*Q := by
      conv_lhs=> rw [← hl]
      simp only [Matrix.mul_assoc]
    _ = Q:= by rw [hu,hI,Matrix.mul_one,hl]
end
end YM.Pulse.Spine.Origin
noncomputable section
namespace YM.Pulse.Spine.Origin
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Tree
open Finset Bloch Laurent Push.AbsoluteSums Extra.Iteration MergeProof Next.Free Work.F08 Extension.UV.Linear
open FreeResolvent Larch
open scoped Classical Topology BigOperators NNReal ENNReal Matrix
variable {G:Gauge}{L c f n:Side}{S: StepData c f}{P:Patch}{K:KernelChoices} {α β X Z:Type}
variable {s η:ℝ≥0}{a b C D ε:ℝ}{B B':Bed}{A A': Stairs G P.L}
lemma h_all (h:Whole B.metric): Whole (hBlock B.metric):= (Whole.boundary 1).flipped.prod (h.prod (Whole.boundary 1))
lemma kroot (h: Whole B.metric): hBlock B.metric=krow B.metric:= by
  apply bank_injective (h_all h).safe (k_capacity h).safe; intro n; obtain ⟨s,C,hs,h⟩:=h; rw [hBlock_periods hs.le h]; exact (Krow_acts _ ⟨s,C,hs,h⟩ n).symm
lemma reblock_all {X: Row α α}[Fintype α][DecidableEq α] (h:Whole X): Whole (reblock L X):= by obtain ⟨s,c,hs,h⟩:=h; exact ⟨s,_,hs,reblock_price hs.le h⟩
lemma reblock_less {X Y:Row α α}[Fintype α][DecidableEq α](h:Whole X)(hp:Whole Y): minusRows (reblock L X) (reblock L Y)= reblock L (minusRows X Y):= by
  apply bank_injective ((reblock_all h).minus (reblock_all hp)).safe (reblock_all (h.minus hp)).safe; intro c
  let g:Ratio c (c*L):=⟨L,rfl⟩; let e:=splitCo g α; have he (H:Row α α) (hv:Whole H): (reblock L H).acts c = (H.acts (c*L)).submatrix e.symm e.symm:= by
    obtain ⟨s,K,hs,hk⟩:= hv; rw [reblock_periods g hs.le hk]; ext a b; simp [e]; rfl
  rw [(reblock_all h).less (reblock_all hp), he X h, he Y hp,he _ (h.minus hp), h.less hp,Matrix.submatrix_sub]; rfl
lemma levy_grid (P:Patch)(k:ℝ)(h:Whole B.metric)(hp:Whole B'.metric): minusRows (brick G P k B) (brick G P k B')=fun i j=> colorRow G (reblock P.L (minusRows (krow B.metric) (krow B'.metric))) (r:=1) i.val j.val:= by
  ext i j p; rw [← kroot h, ← kroot hp, ← reblock_less (h_all h) (h_all hp)]; unfold brick FreeResolvent.fullRow colorRow flatRow FreeResolvent.plusRows scaleRows minusRows; split<;> simp_all
lemma pigment {s:ℝ≥0}{H:Row (Co L (TypeFace 1)) (Co L (TypeFace 1))}(h:H.strip s a)(ha:0≤a): (colorRow G H).strip s a:= by
  intro i j; unfold colorRow; split -- split creates dependent k issue
  · apply h
  simpa [Width] using (budget_loosen (budget_zero (α:=Cover)) ha)
lemma prom_diff {A A' : Stairs G P.L}: minusRows (prom A) (prom A')=prom (minusRows A A'):= by ext i j p; unfold prom minusRows; split_ifs <;> simp_all
lemma compositional [Fintype β]{X Y : Row α β}{T:Row β Z} (h: Whole X)(hp:Whole Y)(hv:Whole T): minusRows (composeRows X T) (composeRows Y T)=composeRows (minusRows X Y) T:= by
  apply bank_injective ((h.prod hv).minus (hp.prod hv)).safe ((h.minus hp).prod hv).safe; intro n; rw [(h.prod hv).less (hp.prod hv), (h.minus hp).acts hv,h.acts hv,hp.acts hv,h.less hp, Matrix.sub_mul]
abbrev payDiff (P:Patch)(G:Gauge)(a:ℝ) := let d:ℝ:= Fintype.card (Loose G P.L); d*(d*(a*(Fintype.card (TypeFace 1):ℝ))*a)
def tiltDiff (P:Patch)(K:KernelChoices)(G:Gauge)(s:ℝ≥0)(a:ℝ):ℝ:= Fintype.card (Cellar G P.L)*(payDiff P G a*(‖K.penalty‖*(probe_ready P s s.property).choose))
lemma charge_sqr (k:ℝ)(h:Whole B.metric)(hp:Whole B'.metric)(hx:Cabinet (brick G P k B) A)(hy: Cabinet (brick G P k B') A')(hc:A.strip (s:ℝ) a)(he:A'.strip s a)(hf:(portfolio B.metric B'.metric).strip s C) (hs:0<s)(hC:0≤C)(ha:0≤a):
    (minusRows A' A).strip s (C*payDiff P G a) ∧ (minusRows (prom A') (prom A)).strip s (C*payDiff P G a):= by
  have hσ : 0<(s:ℝ):= hs; have hK (B:Bed)(h:Whole B.metric) : Whole (brick G P k B) := by
    obtain ⟨u,c,hu,h⟩:=h; exact ⟨u,_,hu,fun i j=> fullRow_width P k hu.le (Cost.nonneg (h (plaquette (Classical.arbitrary PlaqAxes)) (plaquette (Classical.arbitrary PlaqAxes)))) h i.val j.val⟩
  have hG : (minusRows A' A).strip s (C*payDiff P G a):= by
    rw [borrow_difference hy hx (hK _ hp) (hK _ h) ⟨_,_,hσ,he⟩ ⟨_,_,hσ,hc⟩, levy_grid P k h hp]; convert strip_compose s.property (strip_compose s.property he (fun (i j:Loose G P.L)=> pigment (reblock_price s.property hf) (mul_nonneg (Nat.cast_nonneg _) hC) i.val j.val)) hc using 1 <;> try rfl
    unfold payDiff; ring
  refine ⟨hG, by rw [prom_diff]; exact brace _ hG (mul_nonneg hC (show 0≤payDiff P G a by unfold payDiff; positivity))⟩
lemma radii (h:Whole B.metric)(hp:Whole B'.metric)(hx:Cabinet (brick G P K.penalty B) A)(hy: Cabinet (brick G P K.penalty B') A')(hc:A.strip (s:ℝ) a)(he:A'.strip s a)(hf:(portfolio B.metric B'.metric).strip s C) (hs:0<s)(hC:0≤C)(ha:0≤a):
    (minusRows (stretch P K G A') (stretch P K G A)).strip s (C* tiltDiff P K G s a):= by
  obtain ⟨hσ,_⟩:= (show 0<(s:ℝ)∧ True from ⟨hs,trivial⟩); obtain ⟨hl,hU⟩:= (probe_ready P s s.property).choose_spec; let F:= (castProbe P G); have hV := strip_scale (P:=F) (bleed_strip (strip_trans hU) hl) K.penalty; unfold stretch; rw [compositional ⟨_,_,hσ,brace _ he ha⟩ ⟨_,_,hσ,brace _ hc ha⟩ ⟨_,_,hσ,hV⟩]; convert strip_compose s.property (charge_sqr _ h hp hx hy hc he hf hs hC ha).2 hV using 1 <;> try rfl
  unfold tiltDiff; ring
end YM.Pulse.Spine.Origin
