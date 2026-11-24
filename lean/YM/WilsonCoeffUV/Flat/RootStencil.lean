import YM.WilsonCoeffUV.Flat.TreeProjection
import YM.Push.FREE_RESOLVENT.FullRow
/-!
# Repeated coordinate-order tree and contour stencils

Including BOTH occurrences of the imposed root convention. The centering row
of the block predictor is generally not a tree row.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Filter Function Lattice RG Laurent Exterior Bloch Metric Matrix Precision Stationary
open FreeResolvent Tree Work.F08
open UVNext.PricedKernels (rootAt hiker)
open scoped Topology BigOperators ComplexConjugate
variable {G:Gauge} {c f L : Side} {S : StepData c f} {P:Patch}

def bad (x : Cover) := Finset.univ.filter fun i : Axis=>x i≠0

def shrinkAt (x : Cover) : Step := if h : (bad x).Nonempty then
    if x ((bad x).min' h) < 0 then posDir ((bad x).min' h) else negDir ((bad x).min' h)
    else posDir 0

lemma shrink_spec {x : Cover} {n} (hx : x≠0) (hn : x∈box n) : x+(shrinkAt x).vec∈box n ∧
    size (x+(shrinkAt x).vec)<size x := by
  have hb : (bad x).Nonempty := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let a := (bad x).min' hb
  have h : x a≠0 := (Finset.mem_filter.mp (show a∈bad x from Finset.min'_mem _ _)).2
  let q := if x a<0 then posDir a else negDir a
  rw [show shrinkAt x=q from dif_pos hb]
  have hh (i : Axis) (hi : i ≠ a) : (x + q.vec : Cover) i=x i := by unfold q; split <;> simp [hi]
  have hz : (x + q.vec : Cover)∈box n := by
    rw [box_iff_layers]; intro i
    have hk := (box_iff_layers ..).mp hn i
    by_cases H : i=a
    · subst i; unfold Lattice.layers at *; unfold q; split <;> simp at * <;> omega
    rw [hh i H]; exact hk
  refine ⟨hz,?_⟩
  have hu : ((x+q.vec:Cover) a).natAbs<(x a).natAbs := by unfold q; split <;> simp <;> omega
  unfold Laurent.size; refine Finset.sum_lt_sum (fun i _ ↦ ?_) ⟨a,Finset.mem_univ _,hu⟩
  by_cases H : i=a
  · exact H.symm ▸ hu.le
  rw [hh i H]

def residueGo (P : Patch) (i : Site P.L) : Step := shrinkAt (lift i)
def successor (P : Patch) (i : Site P.L) := wrap P.L (lift i+(residueGo P i).vec)
def aRatio (P : Patch) : Ratio 1 P.L := ⟨P.L,by simp⟩
lemma descends {i : Site P.L} (h : i≠0) : size (lift (successor P i)) < size (lift i) := by
  have hh : lift i ≠ 0 := fun ht => h (by rw [← wrap_lift i,ht,map_zero])
  obtain ⟨ha,hb⟩ := shrink_spec hh (show lift i ∈ box _ from (aRatio P).half_box P.odd_side i)
  have he : lift (successor P i)=lift i+(residueGo P i).vec := (aRatio P).half_lift P.odd_side _ ha
  rw [he]; exact hb

noncomputable def residueWalk (P : Patch) (i : Site P.L) : Walk := if _h : i ≠ 0 then
    residueGo P i :: residueWalk P (successor P i) else []
termination_by size (lift i)
decreasing_by apply descends _h

lemma go_ok {g:Ratio c f} (ho:Odd g.count.val) {x:Site f} (h:leaf g x) :
    g.parent (x+(shrinkAt (lift (g.residue x))).vec)=g.parent x ∧
    size (lift (g.residue (x+(shrinkAt (lift (g.residue x))).vec)))<size (lift (g.residue x)) := by
  have he : lift (g.residue x)≠0 := fun e=> h ((g.root_id x).2 (by rw [← wrap_lift (g.residue x), e,map_zero]))
  obtain ⟨hx,hv⟩ := shrink_spec he (g.half_box ho (g.residue x))
  obtain ⟨hh,h⟩ := g.internal ho hx
  exact ⟨h,hh ▸ hv⟩

def repeatF (S:StepData c f) : Forest S.ratio where
  up i := residueGo S.patch (S.ratio.residue i)
  height i := size (lift (S.ratio.residue i))
  bound i := by
    unfold Laurent.size
    apply le_trans (b:=∑ _ : Axis,S.ratio.count.val) (Finset.sum_le_sum fun j _ => ?_) (by simp [Axis])
    have h := (box_iff_layers ..).mp (S.ratio.half_box S.patch.odd_side (S.ratio.residue i)) j
    unfold Lattice.layers at h; rw [Finset.mem_Icc] at h; omega
  rise _ h := (go_ok S.patch.odd_side h).2
  stays _ h := (go_ok S.patch.odd_side h).1
lemma leaf_test (g : Ratio c f) (x : Site f) : leaf g x ↔ g.residue x≠0 := not_congr (g.root_id _)
lemma repeats (S : StepData c f) (x : Site f) : (repeatF S).hike x=residueWalk S.patch (S.ratio.residue x) := by
  induction x using Forest.hike.induct (repeatF S) with
  | case1 x h ih =>
    rw [Forest.hike,dif_pos h,ih]; conv_rhs => rw [residueWalk]
    split; swap; next hN => exact False.elim (hN ((leaf_test _ _).mp h))
    have he : S.ratio.residue (x+((repeatF S).up x).vec)=successor S.patch (S.ratio.residue x) := by
      rw [← show wrap f ((repeatF S).up x).vec=((repeatF S).up x).vec from wrap_vec ..,moves_residue]; rfl
    rw [he]; rfl
  | case2 x h =>
    rw [Forest.hike,dif_neg h]; conv_rhs => rw [residueWalk]
    split; next hN => exact False.elim (((leaf_test _ _).not.mp h) hN)
    rfl

def zeroLift {α β : Type*} (R : Matrix α β ℝ) : Row α β := fun i j x=> if x=0 then R i j else 0
lemma zero_act {α β : Type*} (R : Matrix α β ℝ) (i j) : (zeroLift R).acts L i j=if i.1=j.1 then R i.2 j.2 else 0 := by
  unfold Row.acts; dsimp only [Matrix.of_apply]
  rw [tsum_eq_single 0]; · simp [zeroLift,eq_comm]
  intro x hx; simp [hx,zeroLift]

-- Cost is post L, known at all widths.
def Priced {α β:Type*} (Q : Row α β) (s : ℝ) := ∃ C : ℝ,0≤C ∧ Q.strip s C
variable {α β γ δ : Type} {η C:ℝ}
lemma zeroLift_price [Fintype α] [Fintype β] (R : Matrix α β ℝ) : Priced (zeroLift R) η := by
  apply Draw.ready_strip
  intro i j s
  have hh x (hx:x≠0) : Real.exp (s*size x)*‖zeroLift R i j x‖=0 := by simp [zeroLift,hx]
  let v := fun x : Cover=>Real.exp (s*size x)*‖zeroLift R i j x‖
  have he x : 0 ≤ v x := by unfold v; positivity
  exact ⟨v 0,he 0,he,summable_of_ne_finset_zero (s:={0}) fun b hb=> hh b (by simpa using hb),(tsum_eq_single 0 hh).le⟩
lemma Priced.chain {U:Row α β} {V:Row β γ} [Fintype β] (h:Priced U η) (g:Priced V η) (hs:0≤η) : Priced (composeRows U V) η := by
  obtain ⟨a,ha,h⟩ := h; obtain ⟨b,hb,g⟩ := g; exact ⟨_,by positivity, strip_compose hs h g⟩
lemma Priced.plus {U V:Row α β} (h:Priced U η) (g:Priced V η) : Priced (plusRows U V) η := by
  obtain ⟨a,ha,h⟩ := h; obtain ⟨b,hb,g⟩ := g; exact ⟨_,by positivity, strip_plus h g⟩
lemma Priced.minus {U V:Row α β} (h:Priced U η) (g:Priced V η) : Priced (minusRows U V) η := by
  obtain ⟨a,ha,h⟩ := h; obtain ⟨b,hb,g⟩ := g; exact ⟨_,by positivity, strip_minus h g⟩
lemma Priced.acts_chain {U:Row α β} {V:Row β γ} [Fintype β] (h:Priced U η) (g:Priced V η) (hs:0≤η) (c:Side) :
    (composeRows U V).acts c=U.acts c*V.acts c := by obtain ⟨_,-,h⟩ := h; obtain ⟨_,-,g⟩ := g; exact acts_compose hs h g c
lemma Priced.acts_plus {U V:Row α β} (h:Priced U η) (g:Priced V η) (hs:0≤η) (c:Side) :
    (plusRows U V).acts c=U.acts c+V.acts c := by obtain ⟨_,-,h⟩ := h; obtain ⟨_,-,g⟩ := g; exact FreeResolvent.acts_plus h g hs c
lemma Priced.acts_minus {U V:Row α β} (h:Priced U η) (g:Priced V η) (hs:0≤η) (c:Side) :
    (minusRows U V).acts c=U.acts c-V.acts c := by obtain ⟨_,-,h⟩ := h; obtain ⟨_,-,g⟩ := g; exact Work.F08.acts_minus hs h g c

-- Basic repacks
lemma backed [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {α' β' : Type} [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']
    (s:α ≃ α') (t:β≃β') (R:Matrix α' β' ℝ) (U:Matrix α β ℝ) (h:U=R.submatrix s t) : repackM s t U=R := by
  rw [h]; ext i j; simp [repackM]
lemma repack_return [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [Fintype δ] [DecidableEq δ] (s:α≃β) (t:γ≃δ) (R:Matrix α γ ℝ) : repackM s.symm t.symm (repackM s t R)=R := by ext; simp [repackM]

-- introduce colors uniformly over all four combinations (crosses)
def coloration {α' β' : Type*} (G:Gauge) (x:α'→α×G.ColorIndex) (y:β'→β×G.ColorIndex) (R:Row α β) : Row α' β' := fun i j k =>
    if (x i).2=(y j).2 then R (x i).1 (y j).1 k else 0

lemma coloration_act {α' β' : Type*} (x:α'→α×G.ColorIndex) (y:β'→β×G.ColorIndex) (R:Row α β) (i j) :
    (coloration G x y R).acts L i j=if (x i.2).2=(y j.2).2 then R.acts L (i.1,(x i.2).1) (j.1,(y j.2).1) else 0 := by
  unfold coloration Row.acts; dsimp only [Matrix.of_apply]; split_ifs <;> simp_all

lemma coloration_paid {α' β' : Type*} (x:α'→α×G.ColorIndex) (y:β'→β×G.ColorIndex) (R:Row α β) (he:0≤C) (h:R.strip η C) :
    (coloration G x y R).strip η C := by
  intro a b; unfold coloration; split <;> first | exact h _ _ | simp [Width,RG.SumBudget,he]
lemma Priced.colored {α' β' : Type*} (x:α'→α×G.ColorIndex) (y:β'→β×G.ColorIndex) {R:Row α β} (h:Priced R η) :
    Priced (coloration G x y R) η := by obtain ⟨C,hC,h⟩ := h; exact ⟨C,hC,coloration_paid x y _ hC h⟩

def expandI (G:Gauge) (L:Side) (s : ℕ) (x:Co L (PAC G s)) : Co L (TypeFace s) × G.ColorIndex :=
    ((x.1,x.2.1),x.2.2)
lemma colored_backed {a b : ℕ} (A:Row (Co S.patch.L (TypeFace a)) (Co S.patch.L (TypeFace b)))
    (U:Matrix (Body a f) (Body b f) ℝ)
    (h:U=(A.acts c).submatrix (splitCo S.ratio (TypeFace a)) (splitCo S.ratio (TypeFace b))) :
    (coloration G (expandI G _ _) (expandI G _ _) A).acts c=repackM (unitSplit G S a) (unitSplit G S b) (tensor G U) := by
  classical
  symm; apply backed; ext i j; rcases i with ⟨x,i,u⟩; rcases j with ⟨y,j,v⟩
  simp only [unitSplit,Matrix.submatrix_apply,split_co,coloration_act,h,tensor,Matrix.of_apply,expandI]; rfl
lemma cross_backed {a b : ℕ} (A:Row (Co S.patch.L (TypeFace a)) (TypeFace b)) (U:Matrix (Body a f) (Body b c) ℝ)
    (h:U=installed S.ratio A) :
    let R:=coloration G (expandI G _ _) id A
    R.acts c=repackM (unitSplit G S a) (Equiv.refl _) (tensor G U) := by
  classical
  dsimp only; symm; apply backed; ext i j; rcases i with ⟨x,i,u⟩; rcases j with ⟨y,j,v⟩
  rw [Matrix.submatrix_apply, unitSplit, split_co, coloration_act,h]
  unfold tensor; simp only [Matrix.of_apply,expandI,installed, Matrix.submatrix_apply,split_co]; rfl
lemma across_backed {a b : ℕ} (A:Row (TypeFace a) (Co S.patch.L (TypeFace b))) (U:Matrix (Body a c) (Body b f) ℝ)
    (h:U=(A.acts c).submatrix id (splitCo S.ratio (TypeFace b))) :
    (coloration G id (expandI G _ _) A).acts c=repackM (Equiv.refl _) (unitSplit G S b) (tensor G U) := by
  classical
  symm; apply backed; ext i j; rcases i with ⟨x,i,u⟩; rcases j with ⟨y,j,v⟩
  rw [Matrix.submatrix_apply,unitSplit,split_co,coloration_act,h]; unfold tensor
  simp only [Matrix.of_apply,expandI,Matrix.submatrix_apply,split_co]; rfl

-- native basic stencils
lemma grow_period {r s : ℕ} (U:Row (TypeFace r) (TypeFace s)) (S:StepData c f) (h:Priced U η) (he:0≤η) :
    U.acts f=((fineCompose U (unitRow (Co S.ratio.count _))).acts c).submatrix (splitCo S.ratio _) (splitCo S.ratio (TypeFace s)) := by
  let E:=splitCo S.ratio (TypeFace s)
  obtain ⟨a,-,h⟩ := h
  have hh : installed S.ratio (unitRow (Co S.ratio.count (TypeFace s))) = (1:Matrix _ _ ℝ).submatrix E id := by
    unfold installed; rw [acts_unit]
  ext i j; change _=installed S.ratio _ i (E j)
  rw [installed_fine S.ratio he h strip_unit,hh]; simp [Matrix.mul_apply,Matrix.one_apply,E.injective.eq_iff]

def gradS (G:Gauge) (P:Patch) := coloration G (expandI G P.L 1) (expandI G P.L 0) (fineCompose (cobound 0) (unitRow _))
lemma gradS_paid (h:0≤η) : Priced (gradS G P) η := by
  obtain ⟨k,hk,H⟩ := cobound_ready 0 η
  exact Priced.colored _ _ ⟨_,by positivity,strip_fine h H (strip_unit (α:=Co P.L _))⟩
lemma gradS_period : (gradS G S.patch).acts c=repackM (unitSplit G S 1) (unitSplit G S 0) (tensor G (d 0 f)) :=
    colored_backed _ _ (grow_period _ _ (cobound_ready _ 0) le_rfl)

def upRow (P:Patch) : Row (Co P.L (TypeFace 0)) (Co P.L (TypeFace 1)) := fun a=>Draw.path P.L (lift a.1) (residueWalk P a.1)
def climbS (G:Gauge) (P:Patch) := coloration G (expandI G P.L 0) (expandI G P.L 1) (upRow P)
lemma climbS_paid : Priced (climbS G P) η := by
  apply Priced.colored
  exact Draw.ready_strip (R:= upRow P) (fun i=> Draw.path_ready _ _) η
lemma climbS_period : (climbS G S.patch).acts c=repackM (unitSplit G S 0) (unitSplit G S 1) (tensor G (hiker S (repeatF S))) := by
  apply colored_backed
  ext i j
  simp only [Matrix.submatrix_apply, split_co]
  rw [hiker,LinearMap.toMatrix'_apply]
  dsimp only [LinearMap.pi_apply]
  let x := i.1; let p := S.ratio.parent x; let z := S.ratio.residue x
  have hz := Draw.spot_path (g:=S.ratio) p j (Lattice.lift z) (residueWalk S.patch z)
  rw [add_comm,S.ratio.unpack_at] at hz
  unfold Draw.spot at hz; rw [split_co] at hz; rw [repeats]; exact hz.symm

def fixS (G:Gauge) (P:Patch) : Row (PAC G 0) (Co P.L (PAC G 1)) := coloration G id (expandI G P.L _) (rootRow P)
lemma fixS_paid : Priced (fixS G P) η := Priced.colored _ _ (ready_rootRow P η)
lemma fixS_period : (fixS G S.patch).acts c=repackM (Equiv.refl _) (unitSplit G S 1) (tensor G (fixRoot S)) :=
    across_backed _ _ (block_root _)

def sameRoot (P:Patch) := zeroLift (fun (_:Co P.L (TypeFace 0)) (_:TypeFace 0)=> (1:ℝ))
def copyS (G:Gauge) (P:Patch) : Row (Co P.L (PAC G 0)) (PAC G 0) := coloration G (expandI G P.L _) id (sameRoot P)
lemma copyS_paid : Priced (copyS G P) η := Priced.colored _ _ (zeroLift_price _)
lemma copyS_period : (copyS G S.patch).acts c=repackM (unitSplit G S 0) (Equiv.refl _) (tensor G (rootAt S.ratio)) := by
  apply cross_backed
  ext i j; rcases i with ⟨i,a⟩; rcases j with ⟨j,b⟩; rw [vac_only a,vac_only b]
  unfold rootAt installed sameRoot; rw [Matrix.submatrix_apply,split_co]; erw [zero_act,LinearMap.toMatrix'_apply]
  simp [Pi.single_apply]

def buttS (G:Gauge) (P:Patch) := zeroLift (shardX (Co P.L (Loc G 1)) (Loc G 0) ℝ)
def brimS (G:Gauge) (P:Patch) := zeroLift (shardY (Co P.L (Loc G 1)) (Loc G 0) ℝ)
lemma buttS_period : (buttS G S.patch).acts c=repackM (unitSplit G S 1) (clothe G S) (butt G c f) := by
  classical
  symm; apply backed; rw [helmet_butt]; ext i j; cases j with
  | inl j=>
    rw [Matrix.submatrix_apply, inflowL,buttS,zero_act]
    have hh : i=j ↔ (unitSplit G S 1 i).1=(unitSplit G S 1 j).1 ∧ (unitSplit G S 1 i).2=(unitSplit G S 1 j).2 := by rw [← Prod.ext_iff]; exact (unitSplit G S 1).injective.eq_iff.symm
    simp only [shardX,LinearMap.toMatrix'_apply,LinearMap.pi_apply,LinearMap.proj_apply,Pi.single_apply,Sum.inl.injEq,hh,ite_and]; simp only [StepData.ratio,unitSplit] at *; simp; congr!
  | inr j =>
    rw [Matrix.submatrix_apply,buttS,zero_act,show clothe G S (.inr j)= (j.1,Sum.inr j.2) from rfl]; simp [shardX,LinearMap.toMatrix'_apply]
lemma brimS_period : (brimS G S.patch).acts c=repackM (Equiv.refl _) (clothe G S) (brim G c f) := by
  classical
  symm; apply backed; rw [helmet_brim]; ext i j; cases j with
  | inl j => rw [Matrix.submatrix_apply,inflowL,brimS,zero_act]; simp [shardY,LinearMap.toMatrix'_apply]
  | inr j =>
    rw [Matrix.submatrix_apply,brimS,zero_act,show clothe G S (.inr j)= (j.1,Sum.inr j.2) from rfl]
    simp only [shardY,LinearMap.toMatrix'_apply,LinearMap.pi_apply,LinearMap.proj_apply,Pi.single_apply,Sum.inr.injEq,Equiv.refl_apply]; simp only [Prod.ext_iff,ite_and]

def turningS (G:Gauge) (P:Patch) :=
    minusRows (composeRows (climbS G P) (buttS G P)) (composeRows (copyS G P)
        (plusRows (brimS G P) (composeRows (fixS G P) (buttS G P))))

def projector (G:Gauge) (P:Patch) : Row (Co P.L (PAC G 1)) (ParcelG G P.L) := plusRows (buttS G P) (composeRows (gradS G P) (turningS G P))
lemma steering (h:0≤η) : Priced (turningS G P) η :=
    (climbS_paid.chain (zeroLift_price _) h).minus (copyS_paid.chain ((zeroLift_price _).plus (fixS_paid.chain (zeroLift_price _) h)) h)
lemma projector_price (h:0≤η) : Priced (projector G P) η :=
    (zeroLift_price _).plus ((gradS_paid h).chain (steering h) h)
lemma steering_period : (turningS G S.patch).acts c=repackM (unitSplit G S 0) (clothe G S) (turning G (repeatF S)) := by
  classical
  let Q := turning G (repeatF S)
  have ht : Priced (buttS G S.patch) 0 := zeroLift_price _
  have hV : Priced (brimS G S.patch) 0 := zeroLift_price _
  unfold turningS
  rw [(climbS_paid.chain ht le_rfl).acts_minus (copyS_paid.chain (hV.plus (fixS_paid.chain ht le_rfl)) le_rfl) le_rfl,
      climbS_paid.acts_chain ht le_rfl, copyS_paid.acts_chain (hV.plus (fixS_paid.chain ht le_rfl)) le_rfl,
      hV.acts_plus (fixS_paid.chain ht le_rfl) le_rfl, fixS_paid.acts_chain ht le_rfl,
      climbS_period (S:=S),copyS_period (S:=S),fixS_period (S:=S),brimS_period (S:=S),buttS_period (S:=S)]
  unfold turning
  erw [show repackM (unitSplit G S 0) (clothe G S) (_ - _) = repackM (unitSplit G S 0) (clothe G S) (tensor G (hiker S (repeatF S)) * butt G c f) - repackM (unitSplit G S 0) (clothe G S) (tensor G (rootAt S.ratio) * (brim G c f + tensor G (fixRoot S) * butt G c f)) from rfl]
  rw [repack_multiply _ (unitSplit G S 1) _ _ (butt G c f), repack_multiply _ (Equiv.refl (Lines G c 0))]
  erw [show repackM (Equiv.refl _) (clothe G S) (_+_) = repackM (Equiv.refl _) (clothe G S) (brim G c f) + repackM (Equiv.refl _) (clothe G S) (tensor G (fixRoot S)*butt G c f) from rfl]
  rw [repack_multiply _ (unitSplit G S 1)]; rfl
lemma projector_period : (projector G S.patch).acts c=repackM (unitSplit G S 1) (clothe G S) (toTree G (repeatF S)) := by
  classical
  unfold projector
  have ht : Priced (buttS G S.patch) 0 := zeroLift_price _
  rw [ht.acts_plus ((gradS_paid le_rfl).chain (steering le_rfl) le_rfl) le_rfl,
     (gradS_paid (η:=0) le_rfl).acts_chain (steering le_rfl) le_rfl,
     steering_period (S:=S),gradS_period (S:=S),buttS_period (S:=S)]; erw [← repack_multiply (unitSplit G S 1) (unitSplit G S 0) (clothe G S)]; rfl
end YM.WilsonCoeffUV
