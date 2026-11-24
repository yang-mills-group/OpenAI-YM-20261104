import YM.FormalBulk08.Flat.Stick

/-! Enrolling path stencils and residues. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08 Stationary Tree
open scoped Topology BigOperators Matrix
variable {G : Gauge} {P : Patch} {K : KernelChoices} {c f : Side} {S : StepData c f}

section act
variable {a b d e : Type} [Fintype a] [Fintype b] [Fintype d] [Fintype e]
    [DecidableEq a] [DecidableEq b] [DecidableEq d] [DecidableEq e]
lemma repack_sees (p : a≃b) (q : d≃e) (M : Matrix a d ℝ) (i : a) (v : e→ℝ) :
    (repackM p q M *ᵥ v) (p i)= (M*ᵥ (v ∘ q)) i := by
  conv_lhs => rw [show v=(v ∘ q) ∘ q.symm from funext fun j=>by simp,repack_act _ _ M (v ∘ q)]
  simp
-- universal axis. A Stick stencil turns repeats into an actual row.
omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
end act

variable (P K)
namespace Lodge
variable (G) (T : Lodge P)

def hikes (x : Co P.L (Loc G 0)) := let S:=primary P K 1
    stride G P (lift x.1) x.2.2 ((forest (S:=S) T).hike (S.ratio.assemble (0,x.1)))
def fatherStick (x : Co P.L (Loc G 0)) : Stick (Loc G 0) := Finsupp.single (0,vac,x.2.2) 1
variable {G}
lemma hikes_become (c : Side) :
    let S:=primary P K c
    (deposit (hikes G P K T)).acts c = repackM (unitSplit G S 0) (unitSplit G S 1) (patron G (trails S T.forest)) := by
  intro S
  classical
  apply mat_confirm; intro v
  funext j
  obtain ⟨⟨x,b⟩,rfl⟩ := (unitSplit G S 0).surjective j
  erw [repack_sees, unitSplit,split_co,stick_eval]
  let U:=primary P K 1; let y:=U.ratio.assemble (0,S.ratio.residue x)
  have hp : stretch S (S.ratio.parent x) (lift (S.ratio.residue x))=x := by unfold stretch; rw [add_comm]; exact Ratio.unpack_at ..
  rw [roots_pictured]
  change tollHere (S.ratio.parent x) v (stride G P (lift (S.ratio.residue x)) b.2 ((forest (S:=U) T).hike y))=_
  have h := compatible K P T 1 c y x (by unfold y; rw [Ratio.assemble_res])
  exact calc
    _ = integralLink (stretch S (S.ratio.parent x) (lift (S.ratio.residue x))) ((forest (S:=U) T).hike y) (atPaint (v ∘ unitSplit G S 1) b.2) := line_seen ..
    _ = _ := by rw [hp,h]; rfl
lemma father_serves (c : Side) :
    let S:=primary P K c
    (deposit (fatherStick P (G:=G))).acts c=repackM (unitSplit G S 0) (Equiv.refl (Lines G c 0)) (patron G (apices S)) := by
  intro S; classical
  apply mat_confirm; intro v; funext j
  obtain ⟨⟨x,b⟩,rfl⟩ := (unitSplit G S 0).surjective j
  erw [repack_sees,peak_seen,unitSplit,split_co,stick_eval]
  simp [tollHere,fatherStick]
end Lodge

variable {P K}

def capStick (G : Gauge) (P : Patch) (a : P.Points) (i : G.ColorIndex) :=
    -((Fintype.card P.Points:ℝ)⁻¹ • ∑ b : P.Points,(Fintype.card Lattice.Order:ℝ)⁻¹ •
       ∑ o : Lattice.Order,stride G P a.val i (route a.val b.val o))
lemma cap_cost (S : StepData c f) (a : S.patch.Points) (i : G.ColorIndex) (x : Site c) (v : Co c (Co S.patch.L (Loc G 1))→ℝ) :
    tollHere x v (capStick G S.patch a i)=Precision.tau S x a (atPaint (v ∘ unitSplit G S 1) i) := by
  simp only [capStick,map_neg,map_smul,map_sum,Precision.tau,LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sum_apply,line_seen S x]; rfl

def decorated (G : Gauge) (P : Patch) (x : Loc G 0) :=
    capStick G P P.center x.2 - ∑ b : P.Points,P.weight b • capStick G P b x.2
lemma decorated_service (S : StepData c f) : (deposit (decorated G S.patch)).acts c=repackM (Equiv.refl _) (unitSplit G S 1) (patron G (fixRoot S)) := by
  classical
  apply mat_confirm; intro v
  funext ⟨x,i,j⟩
  rw [stick_eval]
  simp only [decorated,map_sub,map_sum,map_smul,cap_cost S]
  have h:= congr_fun (paint_eats (fixRoot S) (v ∘ unitSplit G S 1) j) (x,i)
  have he := repack_sees (Equiv.refl _) (unitSplit G S 1) (patron G (fixRoot S)) (x,i,j) v
  apply Eq.symm
  refine he.trans (h.trans ?_)
  rw [fixRoot,LinearMap.toMatrix'_mulVec]; simp only [LinearMap.pi_apply,adjusted,LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply]

def coversRow (P : Patch) (G : Gauge) := fun (x : Loc G 0)=> (Finsupp.single (0,Sum.inr x) 1:Stick (ParcelG G P.L)) -- unnecessary K
lemma covers_service (S : StepData c f) : (deposit (coversRow S.patch G)).acts c=repackM (Equiv.refl _) (clothe G S) (brim G c f) := by
  classical
  apply mat_confirm; intro v; funext ⟨x,i⟩
  apply Eq.symm
  apply (repack_sees _ _ _ (x,i) v).trans
  rw [stick_eval]
  simp only [tollHere,coversRow,Finsupp.linearCombination_single,map_zero,add_zero,one_smul]
  rw [helmet_brim, sliceY]; rfl

def touchRow (T : Lodge P) (G : Gauge) : Row (Lodge.selected G P T) (Co P.L (Loc G 1)) := fun i=> unitRow _ i.val
lemma touch_service (S : StepData c f) (T : Lodge S.patch) :
    (touchRow T G).acts c=repackM (T.splitting (G:=G)) (unitSplit G S 1) (dropRoot G S T.forest) := by
  classical
  apply mat_confirm; intro v
  funext i
  obtain ⟨x,rfl⟩:= (T.splitting (G:=G)).surjective i
  erw [repack_sees,drop_apply]
  let L:=Co S.patch.L (Loc G 1)
  let p:=T.splitting x
  change ((unitRow L).acts c *ᵥ v) (p.1,p.2.val)=v (unitSplit G S 1 x.val)
  rw [acts_unit,Matrix.one_mulVec,T.alignment]
end YM.FormalBulk08.Flat
