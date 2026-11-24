import YM.RegulatorIR.Quadratic.Hawk

/-! Folded quadratic exact transparency. Primitive-only clip. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Quadratic
open Lattice Function Budget Motion Budget.Layer Budget.Packet Budget.Deck Step Diagram RG Binding Filter Tree Tree.Forest Metric Set Geometry Geometry.Field PertExtension Chart Laplace GaussianScore Matrix Wilson Orb Series Series.Radial Diagram.Formal
open scoped NNReal ENNReal Topology Real Classical BigOperators ContDiff PowerSeries Matrix
variable {G:Gauge}{X Y:Type}{P:ℝ} {f c:Side} {S:StepData c f}{F: Forest S.ratio}
variable {A:Deck P X (Book G f)}{B:Deck P Y (Book G c)}{Yard:Scale}(J: GridStep A B)
variable {K N: Layer X X} {L:Layer Y Y} {Q:Layer Y X} {D:Layer X Y} (R: Bedload A B S.kernel.penalty (awake S F) K L Q D N)
variable (hv: J.line=petals (I:=Y) N)(he : J.driftL= Function.swap (hoses D))
lemma Terrain {X Y A' B':Type}(A:Deck P X A')(B:Deck P Y B')(D:Layer X Y) (h:Sym A B D): Sym (Step.combine A B) (Step.combine A B) (hoses D):=by
 intro d m n; cases m <;> cases n <;> rename_i i j <;> first|rfl|exact h d i j | (change ID Y (B.wind d i) (B.wind d j)=ID Y i j; simp [ID])
include he R in
lemma terrain : J.mean=lamber (fmat A B D):=by
 unfold GridStep.mean; rw [he]; let P:= Step.combine A B
 change fmat P P (Function.swap (hoses D))= _; rw [fmat_trans P P (hoses D) (Terrain A B D R.sym.2.2.1), fmat_hose]; rfl
include hv in
lemma endemic : J.layer=petals (fmat A A N):=by unfold GridStep.layer;rw [hv]; exact fmat_petals A B N
-- need remaining layer facts from genuine patch VERTEX later
abbrev ScrollA (J:GridStep A B): Orders (Book G f⊕Book G c):=fun i j=>(Step.combine A B).deckSum (J.addon i j)
def joins (S:StepData c f)(F:Forest S.ratio)(y:Meadow G (Wind F))(w:Horizon G c):=
 Sum.elim (foresh S F G y) (paper G c w)
structure Launch (S:StepData c f) (F : Forest S.ratio) (H: Scale)(J:GridStep A B):Prop where
 print (w: Horizon G c) y : PowerSeries.mk (fun i=> normTerm (aura (1:Hook G (Wind F) (OEdge c))) (priceMap (nextO S F H)) i (y,1,w)) = PowerSeries.C (morning G (Wind F)*Real.exp (-feeO S (injectX F y) w))*expo (flavor 2 (joins S F y w) (ScrollA J))
 symmetry : gradedSymmetric (ScrollA J)
 positive : Vacuum (ScrollA J)

variable (Z: Vertex (beneath (fmat A A K)))(Hx:∀ x:Horizon G f,(fmat B A Q) *ᵥ paper G f x=paper G c (rod G S x))(hc: Even c.val)(hf:Even f.val)
variable (h:Field.Square F)(V:S.patch.Branches S.kernel G) (Hr:Launch S F Yard J)
include Z R Hx V hc hf hv he h Hr
lemma boot : Nonempty (FitsO J S F Yard (beneath (fmat A A K)) (beneath (fmat B B L))) := by
 let q:=R.grid
 refine ⟨{ law:=stepLaw q Hx Z h hc hf V, slide := fun w=> panes S F (fmat A B D*ᵥ paper G c w), directions:=qualify S F,covariance:=by rw [believer q Hx Z h hc hf V, endemic J hv],symmetry:=Hr.symmetry,order:=Hr.positive, witness:=fun w x i=>?_,gap:=fun w x=>?_,sing:=fun w x=>?_ }⟩ -- universe implicit Genre
 · rw [terrain J R he]; exact (congr_fun (qualifies q x w) (Sum.inl i)).symm
 · rw [next_color Yard S V]; exact age q Hx w x
 dsimp only; rw [next_color Yard S V,Hr.print,terrain J R he]; exact congr_arg (fun b=> _ * expo (flavor 2 b _)) (qualifies q x w).symm
end YM.RegulatorIR.Quadratic
