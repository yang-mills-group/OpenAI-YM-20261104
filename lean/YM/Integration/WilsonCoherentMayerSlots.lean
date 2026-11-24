import YM.Integration.WilsonCoherentMayerSubmission
import YM.Integration.QLocalInheritedRegularSlots

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerSlots
open Function Finset Lattice Wilson RG PhysicalNext.Repeat Legato Lotus Progress.DirectedRecipe
open WilsonCoherentMayerSubmission
open scoped Classical
variable {G:Gauge} {f:Side} {A:Rep G f} {I:Type} [Fintype I]

def Shelf (A:Rep G f):Prop:=∀(a:RegularAddress f)(j:ℕ),
  A.activities.reg (blankRow f (a,j))=a ∧ A.activities.E (blankRow f (a,j))=0

theorem furnished (h:HasSlots A.p A.activities):Shelf A:=by
  intro a j
  exact ⟨h.reg ▸ congrArg Prod.fst (recorded (regularKeys f) a j),h.regular _⟩

theorem inherited (A:Rep G f):Shelf (QLocalInheritedRegularSlots.carrier A):=
  QLocalInheritedRegularSlots.reserved A

private def number (f:Side) (key:ℕ):ℕ:=
  if h:∃a,blankRow f a=key then h.choose.2 else 0

private theorem at_number (a:RegularAddress f×ℕ):number f (blankRow f a)=a.2:=by
  have h:∃z,blankRow f z=blankRow f a:=⟨a,rfl⟩
  rw [number,dif_pos h]
  exact congrArg Prod.snd ((blankRow f).injective h.choose_spec)

private def used (m:Leaf A):ℕ:=
  match m.turn with
  | .logKey k=>number f k
  | .gasKey _=>0

variable (run:Run G) (d:I→ℕ) (x:I→Site f)
def address (i:I):RegularAddress f where
  site:=x i
  support:=(run.family.localSection (d i)).footprint (x i)
  anchor:=Finset.mem_image.mpr ⟨0,(run.makes.sections (d i)).anchored,by simp⟩

variable (old:Team A)
private def slotTag (i:I):ℕ:=old.own.sup used+1+((Fintype.equivFin I) i).val
def key (i:I):ℕ:=blankRow f (address run d x i,slotTag old i)

theorem separated:Injective (key run d x old):=by
  intro i j eq
  have same:=congrArg Prod.snd ((blankRow f).injective eq)
  apply (Fintype.equivFin I).injective
  apply Fin.ext
  exact Nat.add_left_cancel (show old.own.sup used+1+((Fintype.equivFin I) i).val=
     old.own.sup used+1+((Fintype.equivFin I) j).val from same)

variable (shelf:Shelf A) (y:∀i,run.family.label (d i)) (phase:I→ℂ →L[ℝ] ℝ)
def issued:Submitted run A I where
  grade:=d
  site:=x
  label:=y
  phase:=phase
  key:=key run d x old
  separated:=separated run d x old
  covers i:=by unfold key;rw [(shelf (address run d x i) (slotTag old i)).1];exact Subset.rfl
  vacant i:=(shelf (address run d x i) (slotTag old i)).2

theorem fresh (m:Leaf A) (hm:m∈old.own) (i:I):
    m.turn≠(row (issued run d x old shelf y phase) i).turn:=by
  intro eq
  change m.turn=Wing.logKey (key run d x old i) at eq
  have bound:=Finset.le_sup (f:=used) hm
  have seen:used m=slotTag old i:=by
    unfold used
    rw [eq]
    exact at_number (address run d x i,slotTag old i)
  rw [seen] at bound
  unfold slotTag at bound
  omega

end YM.Integration.WilsonCoherentMayerSlots
