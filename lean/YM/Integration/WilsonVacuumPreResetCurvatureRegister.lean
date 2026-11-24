import YM.Integration.WilsonVacuumPreResetCurvaturePrice
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Urb

/-! Common numbering of the actual quadratic, cubic and quartic source,
including all its original placements and spatial symmetries. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetCurvatureRegister
open Lattice RG Wilson PhysicalNext PhysicalNext.Repeat AnalyticBridge VerifiedReset
open Push Push.AbsoluteSums Collection Quotes Song Filter
open WilsonVacuumPreResetCurvatureField
open Push.AbsoluteSums.Animals ConnectedActivityE6 Next.Scheduling Extra.Iteration Meadow WilsonStartup Geo
open scoped Classical Topology
variable {G:Gauge}{n:Side}

abbrev Tags := Low ⊕ ℕ ⊕ ℕ

def enter (x:Seat n):Tags→Rows n:=Sum.elim (fun j=>.inl (x,j))
  (Sum.elim (fun j=>.inr (.inl (x,j))) (fun j=>.inr (.inr (x,j))))

def seat : Rows n→Seat n:=Sum.elim Prod.fst (Sum.elim Prod.fst Prod.fst)

def tag : Rows n→Tags:= Sum.elim (Sum.inl ∘ Prod.snd)
  (Sum.elim (fun j=>.inr (.inl j.2)) (fun j=>.inr (.inr j.2)))

def raw : Tags→Meadow.Rags:=Sum.elim Sum.inl (Sum.elim (fun j=>.inr (.inl j)) (fun j=>.inr (.inr (.inl j))))

theorem entered (x:Seat n)(k:Tags):seat (enter x k)=x ∧ tag (enter x k)=k:=by
  rcases k with k|k|k <;> exact ⟨rfl,rfl⟩

theorem restore (j:Rows n):enter (seat j) (tag j)=j:=by
  rcases j with ⟨x,k⟩|⟨x,k⟩|⟨x,k⟩ <;> rfl

theorem named (j:Rows n):slot j=Meadow.legs (seat j) (raw (tag j)):=by
  rcases j with j|j|j <;> rfl

theorem debit (j:Rows n)(K:PathData G):Meadow.melody K (raw (tag j))=arc K (slot j):=by
  rcases j with j|j|j <;> rfl

def number (n:Side):ℕ≃Rows n:=numbering _

def next (s:Signed)(b:Site n):Equiv.Perm (Rows n):=
  Equiv.sumCongr (whirl (ι:=Low) s b) (Equiv.sumCongr (whirl (ι:=ℕ) s b) (whirl (ι:=ℕ) s b))

def walk (s:Signed)(b:Site n):Equiv.Perm ℕ:=((number n).trans (next s b)).trans (number n).symm

theorem atWalk (s:Signed)(b:Site n)(i:ℕ):number n (walk s b i)=next s b (number n i):=by
  exact (number n).apply_symm_apply _

theorem sameTag (s:Signed)(b:Site n)(j:Rows n):tag (next s b j)=tag j:=by
  rcases j with j|j|j <;> rfl

theorem moves (B:BudgetPoint)(K:PathData G)(c:Clip)(γ β:ℝ)(s:Signed)(b:Site n)(j:Rows n):
    (strings K B (slot (next s b j))).site=affine s b (strings K B (slot j)).site ∧
    (strings K B (slot (next s b j))).support=(strings K B (slot j)).support.image (affine s b) ∧
    source K c γ β (next s b j)=source K c γ β j ∘ pull s b:=by
  rcases j with ⟨x,k⟩|⟨x,k⟩|⟨x,k⟩
  all_goals refine ⟨rfl,x.spread_move _ _ _,?_⟩
  all_goals funext U
  · change (factor*γ)*(k.mark K c*k.plain K 0 ((Seat.move s b x).view U))=_
    rw [x.view_move];rfl
  · change (factor*β)*(K.cubic k).unmasked ((Seat.move s b x).view U) 0=_
    rw [x.view_move];rfl
  · change (factor*β)*(K.quartic k).unmasked ((Seat.move s b x).view U) 0=_
    rw [x.view_move];rfl

theorem invoice (B:BudgetPoint)(K:PathData G)(c:Clip){σ C Λ:ℝ}(h:K.Bounds c σ C Λ)
    (clip:Decent c B)(reach:preExponent B/B.B≤σ/4)(γ β:ℝ):
    Meadow.Budget B (fun i=>strings K B (slot (number n i))) (source K c γ β ∘ number n)
      (WilsonVacuumPreResetCurvaturePrice.cost (G:=G) B c σ C γ β):=by
  obtain ⟨f,due,rows⟩:=WilsonVacuumPreResetCurvaturePrice.long (n:=n) B K c h clip reach γ β 0
  refine ⟨f ∘ number n,fun x=>?_,fun i=>rows (number n i)⟩
  simpa using Cost.equiv (number n) (due x)

end YM.Integration.WilsonVacuumPreResetCurvatureRegister
