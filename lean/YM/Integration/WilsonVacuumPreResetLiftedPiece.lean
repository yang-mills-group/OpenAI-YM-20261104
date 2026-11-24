import YM.Integration.WilsonVacuumPreResetPeriodIndex

/-! Lifted path length truncation of the actual independent period packet.
The two-leg packet retains its native clover subtraction and zero affine
Hessian. Both kinds use the very same full original ledger addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetLiftedPiece
open Function Finset Lattice RG Marker Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Render PhysicalNext PhysicalNext.Repeat IterationFour.Vacuum
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup
open Extra.Iteration Push.AbsoluteSums
open scoped Classical Topology BigOperators
variable {G:Gauge}{n:Side}

def frame (n:Side)(a:PrismA G)(keep:ℕ→Prop):Frame G n:=
  match a with
  | ⟨_,0,_,P⟩=>Frame.makeRose P n 1 keep
  | ⟨_,_+1,_,P⟩=>rack n P 1 keep

def issue (n:Side)(a:PrismA G)(keep:ℕ→Prop):Payload G n:=
  let F:=frame n a keep
  ⟨F.shelf ∘ numbering (Cycle n),F.table ∘ numbering (Cycle n)⟩

def rebate (σ:ℝ)(D:ℕ):ℝ:=(Real.exp ((σ/4)*D))⁻¹

theorem whole (n:Side)(a:PrismA G)(B:BudgetPoint)(σ C:ℝ):
    issue n a Frame.full=(FundedCorrectedPeriod.piece n B σ C a).packet:=by
  rcases a with ⟨d,r,h,P⟩
  cases r <;> rfl

theorem labels (n:Side)(a:PrismA G)(keep:ℕ→Prop):
    (issue n a keep).labels=(issue n a Frame.full).labels:=by
  rcases a with ⟨d,r,h,P⟩
  cases r <;> rfl

theorem fields (n:Side)(a:PrismA G)(keep:ℕ→Prop)(i:ℕ):
    (issue n a keep).action i=(if keep ((numbering (Cycle n)) i).2 then (issue n a Frame.full).action i else 0):=by
  rcases a with ⟨d,r,h,P⟩
  cases r <;> funext U <;> by_cases active:keep ((numbering (Cycle n)) i).2 <;>
    simp [issue,frame,Frame.table,rack,Frame.makeRose,recipe,Frame.full,active]

theorem long (simple:G.Simple)(hn:20<n.val)(B:BudgetPoint){σ C:ℝ}(hs:0<σ)
    (reach:B.supportExponent/B.B≤σ/4)(blocks:2≤B.B)(a:PrismA G)
    (h:Commission a.cells σ C a.grade)(D:ℕ):
    (issue n a (postW a.cells D)).Invoice B (rebate σ D*FundedCorrectedPeriod.credit B σ C a):=by
  let A:=Pane.pale n G
  have hm (s:Signed)(b:Site n):A.Moves s b:=((Pane.whey n G B).moves s b).some
  rcases a with ⟨d,r,hr,P⟩
  cases r with
  | zero=>
    let F:=Frame.makeRose P n 1 (postW P D)
    have fair:=Frame.rose_era P n 1 (postW P D) h.hue B
    have zero:=Frame.rose_stars P n 1 simple (postW P D) h.hue B hn
    have reg:=Frame.authentic A fair zero simple (by omega)
    have price:=Frame.rose_far P n 1 (A:=A) hs reach blocks h.hue h.toll D
    refine ⟨reg.smooth,reg.at_flat,reg.vanish,?_,?_⟩
    · intro s b
      let q:=Frame.move F A (hm s b)
      exact ⟨q.ep,fun i=>⟨q.reg_site i,q.reg_support i,q.valuesE i⟩⟩
    · change (F.coffee A).EBound B _
      convert price using 1
      change rebate σ D*(Frame.cost B*(Frame.roseCharge 1 σ G B*C))=_
      unfold rebate
      ring
  | succ r=>
    let F:=rack n P 1 (postW P D)
    have fair:=bandFits (F:=P) (n:=n) (a:=1) (h:=postW P D) h.hue B
    have zero:=bandNull (n:=n) (F:=P) (a:=1) (h:=postW P D) (by omega)
    have reg:=Frame.authentic A fair zero simple (by omega)
    have price:=remaining P 1 A h.hue h.toll hs reach D
    refine ⟨reg.smooth,reg.at_flat,reg.vanish,?_,?_⟩
    · intro s b
      let q:=Frame.move F A (hm s b)
      exact ⟨q.ep,fun i=>⟨q.reg_site i,q.reg_support i,q.valuesE i⟩⟩
    · change (F.coffee A).EBound B _
      convert price using 1
      simp only [FundedCorrectedPeriod.credit,Nat.succ_ne_zero,if_false,rebate]
      ring

end YM.Integration.WilsonVacuumPreResetLiftedPiece
