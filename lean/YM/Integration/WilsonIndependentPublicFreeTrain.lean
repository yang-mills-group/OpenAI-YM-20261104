import YM.Integration.WilsonIndependentCutJoinPlate

/-! Identify the actual free tables and block predictors on the public notebook. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPublicFreeTrain
open Lattice RG WilsonCoeffUV RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle Next.Free
open scoped Matrix
variable {G:Gauge}{K:KernelChoices}{Ω:Type}{M:Ω→ℕ}{n:Page M→Side}
variable {i j i' j':ℕ}
private theorem heads (q:i=j) : HEq (Train.top i) (Train.top j) :=by subst j; rfl
private theorem legs {L L':Side}
    (l:Odd L.val)(t:3 ≤ L.val)(p:4 ≤ i)(b:j ≤ i)(h:i ≤ j+1)
    (l':Odd L'.val)(t':3 ≤ L'.val)(p':4 ≤ i')(b':j' ≤ i')(h':i' ≤ j'+1)
    (X:Train i)(Y:Train i')(q:i=i')(v:j=j')(g:L=L')(x:HEq X Y) :
    HEq (⟨L,l,t,p,b,h,X⟩:Flight i j) (⟨L',l',t',p',b',h',Y⟩:Flight i' j') :=by subst_vars;rfl
private theorem ends (q:i=i')(v:j=j')(P:Flight i j)(Q:Flight i' j')(x:HEq P Q) :
    HEq P.land Q.land:=by subst_vars;rfl

variable (A:Levels G)(C:Circuit M n)(K:KernelChoices)(s:ℕ)(w:Ω)
/-- The data already issued by the actual public calendar, read at each signed face. -/
structure Matches : Prop where
    kinetic:A.clock.kernel=K
    grades (p:Page M):p.bindW=w→A.clock.J (s+(M w-p.downW))=C.J p
    patches (f:Flap M):f.volW=w→(A.clock.op (s+(M w-(f.offset+1))) 0).patch=C.pactP f

variable {A C K s w} (R:Matches A C K s w)
include R
private theorem flap (f:Flap M)(h:f.volW=w)
    (input:HEq (location A (s+M w) (s+(M w-f.offset))) (C.training f.prev)) :
    HEq (destination A (s+M w) (s+(M w-(f.offset+1)))) (C.crew f) :=by
  have bounded:f.offset<M w:=h ▸ f.ok
  have ht:s+(M w-(f.offset+1))+1=s+(M w-f.offset):=by omega
  apply legs
  · rw [ht];exact R.grades f.prev h
  · exact R.grades f.next h
  · exact congrArg Patch.L (R.patches f h)
  · rw [ht];exact input

theorem training (p:Page M)(hp:p.bindW=w) :
    HEq (location A (s+M w) (s+(M w-p.downW))) (C.training p) :=by
  rcases p with ⟨w',d,hd⟩
  change w'=w at hp
  subst w'
  induction d with
  | zero=> rw [Nat.sub_zero,loc_top];exact heads (R.grades (Page.opening M w) rfl)
  | succ d ih=>
    let f:Flap M:=⟨w,d,hd⟩
    have hz:s+(M w-(d+1))<s+M w:=by omega
    change HEq (location A (s+M w) (s+(M w-(d+1)))) (C.training f.next)
    rw [loc_land A _ _ hz,C.crest]
    apply ends
    · rw [show s+(M w-(d+1))+1=s+(M w-d) by omega]
      exact R.grades f.prev rfl
    · exact R.grades f.next rfl
    · exact flap R f rfl (ih (by omega))

omit R in
private theorem pink_eq (k k':ℝ)(q:k=k')(P:Train i)(Q:Train j)(v:i=j)(x:HEq P Q) :
    pink k P=pink k' Q:=by subst_vars;rfl

theorem diagonal (Y:Program K)(p:Page M)(hp:p.bindW=w) :
    (C.tables Y p).diagonal=freeForms A (s+M w) (s+(M w-p.downW)) :=by
  rw [(C.honored Y p).flight_s.diag]
  exact (pink_eq _ _ (congrArg KernelChoices.penalty R.kinetic) _ _ (R.grades p hp) (training R p hp)).symm

theorem action (Y:Program K)(p:Page M)(hp:p.bindW=w)(board:Side) :
    Precision.K ((C.tables Y p).metric.acts board)=
      Precision.K ((freeForms A (s+M w) (s+(M w-p.downW))).acts board) :=by
  rw [←diagonal R Y p hp]
  unfold Precision.K
  rw [Matrix.mul_assoc,((C.honored Y p).card.floorP board).same,Matrix.mul_assoc]

omit R in
private theorem predictions (k k':ℝ)(v:k=k')(P:Flight i j)(Q:Flight i' j')
    (a:i=i')(b:j=j')(x:HEq P Q):HEq (P.duo k).A0 (Q.duo k').A0:=by subst_vars;rfl

theorem predictor (Y:Program K)(f:Flap M)(hf:f.volW=w) :
    HEq (predictionA A (s+M w) (s+(M w-(f.offset+1)))) (C.tells Y f) :=by
  have good:f.offset<M w:=hf ▸ f.ok
  apply predictions _ _ (congrArg KernelChoices.penalty R.kinetic)
  · rw [show s+(M w-(f.offset+1))+1=s+(M w-f.offset) by omega];exact R.grades f.prev hf
  · exact R.grades f.next hf
  · exact flap R f hf (training R f.prev hf)

end YM.Integration.WilsonIndependentPublicFreeTrain
