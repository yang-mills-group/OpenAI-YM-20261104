import YM.Integration.WilsonIndependentPublicFreeAppointment
import YM.Integration.WilsonOriginalPublicNodalHelperCircuit

/-! The public helper's actual length roster and its marked Mer faculty on the very same optical boards. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingHelperPlate
open Lattice RG Source Labels PertExtension XSpace Precision WilsonCoeffUV WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.AuxPlates RegulatorIR.Ledger WilsonIndependentExactPlate
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Atlas RegulatorIR.Uniform
open WilsonIndependentEvenPassport (power)
open WilsonOriginalPublicNodalHelperShape (length)
open WilsonIndependentCutJoinPassport (All)
open scoped BigOperators Classical

variable {G:Gauge}{H:Hol G}(P:Master H)(chart:ChartRatio G)(K:KernelChoices)(V:XSpace.Run)
    (e h k j extra:ℕ)(B:WilsonIndependentEvenPassport.Menu P chart K V e h k j extra)
    (hj:4 ≤ j){X:Type}(E r:X→ℕ)(res:∀x,r x<B.a)(enough:∀x,0<length E r B.a x)
local notation "schedule" => length E r B.a
local notation "C" => WilsonOriginalPublicNodalHelperCircuit.circuit V E r B.a j B.positive hj

private theorem patchEq {p q:Patch}(l:p.L=q.L)(j:p.J=q.J):p=q:=by cases p;cases q;congr

include enough in
theorem original (grant:WilsonIndependentCutJoinPlate.Approved P chart K V e h k j extra B):
    ∃(land:X→Levels G)(first:X→ℕ),
      (∀x,WilsonIndependentPublicFreeTrain.Matches (land x) (C) K (first x) x) ∧
      (∀f:Flap schedule,∀per:ℕ,((land f.volW).clock.op (first f.volW+(schedule f.volW-(f.offset+1))) per).patch=(C).pactP f) ∧
      (∀x m,m ≤ schedule x→extendedY (B.price ⟨r x,res x⟩) (land x).S (first x+schedule x) (first x+m)=B.price ⟨r x,res x⟩) ∧
      ∀x,All P (land x) chart (extendedY (B.price ⟨r x,res x⟩) (land x).S (first x+schedule x)) e (first x) h k:=by
  classical
  choose A s kin short long walk fund using fun x:X=>grant ⟨r x,res x⟩ (schedule x) (schedule x-1) (Nat.sub_le ..)
  have pages (x:X)(p:Page schedule)(hp:p.bindW=x):
      (A x).clock.J (s x+(schedule x-p.downW))=(C).J p:=by
    have fit:p.downW ≤ schedule x:=hp ▸ p.good
    have pos:=enough x
    rw [walk x (schedule x-p.downW) (Nat.sub_le _ _)]
    change (if _ ≤ schedule x-1 then j else j+1)=(if p.downW=0 then j+1 else j)
    split_ifs <;> omega
  have rails (f:Flap schedule)(per:ℕ):
      ((A f.volW).clock.op (s f.volW+(schedule f.volW-(f.offset+1))) per).patch=(C).pactP f:=by
    let x:=f.volW
    let n:=schedule x
    have ok:f.offset<n:=f.ok
    have blocks (m:ℕ)(hm:m<n):
        (A x).S.block (s x+m)=if m<n-1 then power V B.a else power V (B.a+r x):=by
      rw [←(A x).fits.sameFactor,Nat.add_assoc,walk x (m+1) hm]
      split_ifs <;> first | exact short x | exact long x | omega
    have lower:n-(f.offset+1)<n:=by omega
    have step:s x+(n-(f.offset+1))+1=s x+(n-f.offset):=by omega
    apply patchEq
    · change (A x).S.block (s x+(n-(f.offset+1)))=power V (if f.offset=0 then B.a+r x else B.a)
      rw [blocks _ lower];split_ifs <;> first | rfl | omega
    · change (A x).clock.J (s x+(n-(f.offset+1))+1)=(C).J f.prev
      rw [step];exact pages x f.prev rfl
  exact ⟨A,s,fun x=>⟨kin x,pages x,fun f hf=>hf ▸ rails f 0⟩,rails,
    fun x m hm=>y_plate _ _ (Nat.add_le_add_left hm _),fund⟩
end YM.Integration.WilsonSeparatedPrefixMovingHelperPlate
end
