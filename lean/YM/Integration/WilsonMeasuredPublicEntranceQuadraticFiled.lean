import YM.Integration.WilsonMeasuredPublicEntranceQuadraticTransfer
import YM.Integration.WilsonMeasuredPublicEntranceAbsoluteColor

/-! Restrict the originally measured finite horizon to its fourth engineering sector.
The second and third moments used for contraction are evaluations of the same tested
field map. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceQuadraticFiled
open Function Climb Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Stab Next.Rank OJoint
open WilsonMeasuredPublicEntranceCommonColor WilsonMeasuredPublicEntranceQuadraticGrid
open WilsonMeasuredPublicEntranceQuadraticSpan WilsonMeasuredPublicEntranceQuadraticProducts
open WilsonMeasuredPublicEntranceMarkedQuadratics
open scoped Classical BigOperators
variable {G:Gauge}{C:Family G}{d:ℕ}

def seat (hd:4≤d):HFields G 4→ₗ[ℂ] HFields G d:=Submodule.inclusion (chain hd)
theorem folded (hd:4≤d)(m:Plane ℝ):seat hd (marked G le_rfl m)=marked G hd m:=by
  change seat hd (∑i,∑j,m i j • tile le_rfl i j)=∑i,∑j,m i j • tile hd i j
  simp only [map_sum]
  rfl

def reader (hd:4≤d)(T:FieldEnd G d)
    (resident:∀w:HFields G 4,(T (seat hd w)).val∈shellSector G 4):FieldEnd G 4:=
  (Submodule.subtype (shellSector G d) ∘ₗ T ∘ₗ seat hd).codRestrict _ resident

theorem placed {A:Module.End ℂ ((Bel C.book).Field d)}(native:WilsonPhysicalPositionAdmissible.Native C A)
    (hd:4≤d):let T:=carried C A
      T (leaf G d)=leaf G d ∧ (∀p:HFields G 4,(T (seat hd p)).val∈shellSector G 4) ∧
      ∀p:HFields G d,T (negating p)=negating (T p):=by
  let U:=fields C.labels d
  let T:=carried C A
  have ev(p:HFields G d):T p=U (A (U.symm p)):=rfl
  have one:U (WilsonPhysicalPositionAdmissible.unit C d)=leaf G d:=Subtype.ext (unit_address ..)
  refine ⟨?_,?_,?_⟩
  · change T (leaf G d)=leaf G d
    rw [←one,ev,U.symm_apply_apply,native.neutral]
  · intro p
    let v:=(fields C.labels 4).symm p
    have registered:U ((scheme C.labels).rise hd v)=seat hd p:=by
      apply Subtype.ext
      change address C.labels d ((scheme C.labels).rise hd v)=p.val
      rw [address_rise]
      exact congrArg Subtype.val ((fields C.labels 4).apply_symm_apply p)
    obtain ⟨z,hz⟩:=native.lower hd v
    change (T (seat hd p)).val∈_
    rw [←registered,ev,U.symm_apply_apply,←hz]
    change address C.labels d ((scheme C.labels).rise hd z)∈_
    rw [address_rise]
    exact address_in C.labels 4 z
  intro p
  have bar(v):U (WilsonPhysicalPositionAdmissible.real C d v)=negating (U v):=
    Subtype.ext (address_star ..)
  have eq:U (WilsonPhysicalPositionAdmissible.real C d (U.symm p))=negating p:=
    (bar _).trans (congrArg negating (U.apply_symm_apply p))
  change T (negating p)=negating (T p)
  rw [ev,←eq,U.symm_apply_apply,native.conjugate,ev,bar]

theorem original (simple:G.Simple)(hd:4≤d)(T:FieldEnd G d)(unit:T (leaf G d)=leaf G d)
    (resident:∀w:HFields G 4,(T (seat hd w)).val∈shellSector G 4)
    (all:∀{n:ℕ}(v:Fin n→HFields G d){x:Points n},x∈conf n→
      Wick.moment G x (fun i=>(T (v i)).val)=Wick.moment G x (fun i=>(v i).val))
    (a b:Axis)(U V:Plane ℝ)(sU:U.transpose=U)(sV:V.transpose=V)
    (fixedU:T (marked G hd U)=marked G hd U)(fixedV:T (marked G hd V)=marked G hd V):
    T (marked G hd (product (lift (exterior a b)) U V))=marked G hd (product (lift (exterior a b)) U V):=by
  let R:=reader hd T resident
  have hu:R (leaf G 4)=leaf G 4:=Subtype.ext (congrArg (fun v:HFields G d=>v.val) unit)
  have held (Z:Plane ℝ)(invoiced:T (marked G hd Z)=marked G hd Z):
      R (marked G le_rfl Z)=marked G le_rfl Z:=by
    apply Subtype.ext
    change (T (seat hd (marked G le_rfl Z))).val=(seat hd (marked G le_rfl Z)).val
    rw [folded,invoiced]
  have pair (x y:E4)(apart:x≠y)(l r:HFields G 4):
      bond G x y (R l).val (R r).val=bond G x y l.val r.val:=by
    let v:Fin 2→HFields G d:=Fin.cons (seat hd l) (fun _=>seat hd r)
    rw [bond_eval,bond_eval]
    convert all v (pair_ok apart) using 2 <;> ext1 i <;> fin_cases i <;> rfl
  have tri (x y z:E4)(hx:x≠y)(hy:x≠z)(hz:y≠z)(l r w:HFields G 4):
      triangle G x y z (R l).val (R r).val (R w).val=triangle G x y z l.val r.val w.val:=by
    let v:Fin 3→HFields G d:=Fin.cons (seat hd l) (Fin.cons (seat hd r) (fun _=>seat hd w))
    rw [tri_eval,tri_eval]
    convert all v (tri_ok hx hy hz) using 2 <;> ext1 i <;> fin_cases i <;> rfl
  have done:=WilsonMeasuredPublicEntranceQuadraticTransfer.original simple R hu a b U V sU sV
    (held U fixedU) (held V fixedV) pair tri
  apply Subtype.ext
  have h:=congrArg (fun z:HFields G 4=>z.val) done
  change (T (seat hd (marked G le_rfl _))).val=(seat hd (marked G le_rfl _)).val at h
  simpa only [folded] using h
end YM.Integration.WilsonMeasuredPublicEntranceQuadraticFiled

