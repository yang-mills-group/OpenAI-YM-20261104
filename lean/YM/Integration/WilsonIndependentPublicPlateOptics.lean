import YM.Integration.WilsonIndependentLicensedCircuit

/-! Physical and grouped optical ages on the same actual unmarked Levels. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentPublicPlateOptics
open Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonIndependentExactPlate
open WilsonIndependentEvenPassport (count old young)
variable {G:Gauge}(V:XSpace.Run)(a:ℕ)(ha:0<a)(j:ℕ)(hj:4≤j)
variable (i:Requests a)(A:Levels G)(s:ℕ)
local notation "C"=> S V a ha j hj
local notation "N"=> M V a i

theorem original
    (book:∀ f:Flap (M V a),f.volW=i→(A.clock.op (s+(N-(f.offset+1))) 0).patch=(C).pactP f) :
    A.S.scale (s+N)-A.S.scale (s+old V a i.val)= -Real.log (V.step i.val).spacing := by
  have paid : ∀ p:Page (M V a),p.bindW=i→
      A.S.scale (s+N)=A.S.scale (s+(N-p.downW))+Real.log ((C).l p):=by
    apply Page.proves
    · intro w same
      change w=i at same
      subst w
      rw [(units V a ha j hj i).1,Real.log_one,add_zero]
      rfl
    · intro f prev nxt
      have host:f.volW=i:=nxt
      have fit:f.offset<N:=host ▸ f.ok
      have shift : s+(N-(f.offset+1))+1=s+(N-f.offset):=by omega
      have block:A.S.block (s+(N-(f.offset+1)))=(C).sizeL f := congrArg Patch.L (book f host)
      have actual:=A.S.scale_succ (s+(N-(f.offset+1)))
      rw [shift,block] at actual
      have prevVal:=prev host
      change A.S.scale (s+N)=A.S.scale (s+(N-f.offset))+Real.log ((C).l f.prev) at prevVal
      change A.S.scale (s+N)=A.S.scale (s+(N-(f.offset+1)))+Real.log ((C).l f.next)
      have positive : (0:ℝ)<((C).sizeL f).val:=by exact_mod_cast ((C).sizeL f).pos
      rw [(C).width_s f,Real.log_mul ((C).l_p _).ne' positive.ne']
      linarith
  have priced:=paid (report V a i) rfl
  have age:N-(report V a i).downW=old V a i.val := by
    change old V a i.val + young a i.val - young a i.val = _
    exact Nat.add_sub_cancel _ _
  rw [age] at priced
  have scaled:=congrArg Real.log (units V a ha j hj i).2
  rw [Real.log_one,Real.log_mul (V.step i.val).positive.ne' ((C).l_p _).ne'] at scaled
  linarith

variable {H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices){e h k extra:ℕ}
    (B:WilsonIndependentEvenPassport.Menu R chart K V e h k j extra)
theorem on_plate (i:Requests B.a) :
    let circuit:= S V B.a B.positive j hj
    let n:=M V B.a i
    let r:Fin B.a:=⟨i.val%B.a,Nat.mod_lt _ B.positive⟩
    ∃ (A:Levels G)(s:ℕ), A.clock.kernel=K ∧
      (∀ f:Flap (M V B.a),f.volW=i→∀ period:ℕ,
        (A.clock.op (s+(n-(f.offset+1))) period).patch=circuit.pactP f) ∧
      A.S.scale (s+n)-A.S.scale (s+old V B.a i.val) = -Real.log (V.step i.val).spacing ∧
      (∀ m:ℕ,m≤n→ extendedY (B.price r) A.S (s+n) (s+m)=B.price r) ∧
      Ally R A chart (extendedY (B.price r) A.S (s+n)) e s h k :=by
  intro circuit n r
  obtain ⟨A,s,kernel,_,paid,price,ally⟩:=
    WilsonIndependentLicensedCircuit.actual V j R chart K B hj i
  let paid':=fun f hf period=>(paid f hf period).1
  exact ⟨A,s,kernel,paid',original V _ _ _ _ i A s (fun f hf=>paid' f hf 0),price,ally⟩

end YM.Integration.WilsonIndependentPublicPlateOptics
