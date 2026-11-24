import YM.Integration.WilsonIndependentTwoMomentPassport
import YM.Integration.WilsonIndependentPublicPlateOptics

/-! A shared unmarked gear at all lower moments on the exact before-length auxiliary calendar. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentTwoMomentPlate
open Lattice RG XSpace Precision Source WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonIndependentExactPlate
open WilsonIndependentTwoMomentPassport
open WilsonIndependentEvenPassport (count young old power)
open scoped Classical BigOperators
variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices)
    (V:XSpace.Run)(e h k j extra:ℕ)
abbrev Menu:=WilsonIndependentEvenPassport.Menu R chart K V e h k j extra
def Approved (B:Menu R chart K V e h k j extra) := ∀ (r:Fin B.a) (n c:ℕ),c≤n→
    ∃ (A:Levels G)(s:ℕ),A.clock.kernel=K ∧ A.clock.factor j=power V B.a ∧
      A.clock.factor (j+1)=power V (B.a+r.val) ∧ Walk A j c s n ∧
      Shared R A chart (extendedY (B.price r) A.S (s+n)) e s h k

theorem purchase (good:G.Simple)(valid:LocalRatio chart)(branches:∀ p:Patch,p.Branches K G)
    (q:h+3≤j)(late:5≤j) : ∃ B:Menu R chart K V e h k j extra,Approved R chart K V e h k j extra B := by
  obtain ⟨f,ok⟩:=funded good R chart valid K branches e h k j q late
  obtain ⟨a,ha,hf⟩:= WilsonIndependentGroupedInversionMesh.floor V (max f extra)
  have lo : f≤(power V a).val:= (Nat.le_max_left _ _).trans hf
  have z : 0<V.ratio:=by have:=V.large;omega
  have run (r:Fin a) :=ok (power V a) (power V (a+r.val)) lo
    (lo.trans (Nat.pow_le_pow_right z (Nat.le_add_right _ _)))
    V.odd.pow V.odd.pow (Nat.pow_le_pow_right z (Nat.le_add_right _ _))
  choose price shell license using run
  let C:=1+∑ r:Fin a,price r
  have bound (r:Fin a) : price r≤ C:=by
    have H:=Finset.single_le_sum (s:=Finset.univ) (f:=price) (fun t _=>(by linarith [shell t] : 0≤price t)) (Finset.mem_univ r)
    dsimp only [C]
    linarith
  let B:WilsonIndependentEvenPassport.Menu R chart K V e h k j extra:=
    ⟨a,ha,(Nat.le_max_right _ _).trans hf,C,price,fun r=>⟨shell r,bound r⟩,
      fun r n c hnc=>by
        obtain ⟨A,s,kin,one,two,walk,both⟩:=license r n c hnc
        exact ⟨A,s,kin,one,two,walk,admitted _ _ both⟩⟩
  exact ⟨B,license⟩

private lemma samePatch {p q:Patch}(l:p.L=q.L)(k:p.J=q.J):p=q:=by cases p;cases q;congr

variable (B:Menu R chart K V e h k j extra) (grant:Approved R chart K V e h k j extra B)
include grant in
theorem optics (hj:4≤j)(i:Requests B.a):
    let C:=S V B.a B.positive j hj
    let n:=M V B.a i
    let r:Fin B.a:=⟨i.val%B.a,Nat.mod_lt _ B.positive⟩
    ∃ (A:Levels G)(s:ℕ), A.clock.kernel=K ∧
      (∀ p:Page (M V B.a),p.bindW=i→A.clock.J (s+(n-p.downW))=C.J p) ∧
      (∀f:Flap (M V B.a),f.volW=i→∀ period:ℕ,(A.clock.op (s+(n-(f.offset+1))) period).patch=C.pactP f) ∧
      A.S.scale (s+n)-A.S.scale (s+old V B.a i.val)= -Real.log (V.step i.val).spacing ∧
      (∀m:ℕ,m≤n→extendedY (B.price r) A.S (s+n) (s+m)=B.price r) ∧
      Shared R A chart (extendedY (B.price r) A.S (s+n)) e s h k :=by
  intro C n r
  obtain ⟨A,s,hK,short,long,walk,both⟩:=grant r n (n-1) (Nat.sub_le ..)
  have blocks (m:ℕ)(hm:m<n) :
      A.S.block (s+m)=if m<n-1 then power V B.a else power V (B.a+r.val) := by
    rw [← A.fits.sameFactor,Nat.add_assoc,walk (m+1) hm]
    split_ifs <;> first | exact short | exact long | omega
  have hi : (0 : ℕ) < (i : ℕ) / B.a :=Nat.div_pos i.property B.positive
  have hcount:0<M V B.a i:=Nat.add_pos_right _ hi
  have pages (p:Page (M V B.a))(hp:p.bindW=i) :
      A.clock.J (s+(M V B.a i-p.downW))=C.J p :=by
    have good:M V B.a i≥p.downW:=hp ▸ p.good
    rw [walk (M V B.a i-p.downW) (Nat.sub_le _ _)]
    change (if _≤M V B.a i-1 then j else j+1)=(if p.downW=0 then j+1 else j)
    split_ifs <;> omega
  have rails (f:Flap (M V B.a))(fi:f.volW=i)(period:ℕ) :
      (A.clock.op (s+(M V B.a i-(f.offset+1))) period).patch=C.pactP f :=by
    have fit : f.offset<M V B.a i:=fi ▸ f.ok
    have coarse : M V B.a i-(f.offset+1)<M V B.a i:=by omega
    have succ : s+(M V B.a i-(f.offset+1))+1=s+(M V B.a i-f.offset):= by omega
    apply samePatch
    · change A.S.block _=WilsonIndependentExactPlate.sizeL _ _ _
      rw [blocks _ coarse]
      dsimp only [WilsonIndependentExactPlate.sizeL,residue]
      rw [fi]
      change (if M V B.a i-(f.offset+1)<M V B.a i-1 then _ else _)=power V (if f.offset=0 then _ else _)
      split_ifs <;> first | rfl | omega
    · change A.clock.J (s+_+1)=C.J f.prev
      rw [succ]
      exact pages f.prev fi
  exact ⟨A,s,hK,pages,rails,WilsonIndependentPublicPlateOptics.original V B.a B.positive j hj i A s (fun f hf=>rails f hf 0),
    fun m hm=>y_plate _ _ (Nat.add_le_add_left hm _),both⟩

end YM.Integration.WilsonIndependentTwoMomentPlate
