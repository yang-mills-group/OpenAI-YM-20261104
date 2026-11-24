import YM.Integration.WilsonIndependentExactPlate
import YM.RegulatorIR.Calibration.Upright
import YM.FVAAlt2.Rocket.Orbit

/-! Original unmarked licenses on the exact auxiliary torus, with the native bare-reference notebook. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentLicensedCircuit
open Lattice RG Precision Source XSpace WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.AuxPlates
open RegulatorIR RegulatorIR.Ledger RegulatorIR.Oracle
open WilsonIndependentEvenPassport (power count)
open WilsonIndependentExactPlate
open scoped Classical BigOperators
variable (V:XSpace.Run)(a j:ℕ)(ha:0<a)(hj:4≤j)
private lemma patch_eq {p q:Patch}(l:p.L=q.L)(k:p.J=q.J):p=q:=by cases p;cases q;congr

def stages := ({j,j+1}:Finset ℕ)
def stamp (z d:ℕ)(h:0<z)(k:4≤d):Patch:=
  ⟨power V z,d,k,V.large.trans (Nat.le_self_pow h.ne' _),V.odd.pow⟩
def patches := insert (stamp V a j ha hj)
  (Finset.univ.image fun r:Fin a => stamp V (a+r.val) (j+1) (Nat.add_pos_left ha _) (Nat.le_succ_of_le hj))

theorem page (p:Page (M V a)) : (S V a ha j hj).J p∈stages j:=by
  change (if p.downW=0 then j+1 else j)∈stages j
  split_ifs <;> simp [stages]

theorem patch (f:Flap (M V a)) : (S V a ha j hj).pactP f∈patches V a j ha hj:=by
  rw [patches,Finset.mem_insert]
  by_cases z:f.offset=0
  · right
    apply Finset.mem_image.mpr
    refine ⟨⟨f.volW.val%a,Nat.mod_lt _ ha⟩,Finset.mem_univ _,?_⟩
    apply patch_eq
    · simp [stamp,Circuit.pactP,S,WilsonIndependentExactPlate.sizeL,z,residue]
    · simp [stamp,Circuit.pactP,S,stage,Flap.prev,z]
  · left
    apply patch_eq
    · simp [stamp,Circuit.pactP,S,WilsonIndependentExactPlate.sizeL,z]
    · simp [stamp,Circuit.pactP,S,stage,Flap.prev,z]

theorem lengths (f:Flap (M V a)): (power V a).val≤((S V a ha j hj).sizeL f).val:=by
  change V.ratio^a≤V.ratio^(if f.offset=0 then _ else _)
  split_ifs <;> first | exact le_rfl | exact Nat.pow_le_pow_right (by have:=V.large;omega) (Nat.le_add_right _ _)

include ha in
theorem ends (i:Requests a) :
    (n V a (Page.finallyW (M V a) i)).val ≤ V.finalSide.side.val*V.ratio^a:=by
  have hi : (0 : ℕ) < (i : ℕ) / a :=Nat.div_pos i.property ha
  have hc:0<M V a i:= Nat.add_pos_right _ hi
  change V.finalSide.side.val*V.ratio^(exp V a (Page.finallyW _ i))≤_
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_right (by have:=V.large;omega)
  change outer V a i+a*(M V a i-M V a i)+(if M V a i=0 then residue a i else 0)≤_
  simp only [Nat.sub_self,Nat.mul_zero,add_zero,hc.ne',if_false]
  exact (Nat.mod_lt _ ha).le

variable {G:Gauge}{H:Hol G}(R:Master H)(chart:ChartRatio G)(K:KernelChoices)
variable {e h k extra:ℕ}(B:WilsonIndependentEvenPassport.Menu R chart K V e h k j extra)

theorem actual (hj:4≤j)(i:Requests B.a) :
    let C:=S V B.a B.positive j hj
    let r:Fin B.a:=⟨i.val%B.a,Nat.mod_lt _ B.positive⟩
    ∃ (A:Levels G)(s:ℕ),A.clock.kernel=K ∧
      (∀ p:Page (M V B.a),p.bindW=i→A.clock.J (s+(M V B.a i-p.downW))=C.J p) ∧
      (∀ f:Flap (M V B.a),f.volW=i→∀ period:ℕ,
        (A.clock.op (s+(M V B.a i-(f.offset+1))) period).patch=C.pactP f ∧
        (A.clock.op (s+(M V B.a i-(f.offset+1))) period).kernel=(C.rail K f).kernel) ∧
      (∀ m:ℕ,m≤M V B.a i→ extendedY (B.price r) A.S (s+M V B.a i) (s+m)=B.price r) ∧
      Ally R A chart (extendedY (B.price r) A.S (s+M V B.a i)) e s h k := by
  intro C r
  obtain ⟨A,s,hK,walk,blocks,price,ticket⟩:=WilsonIndependentEvenPassport.plate R chart K V e h k j B i.val
  have hi : (0 : ℕ) < (i : ℕ) / B.a :=Nat.div_pos i.property B.positive
  have hcount:0<M V B.a i:=Nat.add_pos_right _ hi
  have pages (p:Page (M V B.a))(hp:p.bindW=i) :
      A.clock.J (s+(M V B.a i-p.downW))=C.J p :=by
    have good:M V B.a i≥p.downW:=hp ▸ p.good
    rw [walk (M V B.a i-p.downW) (Nat.sub_le _ _)]
    change (if _≤M V B.a i-1 then j else j+1)=(if p.downW=0 then j+1 else j)
    split_ifs <;> omega
  refine ⟨A,s,hK,pages,?_,price,ticket⟩
  intro f fi period
  have fit : f.offset<M V B.a i:=fi ▸ f.ok
  have coarse : M V B.a i-(f.offset+1)<M V B.a i:=by omega
  have succ : s+(M V B.a i-(f.offset+1))+1=s+(M V B.a i-f.offset):= by omega
  refine ⟨patch_eq ?_ ?_,hK⟩
  · change A.S.block _=WilsonIndependentExactPlate.sizeL _ _ _
    rw [blocks _ coarse]
    dsimp only [WilsonIndependentExactPlate.sizeL,residue]
    rw [fi]
    change (if M V B.a i-(f.offset+1)<M V B.a i-1 then _ else _)=power V (if f.offset=0 then _ else _)
    split_ifs <;> first | rfl | omega
  · change A.clock.J (s+_+1)=C.J f.prev
    rw [succ]
    exact pages f.prev fi

variable (Y:Program K)(branches:∀ p:Patch,p.Branches K G)(col:G.ColorIndex)(p:ℕ)
theorem notebook :
    let C:=S V a ha j hj
    ∃ F:Calibration.Tent (M V a), Calibration.Notebook C Y G branches col
      (RegulatorIR.FVAAlt2.Rocket.native (M V a)) F p ∧
      ∀ i:Requests a,Calibration.sheet F (Page.opening _ i)=Clocks.flat :=by
  intro C
  obtain ⟨F,ok⟩:=Calibration.tomorrows C Y G branches col (RegulatorIR.FVAAlt2.Rocket.native _) p
  refine ⟨F,ok,fun i=>?_⟩
  change (F (Page.opening _ i)).scale=_
  rw [show F (Page.opening _ i)=Calibration.dawn from ok.reference i]
  exact RegulatorIR.FVAAlt2.Rocket.still

end YM.Integration.WilsonIndependentLicensedCircuit
