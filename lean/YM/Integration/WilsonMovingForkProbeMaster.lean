import YM.Integration.WilsonMovingForkPointPrescription
import YM.Integration.WilsonMovingForkCommonEar

/-! A single finite pool of directions at the two genuine home scales for
all reflected entries and the simultaneous ordinary measurements. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMovingForkProbeMaster
open Filter Set Function Lattice Wilson RG Source RG17 Extraction Table Spec Maxwell
open XSpace XSpace.Normalize FVA2 FVA2.Register PhysMS PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Theater
open WilsonPositionHomogeneousFrame WilsonMacroscopicRichTwoDatePivot
open WilsonMovingForkPositionIntegrals
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
  (J:ℝ→tower S)(Z:WilsonPrescription G){n h:ℕ}{P:Type}
local notation "C" => R.family

abbrev Seat (G:Gauge)(n h:ℕ)(P:Type):=Option (Fin n ⊕ (Dframe.Toon G h ⊕ P))

def grade (d:Fin n → ℕ) : Seat G n h P → ℕ
  | none=>0
  | some (.inl i)=>d i
  | some (.inr _)=>h

def home {α:Type*}(near far:α) : Seat G n h P → α
  | some (.inr (.inr _))=>far
  | _=>near

def dose (d:Fin n → ℕ)(v:∀i,Free (C) (d i))(a:P→Free (C) h):
    (i:Seat G n h P)→Free (C) (grade d i)
  | none=>0
  | some (.inl i)=>v i
  | some (.inr (.inl k))=>(WilsonMSDictionaryVector.basis (C) h) k
  | some (.inr (.inr j))=>a j

def cap (h:ℕ)(d:Fin n → ℕ):ℕ:=h+∑i,d i

def bound (d:Fin n → ℕ)(i:Seat G n h P):Fin (cap h d+1):=⟨grade d i,by
  have all(k):d k≤∑j,d j:=Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (Finset.mem_univ k)
  cases i with
  | none=>simp [grade,cap]
  | some j=>cases j with
    | inl k=>have upper:=all k;simp only [grade,cap];omega
    | inr k=>simp [grade,cap]⟩

def axis (d:Fin n → ℕ)(v:∀i,Free (C) (d i))(a:P→Free (C) h)(r t:ℝ)(i:Seat G n h P):S.Tag:=
  ⟨grade d i,homogeneous F J Z (home r t i) (grade d i) (dose d v a i)⟩

private def completeSeat (p:P):(Fin n ⊕ Fin 1) ↪ Seat G n h P where
  toFun
    | .inl i=>some (.inl i)
    | .inr _=>some (.inr (.inr p))
  inj' := by
    rintro (i|i) (j|j) eq
    · exact congrArg Sum.inl (Sum.inl.inj (Option.some.inj eq))
    · have bad:=Option.some.inj eq;cases bad
    · have bad:=Option.some.inj eq;cases bad
    · exact congrArg Sum.inr (Subsingleton.elim _ _)

def whole (p:P):Fin (n+1) ↪ Seat G n h P:=finSumFinEquiv.symm.toEmbedding.trans (completeSeat p)

def pair (k:Dframe.Toon G h)(p:P):Fin 2 ↪ Seat G n h P where
  toFun i:=Fin.cases (some (.inr (.inl k))) (fun _=>some (.inr (.inr p))) i
  inj' := by
    rintro i j eq;fin_cases i <;> fin_cases j <;> first | rfl | have bad:=Sum.inr.inj (Option.some.inj eq);cases bad

private theorem whole_left (p:P)(i:Fin n):whole (G:=G) (h:=h) p (Fin.castAdd 1 i)=some (.inl i):=by
  change completeSeat p (finSumFinEquiv.symm (Fin.castAdd 1 i))=_
  rw [finSumFinEquiv_symm_apply_castAdd];rfl
private theorem whole_right (p:P)(j:Fin 1):whole (G:=G) (h:=h) p (Fin.natAdd n j)=some (.inr (.inr p)):=by
  change completeSeat p (finSumFinEquiv.symm (Fin.natAdd n j))=_
  rw [finSumFinEquiv_symm_apply_natAdd];rfl

theorem whole_uses (d:Fin n → ℕ)(v:∀i,Free (C) (d i))(a:P→Free (C) h)(r t:ℝ)(p:P):
    (fun i=>axis F J Z d v a r t (whole p i))=nearTags F J d h Z (r:=r) (t:=t) v (a p):=by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro k
    rw [whole_left]
    simp [axis,grade,dose,home,nearTags,WilsonMovingForkPhysicalProducts.roster,WilsonMacroscopicRichReflectedRoster.physical,active];rfl
  · intro k
    rw [whole_right]
    simp [axis,grade,dose,home,nearTags,WilsonMovingForkPhysicalProducts.roster,WilsonMacroscopicRichReflectedRoster.physical,active];rfl

theorem gram_uses (d:Fin n → ℕ)(v:∀i,Free (C) (d i))(a:P→Free (C) h)(r t:ℝ)(k:Dframe.Toon G h)(p:P):
    (fun i=>axis F J Z d v a r t (pair k p i))=twoTags F J h Z r t (a p) k:=by
  funext i;fin_cases i <;> rfl

def subface {α β:Type*}[Fintype α](e:α ↪ β):Finset β:=Finset.univ.map e

def visit {α β:Type*}[Fintype α](e:α ↪ β):α ≃ ↥(subface e):=
  Equiv.ofBijective (fun i=>⟨e i,Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩) (by
    constructor
    · exact fun _ _ eq=>e.injective (congrArg Subtype.val eq)
    · rintro ⟨i,hi⟩
      obtain ⟨j,_,rfl⟩:=Finset.mem_map.mp hi
      exact ⟨j,rfl⟩)

theorem selected {α β:Type*}[Fintype α](e:α ↪ β)(i:α):(visit e i).val=e i:=rfl

end YM.Integration.WilsonMovingForkProbeMaster
