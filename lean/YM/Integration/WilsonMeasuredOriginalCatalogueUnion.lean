import YM.Integration.WilsonMeasuredTransitionCatalogue
import YM.Integration.WilsonEmittedFiledGerm

/-! The signed lower field consists of the actual emitted child rows and a
separate copy of the previous lower catalogue at each retained scalar lag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredOriginalCatalogueUnion
open Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 FVA1Physical.TwoReset
open AnalyticBridge.SectorAffine.Offset WilsonMeasuredTransitionCatalogue
open scoped BigOperators Classical
variable {G:Gauge} {n:Side} {C V X:Type} [Fintype C] [Fintype V]
  {I:C→Type} {K:V→Type} {P:C→Passport n Unit} {S:V→Passport n Unit}
  {J:Census Unit} {D:ℕ}
variable (F:(z:C)→I z→Row (P z) J G X) (T:(v:V)→K v→Row (S v) J G X)

def address (I:C→Type) (K:V→Type) : Names C V D→Type
  | .inl z=>I z
  | .inr (v,_)=>K v
def passport (P:C→Passport n Unit)(S:V→Passport n Unit) : Names C V D→Passport n Unit
  | .inl z=>P z
  | .inr (v,_)=>S v
def rows (a:Names C V D) : address I K a→Row (passport P S a) J G X :=
  match a with
  | .inl z=>F z
  | .inr (v,_)=>T v

omit [Fintype C] [Fintype V] in
theorem home (y:Site n) (f:∀z,(P z).origin ()=y) (t:∀v,(S v).origin ()=y)
    (a:Names C V D) : (passport P S a).origin ()=y := by
  cases a with
  | inl z => exact f z
  | inr b => exact t b.1

variable (d:ℕ) (s:Multi.Hot J) (t:X)
local notation "code" => (fun _:Unit=>d)
local notation "model" => rows (D:=D) F T
variable (r:ℝ) (c:V→ℕ→ℝ)
variable (L:Layout G) (tape:Finset Age)
local notation "pole₀" => Launch.index J code s.val + 1

theorem angular
    (staffF:∀z,∃σ k,Air.Staff (F z) (fun b=>(F z b).paint t) code σ k)
    (staffT:∀v,∃σ k,Air.Staff (T v) (fun b=>(T v b).paint t) code σ k)
    (read:∀e≤D,∀B:Stationary.Link G n,
      (r:ℂ)*(∑z,(peek dvd_rfl (F z) code L tape t e B).part s.val) =
        ∑v,∑l∈(Finset.HasAntidiagonal.antidiagonal e:Finset (ℕ×ℕ)),
          (c v l.1:ℂ)*(peek dvd_rfl (T v) code L tape t l.2 B).part s.val)
    (i:ℕ) (hi:i < pole₀ + D + 1) (u:Directions G n) :
    (∑a:Names C V D,weight r c a • WilsonEmittedFiledGerm.price model (fun _=>code)
      (fun _=>t) lag s (fun _=>L) (fun _=>tape) i u a)=0 := by
  let A:=WilsonCubicOriginalTorus.coordinates G n u
  let top (z:C)(j:ℕ):=(peek dvd_rfl (F z) code L tape t j A).part s.val
  let bottom (v:V)(j:ℕ):=(peek dvd_rfl (T v) code L tape t j A).part s.val
  have identical(a:Names C V D):WilsonEmittedFiledGerm.price model (fun _=>code)
      (fun _=>t) lag s (fun _=>L) (fun _=>tape) i u a =
      slice pole₀ i (lag a) (WilsonMeasuredTransitionCatalogue.value top bottom a) := by
    cases a with
    | inl z =>
      obtain ⟨σ,k,Pz⟩:=staffF z
      unfold WilsonEmittedFiledGerm.price slice
      simp only [rows,lag,WilsonMeasuredTransitionCatalogue.value,top]
      split
      · rw [WilsonMeasuredOriginalPeriodRead.original (F z) code t Pz L tape _ A]
        rfl
      · rfl
    | inr b =>
      obtain ⟨σ,k,Pv⟩:=staffT b.1
      rcases b with ⟨v,l⟩
      unfold WilsonEmittedFiledGerm.price slice
      simp only [rows,lag,WilsonMeasuredTransitionCatalogue.value,bottom]
      split
      · rw [WilsonMeasuredOriginalPeriodRead.original (T v) code t Pv L tape _ A]
        rfl
      · rfl
  simp_rw [identical]
  exact WilsonMeasuredTransitionCatalogue.signed r c top bottom (fun e he=>read e he A) pole₀ i hi

theorem field (g:ℝ)(s:J.Mode)(t:X)(U:Config G n) :
    (∑a:Names C V D,weight r c a • (g^(lag a) • (Spill.Foundry.uncut (model a) g t U).part s))=
      r • (∑z,(Spill.Foundry.uncut (F z) g t U).part s) -
      ∑v,(∑l:Fin (D+1),(c v l)*g^l.val) • (Spill.Foundry.uncut (T v) g t U).part s := by
  classical
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [rows,WilsonMeasuredTransitionCatalogue.weight,lag,pow_zero,one_smul,smul_smul,neg_mul,neg_smul,Finset.sum_smul,Finset.smul_sum,
    Finset.sum_neg_distrib,sub_eq_add_neg]
  rfl

end YM.Integration.WilsonMeasuredOriginalCatalogueUnion
end
