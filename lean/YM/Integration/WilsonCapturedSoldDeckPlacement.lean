import YM.Integration.WilsonMeasuredOriginalPeriodRead
import YM.Integration.WilsonCapturedSoldThreeFrontRate
import YM.Work.E04

/-! The physical pair supplies an enrolled relative lift on every copied torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonCapturedSoldDeckPlacement
open Finset Filter Lattice Wilson RG FVA1Physical.TwoReset
open Further.PhysicalPeriodLimitF933 Macrame Shingle PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology

theorem matched {n N:Side}(h:n.val∣N.val)(x y:Site n)(a:Fin (Pages n N)):
    ∃b:Fin (Pages n N),separation (page h x a).val (page h y b).val=separation x y:=by
  let old:=(page h x a).val
  let δ:=lift (x-y)
  let placed:=old-wrap N δ
  have fold:splitter h old=x:=(posted ..).mp (page h x a).property
  have face:splitter h placed=y:=by
    change splitter h (old-wrap N (lift (x-y)))=y
    rw [map_sub,branch,wrap_lift,fold,sub_sub_cancel]
  have belongs:= (posted (splitter h) y placed).mpr face
  obtain ⟨b,hit⟩:= (page h y).surjective (⟨placed,belongs⟩:parcel (splitter h) y)
  refine ⟨b,?_⟩
  have extend:n.val ≤ N.val:=Nat.le_of_dvd N.property h
  have chart:lift (wrap N δ)=δ:=lift_eq_iff.mpr ⟨rfl,by
    intro i
    have small:=lift_centers (x-y) i
    change -((N.val:ℕ):ℤ)<2*lift (x-y) i ∧ 2*lift (x-y) i ≤ (N.val:ℤ)
    omega⟩
  change pdist (old-(page h y b).val)=pdist (x-y)
  rw [hit]
  change pdist (old-(old-wrap N δ))=pdist (x-y)
  rw [sub_sub_cancel];unfold pdist;rw [chart]

theorem shortened {l m n:Side}(newer:Ratio l m)(old:Ratio m n)(x y:Site n):
    (newer.count.val*old.count.val)*separation (newer.parent (old.parent x)) (newer.parent (old.parent y)) ≤
      separation x y+2*(newer.count.val*old.count.val):=by
  have upper:=Corona.foreshorten old x y
  have lower:=Corona.foreshorten newer (old.parent x) (old.parent y)
  have scales:old.count.val ≤ newer.count.val*old.count.val:=
    Nat.le_mul_of_pos_left old.count.val newer.count.property
  calc
    _=old.count.val*(newer.count.val*separation (newer.parent (old.parent x)) (newer.parent (old.parent y))):=by ac_rfl
    _ ≤ old.count.val*(separation (old.parent x) (old.parent y)+newer.count.val):=Nat.mul_le_mul_left _ lower
    _=old.count.val*separation (old.parent x) (old.parent y)+newer.count.val*old.count.val:=by ring
    _ ≤ _:=by omega

theorem short {l m n:Side}(newer:Ratio l m)(old:Ratio m n)(x y:Site n){B:ℕ}
    (range:separation x y ≤ B*(newer.count.val*old.count.val)):
    separation (newer.parent (old.parent x)) (newer.parent (old.parent y)) ≤ B+2:=by
  have line:=shortened newer old x y
  have bound:(newer.count.val*old.count.val)*separation (newer.parent (old.parent x)) (newer.parent (old.parent y)) ≤
      (newer.count.val*old.count.val)*(B+2):=
    line.trans ((Nat.add_le_add_right range _).trans_eq (by ring))
  exact Nat.le_of_mul_le_mul_left bound (Nat.mul_pos newer.count.property old.count.property)

def Room {G:Gauge}(R:Run G)(j per B:ℕ):Prop:=8*(B+2) ≤ (R.family.side j per).val

theorem period {G:Gauge}(R:Run G)(j B:ℕ):∀ᶠ per:ℕ in atTop,Room R j per B:=by
  have growth:Tendsto (fun per:ℕ=>(R.family.side j per).val) atTop atTop:=
    (show StrictMono (fun per:ℕ=>(R.family.side j per).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator j).pos).tendsto_atTop
  exact growth.eventually_ge_atTop _

theorem physical {G:Gauge}(R:Run G)(B:ℕ):∀ᶠ per:ℕ in atTop,∀j:ℕ,Room R j per (B*(R.family.S.denominator j).val):=by
  filter_upwards [R.family.S.period_strict.tendsto_atTop.eventually_ge_atTop (8*(B+2))] with per eligible
  intro j
  let cells:=(R.family.S.denominator j).val
  have positive:1 ≤ cells:=(R.family.S.denominator j).property
  change 8*(B*cells+2) ≤ (R.family.S.period per).val*cells
  calc
    _ ≤ 8*(B+2)*cells:=by nlinarith
    _ ≤ _:=Nat.mul_le_mul_right cells eligible

theorem ratio (S:Schedule)(j per:ℕ)(q:Ratio (S.side j per) (S.side (j+1) per)):
    (S.denominator (j+1)).val=(S.denominator j).val*q.count.val:=by
  have sizes:=q.exact_size
  change (S.period per).val*(S.denominator (j+1)).val=((S.period per).val*(S.denominator j).val)*q.count.val at sizes
  rw [Nat.mul_assoc] at sizes
  exact Nat.eq_of_mul_eq_mul_left (S.period per).property sizes

end YM.Integration.WilsonCapturedSoldDeckPlacement
