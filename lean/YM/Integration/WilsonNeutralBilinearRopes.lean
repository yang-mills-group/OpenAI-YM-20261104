import YM.Integration.WilsonNeutralBilinearLetters
import YM.Integration.WilsonNeutralFiledFieldReversion
import YM.FormalBulk08.Trellis.Ferment

/-! The complete finite-top inverse of the filed grade-four field matrix, in
its true sequence of coupling coordinates.  An addressed unit (including
test derivatives) is allowed in every intermediate input. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonNeutralBilinearRopes
open PowerSeries FormalBulk08 Matrix Lattice Laurent RG Wilson
open Pose Dawn Roof Grail Trellis Filter Dove
open Planned.PrimaryIntegral295 Source Labels Next.Foundations
open WilsonRunFormalMarkedStep
open Precision Exterior Tree Stationary Push.Uniform Bloch Reef Jets Orb Wick Flat Next.Free UVExtension.Free
open Function Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Glide Bank Wine Rial
open PhysicalNext.Repeat.Legato FVA1Physical.TwoReset
open scoped BigOperators Classical

private def Row {I:Type}[DecidableEq I](A:Matrix I I Pence)(s:I):Prop:=
  (∀v,coeff 0 (A s v)= if s=v then 1 else 0) ∧ (∀v,coeff 1 (A s v)=0)

private lemma product {I:Type}[Fintype I][DecidableEq I]
    {A:Matrix I I Pence}{s:I}(h:Row A s)(B:Matrix I I Pence)(v:I):
    coeff 0 ((A*B) s v)=coeff 0 (B s v) ∧ coeff 1 ((A*B) s v)=coeff 1 (B s v):=by
  have c0 (a b:Pence):coeff 0 (a*b)=coeff 0 a*coeff 0 b:=by
    simp only [coeff_zero_eq_constantCoeff_apply,map_mul]
  have c1 (a b:Pence):coeff 1 (a*b)=coeff 0 a*coeff 1 b+coeff 1 a*coeff 0 b:=by
    rw [coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp [Finset.sum_range_succ]
  constructor
  · simp only [Matrix.mul_apply,map_sum,c0,h.1,ite_mul,one_mul,zero_mul]
    simp
  · simp only [Matrix.mul_apply,map_sum,c1,h.1,h.2,zero_mul,add_zero,ite_mul,one_mul]
    simp

private lemma identity {I:Type}[DecidableEq I](s:I):Row (1:Matrix I I Pence) s:=by
  constructor <;> intro v <;> by_cases h:s=v <;> simp [Matrix.one_apply,h]

private lemma invert {I:Type}[Fintype I][DecidableEq I]
    {A:Matrix I I Pence}{s:I}(h:Row A s)(unit:IsUnit A.det): Row A⁻¹ s:=by
  have eq:=Matrix.mul_nonsing_inv A unit
  have read (v:I):=product h A⁻¹ v
  constructor
  · intro v;exact ((read v).1.symm.trans (by rw [eq]; exact (identity s).1 v))
  · intro v;exact ((read v).2.symm.trans (by rw [eq]; exact (identity s).2 v))

private lemma pull {I:Type}[DecidableEq I]{A:Matrix I I Pence}{s:I}(h:Row A s)
    (K:ℕ→Pence)(m i:ℕ):Row (A.map (flow K m i)) s:=by
  refine ⟨fun v=>(topcoin K m i (A s v)).trans (h.1 v),?_⟩
  intro v
  change coeff 1 (flow K m i (A s v))=0
  rw [flows,Series.subst_coeff (bottomless (expanse K m i)) _ 1 1 le_rfl]
  simp [Finset.sum_range_succ,h.2]

variable {G:Gauge} (R:Run G) {D:ℕ}(wood:Primer.Families R.family)(a:hue G)
    (depth:4<D) {U:ℕ→ℕ}(grant:WilsonWindowFormalPurchase.Canonical U R.kit)
local notation "F₄" => R.family.labels.level 4
local notation "nonunit" => {s:(F₄).Index // s≠0}
local notation "S₀" => Primer.fieldStep R.family a wood depth
local notation "K₀" => WilsonNeutralFiledFieldReversion.kinetic R wood a

include grant in
private theorem filed (N i:ℕ)(simple:G.Simple)(o:Loc G 1)(hi:i<N)
    (front:4≤R.family.path.levels.clock.J (i+1))(s:nonunit):
    Row (S₀ N i) (WilsonNeutralBilinearLetters.plain (F₄) s) := by
  let x:=WilsonNeutralBilinearLetters.plain (F₄) s
  have active:Pose.mint (F₄) x ≠0:=s.prop
  have own:=WilsonNeutralBilinearLetters.literal (F₄) simple x active
  refine ⟨?_,fun v=>WilsonNeutralBilinearTransfer.original R wood a depth grant N i simple o hi front (by decide) x v⟩
  intro v
  by_cases live:Pose.mint (F₄) v≠0
  · have same:=WilsonNeutralBilinearLetters.literal (F₄) simple v live
    exact WilsonNeutralNativeFreeStep.own_weight R wood a depth grant N i simple o hi front x v
      (own.2.2.trans same.2.2.symm) own.2.1 same.2.1
  · have quiet:Pose.mint (F₄) v=0:=not_ne_iff.mp live
    have slots:Pose.slots (F₄) v=0:=by change ((F₄).grades (mint (F₄) v)).2=0;rw [quiet,(F₄).zero_degree]
    have diff:x≠v:=fun eq=>active (eq ▸ quiet)
    have invoice:=WilsonNeutralNativeFreeStep.original R wood a depth grant N i simple o hi front
    exact (invoice.bound x v 0 (by rw [slots,own.2.2];decide)).trans (if_neg diff).symm

include grant in
/-- The actual pre-inverted native series at each intervening date is re-read
in the same measured thermal coordinate. The claim includes every input label. -/
theorem original (N m h k:ℕ)(simple:G.Simple)(o:Loc G 1)(dates:m+h≤N)
    (front:4≤R.family.path.levels.clock.J (m+1))(s:nonunit):
    let x:=WilsonNeutralBilinearLetters.plain (F₄) s
    let V:=ropes (K₀ N) (S₀ N) k m h
    (∀v,coeff 0 (V x v)=if x=v then 1 else 0) ∧ (∀v,coeff 1 (V x v)=0):=by
  intro x V
  change Row (ropes (K₀ N) (S₀ N) k m h) x
  induction h with
  | zero =>exact identity x
  | succ h ih =>
    have openAt:4≤R.family.path.levels.clock.J (m+h+1):=front.trans (R.family.path.levels.fits.mono (by omega))
    have paid:=WilsonNeutralNativeFreeStep.original R wood a depth grant N (m+h) simple o (by omega) openAt
    have up:=pull (invert (filed R wood a depth grant N (m+h) simple o (by omega) openAt s) paid.det) (K₀ N) k (m+h)
    have old:=ih (by omega)
    rw [ropes_grow]
    exact ⟨fun v=>(product up _ v).1.trans (old.1 v),fun v=>(product up _ v).2.trans (old.2 v)⟩

end YM.Integration.WilsonNeutralBilinearRopes
end

