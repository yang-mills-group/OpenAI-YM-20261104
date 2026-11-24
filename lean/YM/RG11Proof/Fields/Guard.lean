import YM.RG11Proof.Fields.Grades
import YM.RG11Proof.Horizon.Quotient
/-! Engineering filtration and H action in real row coordinates agree
precisely with the separated `Position.Buffer` convention at the level of
allowed variations. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD MvPolynomial YM.Pert.RawLabels
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {F : Frames G} {d : ℕ}

namespace Basis
variable (B:Basis F d)

def holding (s:Signed): Module.End ℂ (E F d):= (freeTable F).mirror (table_spin F) d s
def Hmat (s: Signed): Square B.J ℝ:= Matrix.of fun i j=> B.coord (holding s (B.b i)) j

theorem Hmap (s : Signed): B.liftRows (B.Hmat s) = holding s:= by
  apply B.b.ext; intro i; rw [row_basis]; apply B.put_round
  unfold Basis.overReals holding; rw [Table.mirror_star,B.pinned]

-- Every buffer occurs as a unique real matrix on this real basis.
def seats (z : Buffer F d) : Square B.J ℝ:= Matrix.of fun i j=>B.coord (z.val (B.b i)) j

theorem lift_all (z : Buffer F d): B.realLift (seats B z)=z.val:=by
  let L:E F d→ₗ[ℂ] E F d:={
      toFun x:=z.val x
      map_add' x y:= map_add ..
      map_smul' a x:= Pert.Rigid.dispatch_cmul F z a x }
  have he:B.liftRows (B.seats z)=L:=by
    apply B.b.ext; intro i; rw [row_basis]; apply B.put_round
    change (freeTable F).conj _ _ _ = _; rw [z.property.2.2.1,B.pinned]
  unfold realLift; rw [he]; rfl

theorem covers (z : Buffer F d):∃ m:B.guard.vary,B.operates m=z :=
  ⟨⟨B.seats z,(by change B.certified _; unfold certified; rw [lift_all]; exact z.property)⟩,Subtype.ext (lift_all ..)⟩
end Basis

-- With adapted grading exactly the usual grade-nonincreasing and H rule.
theorem exactGuard (B:Adapted F d)(Z:Square B.toBasis.J ℝ) :
    Z ∈ B.toBasis.guard.vary ↔ Z ∈ (Constraints.position B.unitIndex (fun i=> (B.w i).1) B.toBasis.Hmat).vary:=by
  let V:=B.toBasis
  rw [Constraints.mem_position_iff]; constructor
  · intro hz
    let z:V.guard.vary:=⟨Z,hz⟩
    let T:=V.operates z
    have he(i): T.val (B.b i)=V.put (fun j=>Z i j):= V.row_basis Z i
    constructor
    · intro i j h
      let k:=(B.w i).1
      have hv : k<d:=lt_of_lt_of_le h (B.heights j)
      have hl:T.val (B.b i)∈lower F k d:= T.property.2.1 k hv (B.b i) (stairs B i le_rfl)
      rw [he] at hl
      have ht:=small_read B j h _ hl; change V.b.equivFun (V.put (fun j=>Z i j)) j=0 at ht; simpa only [Basis.coeff_put,Complex.ofReal_eq_zero] using ht
    constructor
    · intro j; apply Complex.ofReal_injective; simp only [Complex.ofReal_zero, ← V.coeff_put (x:=fun j=>Z B.unitIndex j) j]
      rw [←he,B.unitAt,T.property.1,map_zero]; rfl
    intro s; apply V.row_injective
    rw [V.row_map_mul,V.row_map_mul,V.Hmap]; apply LinearMap.ext; intro p
    change Pert.Rigid.wear F d s (T.val p)= T.val (Pert.Rigid.wear F d s p)
    simp_rw [Pert.Rigid.wear_ride]; exact (V.operates z).property.2.2.2.1 ..
  rintro ⟨hq,hz,h⟩
  change V.certified Z
  let L := V.realLift Z
  constructor
  · change V.liftRows Z ((freeTable F).unit d) = _; rw [← B.unitAt,V.row_basis,funext hz]; exact V.put_zero
  constructor
  · intro e hd p hp
    nth_rw 1 [← B.b.sum_equivFun p]
    change L (∑ i,B.b.equivFun p i • B.b i)∈_
    rw [_root_.map_sum]; apply Submodule.sum_mem; intro i _
    change V.liftRows Z (_ • _)∈_; rw [_root_.map_smul,V.row_basis, V.put_sum]
    by_cases hv:(B.w i).1≤e
    · apply Submodule.smul_mem; apply Submodule.sum_mem; intro j _
      by_cases ht:(B.w i).1<(B.w j).1
      · rw [hq i j ht, Complex.ofReal_zero,zero_smul]; exact Submodule.zero_mem _
      exact Submodule.smul_mem _ _ (stairs B j ((le_of_not_gt ht).trans hv))
    rw [small_read B i (lt_of_not_ge hv) _ hp,zero_smul]; exact Submodule.zero_mem _
  constructor
  · intro p; change (freeTable F).conj (table_spin F) d (V.liftRows Z p)=V.liftRows Z _
    let C:=(freeTable F).conj (table_spin F) d
    change C (V.liftRows Z p)=V.liftRows Z (C p)
    rw [← B.b.sum_equivFun p,_root_.map_sum,_root_.map_sum,_root_.map_sum,_root_.map_sum]; apply Finset.sum_congr rfl; intro i _
    rw [_root_.map_smul,map_smulₛₗ,map_smulₛₗ,_root_.map_smul,V.row_basis, show C _=_ from B.pinned i,V.row_basis]; exact congrArg (_ • ·) (V.puts_real _)
  refine ⟨?_,fun p=> (V.liftRows Z).map_smul Complex.I p⟩
  intro s p
  have he := congrArg V.liftRows (h s)
  rw [V.row_map_mul,V.row_map_mul,V.Hmap] at he
  -- `wear` = `ride` via accepted bridge
  simp_rw [← Pert.Rigid.wear_ride F]
  exact LinearMap.congr_fun he p
end YM.RG11.Fields
