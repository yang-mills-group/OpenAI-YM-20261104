import YM.Integration.WilsonThermometerOffsetSource
import YM.Integration.WilsonThermometerOffsetResidue

/-! A primary calibrated on its own address graph is one actual bare field.
Higher test letters may mix under transport and are projected only after the
whole field has reached the threshold at its true address. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetPrimary
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox
open PhysicalNext.Repeat.Legato MergeProof Accent
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (N p m : ℕ)

private theorem fixed {d : ℕ} (t : Letter d) (ht : depth t=0)
    (i : ℕ) (b : Bud R.family p i) : headFee R.family p i b (line t)=line t := by
  rcases t with ⟨⟨k,h⟩,j⟩
  change k=0 at ht; subst k
  apply Subtype.ext; funext x
  change (BoltBasis 0 j).val (fun _:Fin 0=>_)=(BoltBasis 0 j).val (fun _:Fin 0=>_)
  congr 1; funext e; exact e.elim0

theorem tested {d : ℕ} (sites : ∀ i,Bud R.family p i) (t : Letter d) (ht : depth t=0)
    (q : ℕ) : test R p m sites q (line t)=line t := by
  induction q with
  | zero => rfl
  | succ q ih => rw [test,ih,fixed R p t ht]

theorem scale (d q : ℕ) : units R m d q*(R.family.S.a (m+q):ℂ)^d = (R.family.S.a m:ℂ)^d := by
  induction q with
  | zero => simp [units]
  | succ q ih =>
    rw [units,←Nat.add_assoc,R.family.S.a_step]
    push_cast
    have h : ((R.family.S.block (m+q)).val:ℂ) ≠ 0 := by exact_mod_cast (R.family.S.block _).property.ne'
    rw [div_pow]
    convert ih using 1
    field_simp

private theorem split {d : ℕ} (x : Palette R.family d) : x = ∑ j, chunk j (x j) := by
  funext j
  rw [Finset.sum_apply,Finset.sum_eq_single j]
  · exact (chunk_self _).symm
  · exact fun q _ he=>chunk_miss _ he.symm
  · simp

theorem primary {base d : ℕ} {D : Rail R.family} {B : ℕ → ℕ → ℝ}
    {V : Sight R.family d p} {r : Emblems R.family d} {sites : ∀i,Bud R.family p i}
    (H : Enrolled R.makes D B base N p d sites V r) (entered : base ≤ m) (live : m ≤ N)
    (starts : ∀e≤d,R.family.ref e ≤ N) (t : Letter d) (ht : depth t=0) (y : Palette R.family d) :
    let x := (R.family.factory (kept t) N p).terminal (finer r live y t)
    let here := address R N p m sites (N-m) (by omega)
    pulseOut (V m y) (line t) = dyes R.family m N p live ((R.family.S.a m:ℂ)^d • R.family.O N p x here) := by
  intro x here
  let w := finer r live y
  let g := (finer r live).symm
  let A (j : Letter d) := R.family.O N p ((R.family.factory (kept j) N p).terminal (w j)) here
  have term (j : Letter d) : pulseOut (V m (g (chunk j (w j)))) (line t) =
      dyes R.family m N p live ((units R m d (N-m) * ((if j=t then 1 else 0)*
        (R.family.S.a N:ℂ)^(kept j))) • A j) := by
    have E := congrFun (WilsonThermometerOffsetPhysical.original R N p H entered live starts j
      ((R.family.factory (kept j) N p).terminal (w j))) (line t)
    simp only [LinearEquiv.symm_apply_apply] at E
    rw [WilsonThermometerOffsetCylinder.bare,tested R p m sites t ht,headC] at E
    unfold point at E
    rw [dif_neg (Nat.not_lt.mpr live)] at E
    exact E
  have parted : y=g (∑ j,chunk j (w j)) := by
    rw [←split R w]; exact (LinearEquiv.symm_apply_apply _ _).symm
  calc
    _ = ∑ j,pulseOut (V m (g (chunk j (w j)))) (line t) := by
      conv_lhs => rw [parted,map_sum,map_sum]
      simp only [pulseOut,LinearMap.sum_apply,Prod.fst_sum]
    _ = pulseOut (V m (g (chunk t (w t)))) (line t) := by
      apply Finset.sum_eq_single t
      · intro j _ ne
        rw [term,if_neg ne,zero_mul,mul_zero,zero_smul,dye_vac]
      · simp
    _ = _ := by
      rw [term,if_pos rfl,one_mul]
      have kept0 : kept t=d := by change d-depth t=d; rw [ht,Nat.sub_zero]
      have cutoff : m+(N-m)=N := by omega
      have paid := scale R m d (N-m)
      rw [cutoff] at paid
      have eng : units R m d (N-m)*(R.family.S.a N:ℂ)^(kept t)=(R.family.S.a m:ℂ)^d :=
        by simpa only [kept0] using paid
      rw [eng]

end YM.Integration.WilsonThermometerOffsetPrimary
end
