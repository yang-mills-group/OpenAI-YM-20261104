import YM.Integration.WilsonPhysicalHistoryKioskSubset

/-! On each original filed nonempty marker mode, withdraw its own unmasked
reading. The exact missing part is seated on the very same failed support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedKioskOccupiedSlip
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Corrected Push.AbsoluteSums MeasureTheory QuadraticLocal
open Progress.DirectedRecipe Push.Local Animals Next.Foundations Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{T I V:Type}[DecidableEq V][Fintype V]{p:BudgetPoint}{o:V → Site n}{R:Census V}
variable (L:Lamps T I G p o R)

def gap (t:T)(i:I)(u:Config G n):ℂ:=L.light t i u-L.nominal t i u

omit [Fintype V] in
theorem healthy (t:T)(i:I)(u:Config G n)(hh:Healthy p.threshold (L.ground i) u):gap L t i u=0:=by
  unfold gap Lamps.light
  split
  · exact sub_self _
  · rw [masked_eq _ _ _ _ hh,sub_self]

omit [Fintype V] in
theorem size (t:T)(i:I)(u:Config G n): ‖gap L t i u‖ ≤ ‖L.nominal t i u‖:=by
  by_cases hh:Healthy p.threshold (L.ground i) u
  · rw [healthy L t i u hh,norm_zero];exact norm_nonneg _
  unfold gap Lamps.light
  split
  · rw [sub_self,norm_zero];exact norm_nonneg _
  · rw [masked_ne _ _ _ _ hh,zero_sub,norm_neg]

def sheet : Canopy.ShiftRows T I G p o R where
  place i:=⟨L.ground i,⟨(L.address i).site,(L.address i).anchor⟩⟩
  soap t i u:=Poly.send (L.mode i) (gap L t i u)
  cost t i:=by
    let f:=L.light t i
    have masking:UsesFinal p.threshold (L.ground i) f∧GaugeInvariant f∧Measurable f:=by
      by_cases c:L.clear i
      · have e:f=L.nominal t i:=funext fun _=>if_pos c
        rw [e];exact ⟨fun u v same _=>(L.legal t i).sites u v same,(L.legal t i).symmetry,(L.legal t i).borel⟩
      · have e:f=masked p.threshold (L.ground i) (L.nominal t i):=funext fun _=>if_neg c
        rw [e];exact ⟨uses_mask _ (L.legal t i).sites,invariant_mask (L.legal t i).symmetry _ _,masked_measurable _ _ _ (L.legal t i).borel⟩
    let C:ℂ→ₗ[ℂ] Poly R:={toFun:=Poly.send (L.mode i),map_add':=send_add _,map_smul':=?_}
    swap
    · intro a b;change Poly.send (L.mode i) (a*b)=a • Poly.send (L.mode i) b
      ext m;rw [Poly.part_smul,Poly.part_send,Poly.part_send];split <;>simp
    refine ⟨fun z u=>congrArg C (congrArg₂ (·-·) (masking.2.1 z u) ((L.legal t i).symmetry z u)),
      C.toContinuousLinearMap.continuous.measurable.comp (masking.2.2.sub (L.legal t i).borel),
      fun u v same flags=>congrArg C (congrArg₂ (·-·) (masking.1 u v same flags) ((L.legal t i).sites u v same)),
      fun u j live v hv=>?_⟩
    change (Poly.send _ _).part j≠0 at live
    rw [Poly.part_send] at live
    split at live
    · rename_i eq;exact L.roots i v (eq ▸ hv)
    · contradiction
  clean t i u h hh:=h (by rw [healthy L t i u hh,Poly.send_zero])
  skip t i u:=by rw [Poly.part_send,if_neg (L.live i).symm]
  single t i u:=by
    obtain ⟨v,hv⟩:=Finset.nonempty_iff_ne_empty.mpr (show (L.mode i).val ≠ ∅ from fun eq=>L.live i (Subtype.ext eq))
    exact Classical.byContradiction fun h=>disjoint_left.mp ((merges_of_tagged_mul h).choose_spec.1) hv hv

def bare (t:T)(u:Config G n):Poly R:=∑' i,Poly.send (L.mode i) (L.nominal t i u)

structure Gross (w:V → ℝ)(B:ℕ)(a d:ℝ):Prop where
  before : ∃f:I→ℝ,(∀i,0≤f i) ∧ (∀ i t u,‖L.nominal t i u‖ ≤ f i) ∧
    Hit L.ground B (fun i=>Poly.toll w (L.mode i)*f i) a d

omit [Fintype V] in
theorem split [Fintype I] (t:T)(u:Config G n): L.log t u = bare L t u+(sheet L).log t u:=by
  classical
  simp only [bare,Canopy.ShiftRows.log,Lamps.log,tsum_fintype,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change Poly.send _ (L.light t i u)=Poly.send _ (L.nominal t i u)+Poly.send _ (gap L t i u)
  rw [←send_add,gap];congr 1;abel

omit [Fintype V] in
theorem quiet [Fintype I] (t:T)(u:Config G n):(bare L t u).part R.quiet=0:=by
  simp only [bare,tsum_fintype,Poly.part_sum,Poly.part_send]
  exact Finset.sum_eq_zero fun i _=>if_neg (L.live i).symm

end YM.Integration.WilsonRootedKioskOccupiedSlip
