import YM.Integration.WilsonMacroscopicRichAperture
import YM.Push.ABSOLUTE_SUMS.Animals

/-! The actual number and angular size of bonds needed for the original positive output. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichApertureGeometry
open Filter Function Set Lattice Lattice.Corona Wilson RG OPE OPE.Orbits Source Labels Spec
open RG16 RGComparison.Core16 PhysicalNext.Repeat.Legato Analysis Next.Foundations Push.Local Bid
open Push.AbsoluteSums.Animals WilsonMacroscopicRichProbeShell WilsonMacroscopicRichCroppedProbe WilsonMacroscopicRichCroppedDeposit
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} (R:Run G)

def stencil (h:ℕ) := (R.family.localSection h).stencil.sup (fun x=>Finset.univ.sup fun i:Axis=>(x i).natAbs)
def radius (N p b h L:ℕ) := max (L*(4*(R.family.path.rep N p b).p.B+2)+2*(R.family.path.rep N p b).p.B) (stencil R h)

theorem extent (N p b h L:ℕ) {e:Edge (Site (R.family.side b p))} (member:e∈window R N p b h L):
    separation e.1 0≤radius R N p b h L :=by
  rcases Finset.mem_union.mp member with easy|fixed
  · exact (Finset.mem_filter.mp easy).2.trans (le_max_left ..)
  · obtain ⟨v,hv,seat⟩:=Finset.mem_image.mp (Finset.mem_product.mp fixed).1
    apply le_trans _ (le_max_right ..)
    simp only [add_zero] at seat
    rw [←seat,separation,sub_zero]
    apply Finset.sup_le;intro i hi
    exact (lap v i).trans ((Finset.le_sup (f:=fun a:Axis=>(v a).natAbs) hi).trans
      (Finset.le_sup (f:=fun x:Cover=>Finset.univ.sup fun a:Axis=>(x a).natAbs) hv))

theorem count (N p b h L:ℕ): (window R N p b h L).card≤4*ballCost (radius R N p b h L) :=by
  let D:=radius R N p b h L
  have incl:window R N p b h L⊆neighbors D (0:Site (R.family.side b p)) ×ˢ (Finset.univ:Finset Axis):=by
    intro e he;apply Finset.mem_product.mpr;refine ⟨(neighbors_mem ..).mpr ?_,Finset.mem_univ _⟩
    rw [separation_comm];exact extent R N p b h L he
  apply (Finset.card_le_card incl).trans
  rw [Finset.card_product,Finset.card_univ,show Fintype.card Axis=4 from rfl,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (neighbors_card ..)

/-- Every actual tangent from the prescribed angular probe has precisely this finite support and a uniformly purchased spatial polynomial. -/
theorem directions (h k:ℕ) (J:Jet G) :∃ c:ℝ,0<c ∧ ∀N p b L,
    let A:=window R N p b h L
    let D:=radius R N p b h L
    let θ:=(R.family.path.rep N p b).p.threshold
    let v:=iteratedDeriv k (mask A ∘ testLog R.family.params h 0 (θ • J)) 0
    (∀e,e∉A→v e=0) ∧ (∀e,‖v e‖≤c*θ*(1+(D:ℝ))^(k-1)) :=by
  obtain ⟨c,cp,field⟩:=testLog_bound R.family.params h k J
  refine ⟨c,cp,?_⟩;intro N p b L A D θ v
  have cut:v=mask A (iteratedDeriv k (testLog R.family.params h 0 (θ • J)) 0):=masked_jet A (testLog_diff ..) k
  have tp:= (R.family.path.rep N p b).p.threshold_pos
  refine ⟨fun e he=>by rw [cut,mask_off A he],?_⟩
  intro e;by_cases he:e∈A
  · rw [cut,mask_on A he]
    apply (field _ 0 e θ tp.le (R.family.path.rep N p b).p.threshold_le).trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg cp.le tp.le)
    apply pow_le_pow_left₀ (by positivity) (add_le_add_right _ _) _
    exact_mod_cast extent R N p b h L he
  · rw [cut,mask_off A he,norm_zero];exact mul_nonneg (mul_nonneg cp.le tp.le) (by positivity)

end YM.Integration.WilsonMacroscopicRichApertureGeometry
