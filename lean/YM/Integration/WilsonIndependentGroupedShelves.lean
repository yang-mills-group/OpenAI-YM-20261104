import YM.RegulatorIR.Atlas.Outfit

/-! Pre-length damping and post-length prices for a finite menu of actual
auxiliary Wilson blocks. The bound is independent of the schedule length. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonIndependentGroupedShelves
open RegulatorIR Lattice RG RegulatorIR.Oracle RegulatorIR.Epoch
open RegulatorIR.Epoch.League RegulatorIR.Atlas RegulatorIR.Uniform
open RegulatorIR.Ledger
open scoped ENNReal NNReal BigOperators Classical

variable {X:Type}{M:X→ℕ}{n:Page M→Side}{K:KernelChoices}
variable (G:Gauge)(Y:Program K)(Z:∀ P:Patch,P.Branches K G)

def floor (stages:Finset ℕ)(p u:ℕ)(γ:ℝ)(hγ:0<γ)(hγ':γ<1) :=
  stages.sup (fun j=>orders G Y p u j γ hγ hγ')

private theorem menu {A I:Type}(book:Finset A)(value:A→ℝ≥0∞)
    (finite:∀ a,value a≠⊤)(L:Meter I)(use:I→A)(listed:∀ i,use i∈book) :
    Poly L (value ∘ use) :=
  (Poly.standard L (ENNReal.sum_ne_top.mpr (fun a _=>finite a) :
    (∑ a∈book,value a)≠⊤)).mono fun i=>Finset.single_le_sum
      (fun _ _=>zero_le) (listed i)

theorem original (S:Circuit M n)(stages:Finset ℕ)(p u:ℕ)(γ:ℝ)(hγ:0<γ)
    (hγ':γ<1)(grades:∀ j∈stages,5≤j)(height:p+2≤u)(depth:3≤u)
    (paid:∀ i:Flap M,floor G Y stages p u γ hγ hγ'≤(S.sizeL i).val)
    (patches:Finset Patch)(stage:∀ i,S.J i∈stages)(patch:∀ i,S.pactP i∈patches)
    (z:X→ℝ)(hz:∀ w,0≤z w) :
    SatisfiesQ G Y S Z (stampE S z hz) p u γ := by
  let band:=stampE S z hz
  let length (P:Patch) := ENNReal.ofReal (P.L.val:ℝ)
  have edges (L:Meter (Flap M)) :
      Poly L band.day := menu patches length (fun _=>ENNReal.ofReal_ne_top) L _ patch
  refine ⟨fun _=>rfl,⟨edges _,edges _⟩,depth,height,
    menu patches _ (gf_f G Y Z) _ _ patch,
    menu stages _ (gpage_f G Y) _ _ stage,hγ,hγ',fun i=>grades _ (stage _),?_⟩
  intro i
  exact (Finset.le_sup (f:=fun j=>orders G Y p u j γ hγ hγ')
    (stage i.prev)).trans (paid i)

end YM.Integration.WilsonIndependentGroupedShelves
