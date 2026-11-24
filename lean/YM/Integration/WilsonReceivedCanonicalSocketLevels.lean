import YM.Integration.WilsonReceivedCanonicalVerseRegister

/-! Ordinary incoming words at the fixed, jointly planted canonical sockets. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonReceivedCanonicalSocketLevels
open Lattice RG Finset WilsonCoeffUV WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel WilsonCoeffUV.Blue WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer
open scoped BigOperators Classical

/-- At a simultaneous birth, only singleton connected coefficients are occupied. -/
theorem born {V C:Type} [DecidableEq V] [CommRing C]
    (f:Sac V C)(dark:∀s:Finset V,(∀j:V,s≠{j})→f s=0):
    Equation (fun s=>∏j∈s,f {j}) f:=by
  classical
  refine ⟨by simp, dark ∅ (by simp),?_⟩
  funext s
  let singles:Finset (Finset V):=s.image (fun j=>{j})
  have small:singles⊆s.powerset:=by
    intro t ht
    obtain ⟨j,hj,rfl⟩:=mem_image.mp ht
    simpa using hj
  rw [shells]
  have fixed:∀t∈s.powerset,t∉singles→dial f t*(∏j∈s\t,f {j})=0:=by
    intro t ht out
    have no:∀j:V,t≠{j}:=by
      intro j eq
      subst t
      exact out (mem_image.mpr ⟨j,mem_powerset.mp ht (mem_singleton_self j),rfl⟩)
    simp [dial,dark t no]
  rw [←sum_subset small fixed,show singles=s.image (fun j=>{j}) from rfl,
    sum_image (by intro j _ k _ eq;simpa using eq)]
  calc
    dial (fun t=>∏j∈t,f {j}) s = ∑_j∈s,∏j∈s,f {j}:=by simp [dial]
    _ = _:=by
      apply sum_congr rfl
      intro j hj
      rw [dial,card_singleton,one_smul,sdiff_singleton_eq_erase]
      exact (Finset.mul_prod_erase s (fun j=>f {j}) hj).symm

theorem original {G:Gauge}{V:Type} [DecidableEq V] {D k:V→ℕ}
    (M:family G D)(paid:Eu k M)(dark:∀s:Finset V,(∀j:V,s≠{j})→M s=0)
    (A:Case D)(n:Side)(s:Finset V):
    readO A (levelsO M s) n=∏j∈s,readO A (M {j}) n:=by
  have inside:=levels_exp M paid (dark ∅ (by simp)) A n
  have start:∀t:Finset V,(∀j:V,t≠{j})→feeble M A n t=0:=by
    intro t h
    rw [feeble,dark t h,read_emp]
  exact congrFun (Equation.prod_u _ _ _ inside (born _ start)) s

open Function Finset Lattice Laurent Wilson RG Source Labels
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm
open IndependentSourcePathFamily OriginalMarkedSourceComet WilsonThermometerDeclaredSeeds
open WilsonOriginalStarSceneWords WilsonReceivedCanonicalVerseBasis
open WilsonReceivedCompactVerseEntrance (CoverBill)
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonReceivedCanonicalVerseRegister

theorem canonical {G:Gauge}{V:Type} [Fintype V][DecidableEq V](R:Run G)(d:V→ℕ){h:V→ℕ}
    (κ:(j:V)→Knob (h j))(pt:V→Chamber)(q:(j:V)→Choice R d j)(a:V→Lattice.Cover)
    (A:Case h)(n:Side)(s:Finset V):
    readO A (levelsO (start R d κ pt q a) s) n=∏j∈s,readO A (start R d κ pt q a {j}) n:=
  original _ (IndependentSourcePathFamily.legal _ a (fun j _=>grade R d κ pt j (q j)))
    (fun _ no=>Finset.sum_eq_zero fun j _=>dif_neg (Ne.symm (no j))) A n s

end YM.Integration.WilsonReceivedCanonicalSocketLevels


