import YM.Integration.WilsonIndependentMatchedFreshInlet
import YM.RG08.Arcade.Stars

/-! A lower slot is injected into the common cap with its own marked
engineering weight and its original thermal order.  This uses the actual
coherent basis, so it retains descendants as well as the scalar. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMatchedFreshCapSix
open Lattice Wilson Source Labels RG PhysicalNext.Repeat.Legato
open Push.CutoffProjectors WilsonIndependentMatchedFreshInlet
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {d:ℕ}

def seat (hd:d ≤ 6) (i : (R.family.labels.level d).Index) : (R.family.labels.level 6).Index :=
  RG08.Arcade.sequel R.family.labels hd i

theorem board (hd:d ≤ 6) (i:(R.family.labels.level d).Index) :
    (R.family.labels.level 6).basis (seat R hd i)=raiseLabel G hd ((R.family.labels.level d).basis i) ∧
    (R.family.labels.level 6).grades (seat R hd i)=(R.family.labels.level d).grades i ∧
    embed R hd (Pi.single i 1)=Pi.single (seat R hd i) 1 := by
  have hs:=RG08.Arcade.lifted R.family.labels hd i
  refine ⟨hs,RG08.Arcade.relayV R.family.labels hd i,?_⟩
  rw [embed, ← (R.family.labels.level d).coords_basis i,LinearEquiv.symm_apply_apply,
    ←hs,(R.family.labels.level 6).coords_basis]
  rfl

theorem filed (hd:d ≤ 6) (δ:ℝ) (x:(R.family.labels.level d).Coeff) (J:Jet G) (l:Fin 7) :
    bank R 6 (((δ:ℂ)^(6-d)) • embed R hd x) (J,l) =
    (δ:ℂ)^(6-d) * iteratedDeriv (l : ℕ)
      (fun r : ℝ=>Labels.read (scaleJet J r) ((R.family.labels.level d).coords.symm x).val) 0 := by
  rw [earned,map_smul,smul_eq_mul,probe_eq,embed,LinearEquiv.symm_apply_apply]
  rfl

theorem injective (p:d ≤ 6) : Function.Injective (seat R p) :=
  RG08.Arcade.sq_inj R.family.labels p

end YM.Integration.WilsonIndependentMatchedFreshCapSix
