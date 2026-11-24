import YM.Integration.WilsonThermometerInversionSockets
import YM.Integration.WilsonThermometerFrozenRevaluation
import YM.FVA2.BareOrb

/-! The true copied numerical thermostat word, projected after multiplication
and after the individual monetary divisions, in the finite inversion
prescription on the same sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionFiling
open Function Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Orb PertExtension.Series WilsonOriginalStarSceneWords
open WilsonOriginalStarGradedScene WilsonThermometerDeclaredSeeds WilsonThermometerInversionSockets PowerSeries
open scoped Classical BigOperators
variable {V T : Type} {G:Gauge} (R:Run G) (d:V→ℕ) (s:Finset V)
    (b:(j:V)→Choice R d j) {n:Side} (o:V→Site n) (g τ:ℝ)
    (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "e" j:max => entry R d j (b j)
local notation "O" => WilsonThermometerInversionSockets.word R d s b o g τ v t x L
local notation "w" => charge R d s b

private theorem projection (S : Finset V) (a c:V→ℝ) (z:V→ℂ) :
    L (∏j∈S,↑(a j)*z j*↑(c j)) = (∏j∈S,a j)*L (∏j∈S,z j)*(∏j∈S,c j) := by
  simp_rw [Finset.prod_mul_distrib,←Complex.ofReal_prod]
  have h: (↑(∏j∈S,a j):ℂ)*(∏j∈S,z j)*↑(∏j∈S,c j)=
      ((∏j∈S,a j)*(∏j∈S,c j)) • (∏j∈S,z j) := by
    rw [Complex.real_smul,Complex.ofReal_mul]
    ring
  rw [h,map_smul,smul_eq_mul]
  ring

theorem restored (u : ℝ) (live : u≠0) (U:Config G n) :
    (∏ j∈s,(u^(d j+1))⁻¹) * L (∏ j∈s,
      WilsonThermometerFrozenCopies.word R d g τ v t (e j) u x (o j) U) =
      u⁻¹^(w)*(O) U := by
  have hp (j): WilsonThermometerFrozenCopies.word R d g τ v t (e j) u x (o j) U =
      ↑(u^(d j+1-pole R d (e j)))*(t j x*scalar R d g τ v (e j))*
      ↑((raw R d (e j)).unmasked U (o j)) := by
    rw [WilsonThermometerFrozenSockets.separated R d g τ v (e j)]
    simp only [WilsonThermometerFrozenCopies.word,site,Complex.ofReal_mul]
    ring
  simp_rw [hp]
  rw [projection,WilsonThermometerInversionSockets.word]
  have price : (∏ j∈s,(u^(d j+1))⁻¹)*(∏ j∈s,u^(d j+1-pole R d (e j)))=u⁻¹^(w) := by
    rw [←Finset.prod_mul_distrib,charge,←Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro j _
    have k:=pole_grade R d (e j)
    rw [site] at k
    have cut : u^(d j+1)=u^(d j+1-pole R d (e j))*u^(pole R d (e j)) := by
      rw [←pow_add,Nat.sub_add_cancel (Nat.le_succ_of_le k)]
    rw [cut,mul_inv_rev,mul_assoc,inv_mul_cancel₀ (pow_ne_zero _ live),mul_one,inv_pow]
  rw [←price]
  ring

variable (p:XSpace.Period) (o':V→Site p.side) (tree:p.Tree)
local notation "Z" => WilsonThermometerInversionSockets.word R d s b o' g τ v t x L

theorem periodic (h:ℕ) :
    coeff ((w)+h) (XSpace.Bare.normalized tree G (FVA2.BareOrb.stencil tree (Z))) =
      ↑(Orb.diag (restrictedO (Z)) ((w)+h)) := by
  rw [FVA2.BareOrb.diagram_eq tree (incoming R d s b o' g τ v t x L).1,
    FVA2.TaylorWick.into_coeff,coeff_mk]

theorem odd (h:ℕ) (parity:Odd ((w)+h)) :
    coeff ((w)+h) (XSpace.Bare.normalized tree G (FVA2.BareOrb.stencil tree (Z))) = 0 := by
  rw [periodic,Orb.diag,Orb.normalized_odd (traySpec G) (even_iff_two_dvd.mpr p.even) _ parity,Complex.ofReal_zero]

end YM.Integration.WilsonThermometerInversionFiling
