import YM.Integration.WilsonThermometerSeedReading
import YM.Integration.ActualOrbLeadingIR
import YM.PertExtension.BareSlot

/-! Whole finite inversion coefficients of each actual placed thermometer
socket on a single even torus. All numerical phase factors are frozen
before opening the original Haar integral. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerInversionSockets
open Function Filter Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.Series
open Series.Radial Series.Tested WilsonOriginalStarSceneWords WilsonThermometerDeclaredSeeds
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} (d : V→ℕ) {n : Side}

private theorem allowed (i : Entry R d) (z : Site n) :
    PreTest (fun U=>(raw R d i).unmasked U z) ∧
    RadialOrder (rank R d i) (fun x:Dir G n=>(raw R d i).unmasked (representative x) z) := by
  let a := raw R d i
  have hc := a.unmasked_cont z
  have smooth : ContDiff ℝ ∞ (fun x:Dir G n=>a.unmasked (representative x) z) := by
    change ContDiff ℝ ∞ (fun x=>∑ b:Fin (rank R d i)→G.ColorIndex,
      a.coeff b*∏ j:Fin (rank R d i),field (a.leg j) z (b j) x)
    exact ContDiff.sum (fun b _=>contDiff_const.mul
      (contDiff_prod (fun j _=>coordinateContour (a.leg j) z (b j))))
  refine ⟨⟨?_,⟨hc.comp Orb.continuous_links,smooth.contDiffAt⟩,hc⟩,?_⟩
  · intro u _ U
    simp only [Atom.unmasked,Work.F05.slot_gauge]
    exact lawful R d i (u z) _
  · intro x
    let word (b:Fin (rank R d i)→G.ColorIndex) (t:ℝ) :=
      a.coeff b*∏ j:Fin (rank R d i),field (a.leg j) z (b j) (t • x)
    have row (b:Fin (rank R d i)→G.ColorIndex) : Bill (rank R d i) (word b) := by
      have h:=bill_product univ (fun _:Fin (rank R d i)=>1)
        (fun j (t:ℝ)=>field (a.leg j) z (b j) (t • x)) (fun j _=>slotOrder (a.leg j) z (b j) x)
      simpa [word] using! bill_mul (bill_const (a.coeff b)) h
    convert! bill_sum univ word (fun b _=>row b) using 1
    funext t
    simp only [Finset.sum_apply]
    rfl

variable (s:Finset V) (b:(j:V)→Choice R d j) (o:V→Site n) (g τ:ℝ)
  (v:(j:V)→R.family.label (d j)) (t:V→T→ℂ) (x:T) (L:ℂ→L[ℝ]ℝ)
local notation "e" j:max => entry R d j (b j)

def word (U:Config G n) : ℝ :=
  L (∏ j∈s,t j x*scalar R d g τ v (e j)) * ∏ j∈s,(raw R d (e j)).unmasked U (o j)

def charge : ℕ := ∑ j∈s,pole R d (e j)

local notation "O" => word R d s b o g τ v t x L
local notation "w" => charge R d s b

private theorem grouped {V' : Type} (S : Finset V') (f : V' → Config G n→ℝ)
    (c : ℝ) (a : V'→ℕ) (h : ∀j,PreTest (f j) ∧ RadialOrder (a j) (fun y=>f j (representative y))) :
    let φ := fun U=>c * ∏j∈S,f j U
    PreTest φ ∧ RadialOrder (∑j∈S,a j) (fun y:Dir G n=>φ (representative y)) := by
  let fn := fun U=>c * ∏j∈S,f j U
  have hc : Continuous fn := continuous_const.mul (continuous_finsetProd S (fun j _=>(h j).1.continuous))
  have hd : ContDiffAt ℝ ∞ (fun y:Dir G n=>fn (representative y)) 0 :=
    contDiffAt_const.mul (contDiffAt_prod (t:=S) (f:=fun j y=>f j (representative y))
      (fun j _=>(h j).1.curved.germ))
  refine ⟨⟨?_,⟨hc.comp Orb.continuous_links,hd⟩,hc⟩,?_⟩
  · intro u hu U
    exact congrArg (c*·) (Finset.prod_congr rfl (fun j _=>(h j).1.gauge u hu U))
  · intro y
    have hp:=bill_product S a (fun j (u:ℝ)=>f j (representative (u • y))) (fun j _=>(h j).2 y)
    simpa only [Finset.prod_apply,Nat.zero_add] using! bill_mul (bill_const c) hp

theorem incoming :
    PreTest (O) ∧ RadialOrder (w) (fun y:Dir G n=>(O) (representative y)) :=
  grouped s (fun j U=>(raw R d (e j)).unmasked U (o j))
    (L (∏ j∈s,t j x*scalar R d g τ v (e j))) (fun j=>pole R d (e j))
    (fun j=>⟨(allowed R d (e j) (o j)).1,
      fun y=>bill_ge ((allowed R d (e j) (o j)).2 y) (low R d (e j))⟩)

theorem finite (ev : Even n.val) :
    Aspiration (fun u:ℝ=>(u⁻¹)^(w)*preExpectation (O) u)
      (fun j=>Orb.diag (restrictedO (O)) ((w)+j)) := by
  obtain ⟨hp,order⟩:=incoming R d s b o g τ v t x L
  exact (before_tree_formula ev (traySpec G) hp).shift (diag_down (traySpec G) hp.curved order ev)

end YM.Integration.WilsonThermometerInversionSockets
