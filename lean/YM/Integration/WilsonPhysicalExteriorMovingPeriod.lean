import YM.Integration.WilsonPhysicalExteriorLogRegulator

/-! On the original moving Wilson branch choose one actual period threshold
before every real subtraction clock and every finite bounded position roster,
including mixed, moving or coincident slots. This pays the infrared part of the
formal mixed-array comparison. Its second operand is the original infinite-period
Rocket.adjust on the same finite track. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorMovingPeriod
open Function Set Filter Lattice Precision RG PhysicalNext.Repeat.Legato RegulatorIR RegulatorIR.FVAAlt2
open RegulatorIR.FVAAlt2.Moving Epoch Calibration Rocket Oracle Circuit Lodge Ledger
open MS MS.Land MS.Menus MS.Rake MS.Dial MS.Tone MS.Logarithm YM.FVAAlt2 FormalOPE
open scoped Topology BigOperators Classical

variable {G : Gauge} {K : KernelChoices} {X : Type}
variable (Y : Oracle.Program K) (Z : ∀ b : Patch,b.Branches K G) (C : Run G)
variable (R : Lodge.Contract C Y Z) (t : X → ℕ) (ht : ∀ i, R.floor Y Z C ≤ t i)
local notation "track" => WilsonPhysicalExteriorRegulator.nativeTrack Y Z C R t ht
local notation "periods" => Period.Field.LodgeT.instance_real Y Z C R t ht
variable (F : Calibration.Tent (R.profile Y Z C t ht).entire)
variable {B : MS.Local.Physical.Deck G} (τ : Prescription B) {n : ℕ}

def residual (D : Fin n → Label B) (k : ℕ) (i : X) (m : ℕ) (z : X → Fin n → Cover) (u : ℝ) : ℂ :=
  PowerSeries.coeff k (Sound.Figure.runPer C Z periods z (Calibration.sheet F) m (track).stop D τ
    (u-(track).Θ i) (Sound.Alone track i) i) -
  PowerSeries.coeff k (Rocket.adjust (track).desk Y Z F (Lodge.basisR C) (track).stop D z τ
    (fun w => u-(track).Θ w) (Sound.Alone track) i)

private abbrev Sample := ℝ × ℝ × Sound.Formal.Episode (Fin n) C.family.labels ×
  Sound.Formal.Episode (Fin n) C.family.labels

private theorem nodes (D : Fin n → Label B) (k : ℕ) :
    ∃ m : ℕ, ∃ A : ℝ, 0≤A ∧ ∃ d : ℕ, ∀ i b z u E, 0≤E →
    (∀ j∈Finset.range m, ‖residual Y Z C R t ht F τ D k i b z (j:ℝ)‖≤E) →
      ‖residual Y Z C R t ht F τ D k i b z u‖≤ A*(1+|u|)^d*E := by
  let f := fun u (a : Sample (n:=n) C) =>
    PowerSeries.coeff k (Sound.Formal.dated τ (u-a.1) (Lodge.basisR C) D a.2.1 a.2.2.1) -
      PowerSeries.coeff k (Sound.Formal.dated τ (u-a.1) (Lodge.basisR C) D a.2.1 a.2.2.2)
  have hf : Ready f := (WilsonPhysicalExteriorFiniteLog.dated τ (Lodge.basisR C) D
    (fun a : Sample (n:=n) C => a.1) (fun a => a.2.1) (fun a => a.2.2.1) k).sub
    (WilsonPhysicalExteriorFiniteLog.dated τ (Lodge.basisR C) D (fun a : Sample (n:=n) C => a.1)
      (fun a => a.2.1) (fun a => a.2.2.2) k)
  obtain ⟨m,A,hA,d,hd⟩ := MSExteriorFiniteScales.finite_observations hf
  refine ⟨m,A,hA,d,fun i b z u E hE hg => ?_⟩
  let s : Sample (n:=n) C := ((track).Θ i,Sound.Alone track i,
    Sound.Figure.perRead C Z periods z (Calibration.sheet F) b ((track).stop.choose i),
    Sound.Figure.innerV C (B:=(track).desk) Z Y z F (track).stop i)
  have same (v : ℝ) : residual Y Z C R t ht F τ D k i b z v = f v s := rfl
  rw [same]
  exact hd s u E hE (fun j hj => (same j) ▸ hg j hj)

variable (r E : X → ℝ) (hE : ∀ i, 0<E i) (h N : ℕ)
local notation "Menu" => Sound.Ethos.MenuF B h

include hE in
/-- The actual finite soft-period array versus its authentic cover array.
The entire bounded set of independent native source positions may be specified
after the cutoff and period. There is no separation denominator in this step. -/
theorem infrared :
    ∃ σ : X→ℕ, ∃ A : ℝ, 0≤A ∧ ∃ d : ℕ, ∀ i b, σ i≤b →
    ∀ (D : Fin n → Menu) k, k≤N → ∀ z : X → Fin n → Cover, (∀ j,‖Tone.embed (z i j)‖≤r i) →
    ∀ u : ℝ, ‖residual Y Z C R t ht F τ (Sound.Ethos.owner ∘ D) k i b z u‖ ≤ A*(1+|u|)^d*E i := by
  let Key := (Fin n → Menu) × Fin (N+1)
  choose m A hA d hd using fun k : Key =>
    nodes Y Z C R t ht F τ (Sound.Ethos.owner ∘ k.1) k.2.val
  choose κ hκ using fun j : ℕ => Sound.Ethos.served (I:=Fin n) C Z Y periods F τ (track).stop
    (fun i=>(j:ℝ)-(track).Θ i) (Sound.Alone track) E h N r hE
  let M := ∑ k, m k
  let σ := fun i => ∑ j∈Finset.range M, κ j i
  let A₀ := ∑ k, A k
  let D₀ := ∑ k, d k
  refine ⟨σ,A₀,Finset.sum_nonneg (fun k _ => hA k),D₀,?_⟩
  intro i b hσ D k hk z hz u
  let key : Key := (D,⟨k,Nat.lt_succ_of_le hk⟩)
  have use (j : ℕ) (hj : j∈Finset.range (m key)) : κ j i≤b := by
    have hm : m key ≤ M := Finset.single_le_sum (f:=m) (fun k _ => Nat.zero_le _) (Finset.mem_univ key)
    exact (Finset.single_le_sum (f:=fun q=>κ q i) (fun _ _=>Nat.zero_le _)
      (Finset.mem_range.mpr ((Finset.mem_range.mp hj).trans_le hm))).trans hσ
  have got := hd key i b z u (E i) (hE i).le (fun j hj =>
    (hκ j).answers i b (use j hj) (Sound.Ethos.owner ∘ D)
      (fun w => Nat.le_of_lt_succ (D w).1.isLt) z hz k hk)
  have h₁ : A key ≤ A₀ := Finset.single_le_sum (f:=A) (fun k _=>hA k) (Finset.mem_univ key)
  have h₂ : d key ≤ D₀ := Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (Finset.mem_univ key)
  exact got.trans (mul_le_mul_of_nonneg_right (mul_le_mul h₁
    (pow_le_pow_right₀ (by linarith only [abs_nonneg u]) h₂) (by positivity) ((hA key).trans h₁)) (hE i).le)

end YM.Integration.WilsonPhysicalExteriorMovingPeriod
