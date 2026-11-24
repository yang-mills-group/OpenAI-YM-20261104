import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.RingTheory.PowerSeries.Basic
import YM.Gauge.Chart
/-!
# Bare coefficient computation on one real germ

`Writes` certifies ordinary coefficients separately at any finite order.
No analyticity or convergence is inferred. The convolution orientation
is fine for noncommutative products (holonomies).
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG06.Weak
open scoped Topology ContDiff BigOperators Classical
open Finset Function
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- `F n` is the nth ordinary coefficient at zero (not derivative value). -/
structure Writes (f : ℝ → E) (F : ℕ → E) : Prop where
  smooth : ContDiffAt ℝ ∞ f 0
  coeff (n : ℕ) : ((n.factorial:ℝ)⁻¹ • iteratedDeriv n f 0)=F n

def seed {I : Type*} [Zero I] (x : I) (n : ℕ) : I := if n=0 then x else 0

theorem Writes.constant (x : E) : Writes (fun _ : ℝ=>x) (seed x) where
  smooth := contDiffAt_const
  coeff n := by rw [iteratedDeriv_const]; cases n <;> simp [seed]

variable {f g : ℝ→E} {F H : ℕ→E}
theorem Writes.origin (h : Writes f F) : F 0=f 0 := by simpa using (h.coeff 0).symm

theorem Writes.nice (h : Writes f F) (n : ℕ) : ContDiffAt ℝ (n : ℕ) f 0 :=
  h.smooth.of_le (WithTop.coe_le_coe.mpr le_top)

theorem Writes.plus (h : Writes f F) (v : Writes g H) : Writes (f+g) (F+H) := {
  smooth := h.smooth.add v.smooth
  coeff n := by rw [iteratedDeriv_add (h.nice n) (v.nice n), smul_add,h.coeff, v.coeff]; rfl }

theorem Writes.minus (h : Writes f F) (v : Writes g H) : Writes (f-g) (F-H) := {
  smooth := h.smooth.sub v.smooth
  coeff n := by rw [iteratedDeriv_sub (h.nice n) (v.nice n), smul_sub,h.coeff, v.coeff]; rfl }

theorem Writes.apply (L : E→L[ℝ]D) (h : Writes f F) : Writes (L ∘ f) (L ∘ F) := {
  smooth := L.contDiff.contDiffAt.comp (0:ℝ) h.smooth
  coeff n := by
    have hv := L.iteratedFDeriv_comp_left (n:=↑(n:ℕ∞)) (h.nice n) (i:=n) (by rfl)
    rw [iteratedDeriv_eq_iteratedFDeriv, hv]
    change (↑n.factorial:ℝ)⁻¹ • L ((iteratedFDeriv ℝ n f 0) _)=_
    rw [← L.map_smul, ← iteratedDeriv_eq_iteratedFDeriv, h.coeff]; rfl }

theorem Writes.linear [FiniteDimensional ℝ E] (L : E→ₗ[ℝ]D) (h : Writes f F) : Writes (L ∘ f) (L ∘ F) :=
  Writes.apply L.toContinuousLinearMap h

theorem Writes.scale (x : ℝ) (h : Writes f F) : Writes (x • f) (x • F) :=
  h.apply (x • (ContinuousLinearMap.id ℝ E))

theorem Writes.collect {ι : Type*} {g : ι→ℝ→E} {H : ι→ℕ→E} (s : Finset ι)
    (h : ∀ i∈s,Writes (g i) (H i)) : Writes (∑ i∈s,g i) (∑ i∈s,H i) := by
  induction s using Finset.induction_on with
  | empty=>
    rw [Finset.sum_empty,Finset.sum_empty]
    rw [show (0:ℕ→E)=seed 0 from funext fun n=> by simp [seed]]
    exact Writes.constant 0
  | @insert i s he ih=>
    rw [Finset.sum_insert he,Finset.sum_insert he]
    exact (h _ (Finset.mem_insert_self ..)).plus (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))

theorem Writes.weightedSum {ι : Type*} {g : ι→ℝ→E} {H : ι→ℕ→E} (s : Finset ι) (x : ℝ)
    (h : ∀ i∈s,Writes (g i) (H i)) : Writes (fun t => x • ∑ i∈s,g i t) (fun n => x • ∑ i∈s,H i n) := by
  simp_rw [← Finset.sum_apply]; exact Writes.scale x (Writes.collect s h)

section pi
variable {ι : Type*} [Fintype ι] {Es : ι→Type*} [(i:ι)→NormedAddCommGroup (Es i)] [(i:ι)→NormedSpace ℝ (Es i)]
theorem Writes.pack {f : ℝ→Π i,Es i} {F : ℕ→Π i,Es i} (h : ∀ i,Writes (fun t=>f t i) (fun n=>F n i)) : Writes f F := by
  refine ⟨contDiffAt_pi.mpr fun i => (h i).smooth,?_⟩
  have he : ContDiffAt ℝ ∞ f 0 := contDiffAt_pi.mpr fun i => (h i).smooth
  intro n; funext i
  let L := (ContinuousLinearMap.proj (R:=ℝ) (φ:=Es) i)
  have hw := (show Writes f _ from { smooth :=he, coeff:=fun _=>rfl } ).apply L
  exact (hw.coeff n).symm.trans ((h i).coeff n)
end pi

theorem factorial_rule {n i : ℕ} (h : i ≤ n) : (n.factorial : ℝ)⁻¹ * (n.choose i :ℝ)=
    (i.factorial:ℝ)⁻¹ * ((n-i).factorial:ℝ)⁻¹ := by
  have he : (n.choose i :ℝ)*(i.factorial:ℝ)*((n-i).factorial:ℝ)=(n.factorial:ℝ):= by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  field_simp; linarith only [he]

/-- List-free convolution; second input on the right. -/
def join {S : Type*} [AddCommMonoid S] [Mul S] (F H : ℕ → S) (n : ℕ) :=
  ∑ p∈Finset.antidiagonal n,F p.1 * H p.2
theorem join_range {S : Type*} [AddCommMonoid S] [Mul S] (F H : ℕ → S) (n) :
    join F H n = ∑ i∈Finset.range (n+1), F i * H (n-i) :=
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j=> F i*H j) n

variable {S : Type*} [NormedRing S] [NormedAlgebra ℝ S]
theorem Writes.times {f g : ℝ→ S} {F H : ℕ→S} (h : Writes f F) (u : Writes g H) : Writes (f*g) (join F H) where
  smooth := h.smooth.mul u.smooth
  coeff n := by
    rw [iteratedDeriv_mul (h.nice n) (u.nice n),join_range, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i hi=>?_
    rw [← h.coeff,← u.coeff,← nsmul_eq_mul,← Nat.cast_smul_eq_nsmul ℝ, smul_mul_assoc, smul_smul, factorial_rule (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
      smul_mul_assoc, mul_smul_comm,smul_smul]

def WritesPS (f : ℝ→ S) (F : PowerSeries S) := Writes f (fun n=> PowerSeries.coeff n F)

theorem Writes.ps {f : ℝ→ S} {F : ℕ→S} (h : Writes f F) : WritesPS f (PowerSeries.mk F) := by
  unfold WritesPS; simpa only [PowerSeries.coeff_mk] using h

theorem WritesPS.times {f g : ℝ→ S} {F H : PowerSeries S} (h : WritesPS f F) (u : WritesPS g H) : WritesPS (f*g) (F*H) := by
  unfold WritesPS; simp_rw [PowerSeries.coeff_mul]; exact Writes.times h u

theorem WritesPS.plus {f g : ℝ→ S} {F H : PowerSeries S} (h : WritesPS f F) (u : WritesPS g H) : WritesPS (f+g) (F+H) := by
  -- coeff is linear for AddMonoid
  unfold WritesPS; simp_rw [map_add]; exact Writes.plus h u

theorem WritesPS.constant (x : S) : WritesPS (fun _ : ℝ=>x) (PowerSeries.C x) := by
  unfold WritesPS; simp_rw [PowerSeries.coeff_C]; convert Writes.constant x using 1; funext n; simp [seed]

end YM.RG06.Weak
