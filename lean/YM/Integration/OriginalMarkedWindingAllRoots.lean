import YM.Integration.OriginalPhysicalWindingRows

/-! Transfer a true finite spatial bill at one presentation root to each
independently held source. Only a single positional sum appears, uniformly
in the number of independent nonlinear field and colour coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedWindingAllRoots
open Finset Lattice RG Wilson Gauge FreeResolvent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos
open PhysicalNext.Repeat.Legato PhysicalWilsonRootedHessian
open Marker LocalComparison PhysicalWilsonPricedOutput OriginalPhysicalWindingRows
open scoped BigOperators Classical

variable {ι Z : Type} [DecidableEq ι] [Fintype ι] [Fintype Z] {n : Side}

def account (D : (ι→Site n)→Z→ℕ) (q : (ι→Site n)→Z→ℝ) (w : ℝ) (o : ι) (u : Site n) :=
  ∑ p : ι→Site n, if p o=u then ∑ z,Real.exp (w*(D p z:ℝ))*q p z else 0

theorem host (u : Site n) {t : ℝ} (ht : 0<t) :
    (∑ a : Site n,Real.exp (-t*(separation u a:ℝ))) ≤ sheetPay (t/4) := by
  calc
    _ ≤ ∑ a : Site n,(taxi n).weight (-(t/4)) u a := by
      apply sum_le_sum
      intro a _
      apply Real.exp_monotone
      have h := mul_le_mul_of_nonneg_left (taxi_le_native u a) ht.le
      change t*(taxi n).d u a ≤ t*(4*(separation u a:ℝ)) at h
      linarith
    _ ≤ _ := taxi_volume u _ (by positivity)

theorem transfer (D : (ι→Site n)→Z→ℕ) (q : (ι→Site n)→Z→ℝ)
    (o w : ι) (u : Site n) {σ τ B : ℝ} (ht : τ<σ) (hp : ∀ p z,0≤q p z)
    (span : ∀ p z,separation (p w) (p o)≤D p z) (held : ∀ a,account D q σ o a≤B) :
    account D q τ w u ≤ sheetPay ((σ-τ)/4)*B := by
  let output (p : ι→Site n) := if p w=u then ∑ z, Real.exp (τ*(D p z:ℝ))*q p z else 0
  let fee (a : Site n) := Real.exp (-(σ-τ)*(separation u a:ℝ))
  have cost : 0≤B := (sum_nonneg (fun p _ => show 0≤(if p o=u then
    ∑ z,Real.exp (σ*(D p z:ℝ))*q p z else 0) from by
      split <;> first | exact sum_nonneg (fun z _ => mul_nonneg (Real.exp_pos _).le (hp p z)) | exact le_rfl)).trans (held u)
  have once (a : Site n) :
      (∑ p : ι→Site n, if p o=a then output p else 0) ≤ fee a*account D q σ o a := by
    unfold account
    rw [mul_sum]
    apply sum_le_sum
    intro p _
    by_cases ho : p o=a
    · by_cases hw : p w=u
      · simp only [output,ho,hw,if_true,mul_sum]
        apply sum_le_sum
        intro z _
        rw [←mul_assoc]
        apply mul_le_mul_of_nonneg_right _ (hp p z)
        rw [show fee a * Real.exp (σ*(D p z:ℝ)) =
          Real.exp (-(σ-τ)*(separation u a:ℝ) + σ*D p z) from (Real.exp_add _ _).symm]
        apply Real.exp_monotone
        have hd : (separation u a:ℝ)≤D p z := by exact_mod_cast (hw ▸ ho ▸ span p z)
        nlinarith only [mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr ht.le)]
      · simp only [output,hw,ho,if_true,if_false]
        exact mul_nonneg (Real.exp_pos _).le (sum_nonneg (fun z _ => mul_nonneg (Real.exp_pos _).le (hp p z)))
    · simp [ho]
  calc
    account D q τ w u = ∑ a : Site n, ∑ p : ι→Site n, if p o=a then output p else 0 := by
      rw [sum_comm]
      simp [account,output]
    _ ≤ ∑ a : Site n, fee a*B := sum_le_sum fun a _ =>
      (once a).trans (mul_le_mul_of_nonneg_left (held a) (Real.exp_pos _).le)
    _ = (∑ a : Site n, fee a)*B := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (host u (sub_pos.mpr ht)) cost

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} {S : Census V}
variable (T : Run G) (d : LocalFormal.Datum T.family S)
local notation "c" => T.family.side d.level d.period

omit [Fintype V] in
/-- A numerical buyer can hold any actual marked root while leaving the
signed function and its one presentation root fixed. -/
theorem marked {l : ℕ} (s : S.Mode) (o w : s.val) (u : Site (c)) {σ τ B : ℝ} (ht : τ<σ)
    (P : (s.val→Site (c))→(Fin l→Label G (c))→ℂ)
    (sold : ∀ a,markedHeld T d s o a σ P≤B) :
    markedHeld T d s w u τ P ≤ sheetPay ((σ-τ)/4)*B := by
  let dist (p : s.val→Site (c)) (z : Fin l→Label G (c)) :=
    span T d (univ.image p ∪ univ.image fun i => (z i).1)
  have width (p : s.val→Site (c)) (z : Fin l→Label G (c)) : separation (p w) (p o)≤dist p z := by
    let A := univ.image p ∪ univ.image fun i => (z i).1
    have both (v : s.val) : p v∈A := mem_union_left _ (mem_image.mpr ⟨v,mem_univ _,rfl⟩)
    exact (le_sup (f:=fun v => separation (p w) v) (both o)).trans
      (le_sup (f:=fun v => A.sup fun u => separation v u) (both w))
  exact transfer dist (fun p z => ‖P p z‖) o w u ht (fun _ _ => norm_nonneg _) width sold

end YM.Integration.OriginalMarkedWindingAllRoots
end
