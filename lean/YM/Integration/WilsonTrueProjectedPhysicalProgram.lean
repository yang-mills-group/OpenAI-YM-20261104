import YM.Integration.WilsonTrueProjectedDatedProgram

/-! A finite chronology of group fields on the original Wilson representation.
The density at each shared date has one engineering normalization, one
numerical coefficient vector and one registered basis on the actual group. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPhysicalProgram
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PhysicalNext Repeat Legato Graces Roost Org
open WilsonTrueProjectedDualHistory WilsonTrueProjectedFiledTransfer WilsonTrueProjectedDatedProgram
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d D p : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "𝓒" => R.family

def density (m q : ℕ) (Ψ : ∀ j, RG.Rep G ((𝓒).side j p))
    (book : ∀ j, ι → Config G ((𝓒).side j p) → ℂ)
    (X : ℕ → Fin (q+1) → ι → ℂ) : Spaces R p :=
  fun j W => (mesh R d m j : ℂ) * ((Ψ j).eval W : ℂ) *
    (∑ k, submitted R (book j) (X j k) W)

theorem sum_grades {T : Type*} [Fintype T] {j : ℕ} (book : ι → Config G ((𝓒).side j p) → ℂ)
    (x : T → ι → ℂ) (W : Config G ((𝓒).side j p)) :
    (∑ k, submitted R book (x k) W) = submitted R book (fun u => ∑ k, x k u) W := by
  unfold submitted weighted
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem incoming {T : Type*} [Fintype T] (i : ℕ)
    (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) (book : ι → Config G ((𝓒).side (i+1) p) → ℂ)
    (x : T → ι → ℂ) (W : Config G ((𝓒).side (i+1) p)) :
    (∑ k, submitted R (fun b =>
      WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (book b)) (x k) W) =
      ((((𝓒).S.block i).val : ℂ)^d)⁻¹ * ((Ψ (i+1)).eval W : ℂ) *
        (∑ k, submitted R book (x k) W) := by
  unfold submitted weighted WilsonMeasuredOriginalColumnTransition.upper
  simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring

private theorem change_units {i N : ℕ} (Ψ : ∀ j, RG.Rep G ((𝓒).side j p))
    {σ C Λ δ w : ℝ} (law : (Ψ i).Lawful σ C Λ δ w)
    (F V : Spaces R p) {bill : ℝ} (s : ℂ)
    (step : WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ V i bill)
    (source : Integrable (V (i+1)) (prior G _))
    (fine : F (i+1) = fun W => s*V (i+1) W) (coarse : F i = fun W => s*V i W) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i (‖s‖*bill) := by
  have out := combine R Ψ law Unit.unit (fun _ => V) (fun _ => bill) (fun _ => step)
    (fun _ => source) (fun _ => s) F
  apply (by simpa only [Fintype.sum_unique] using out : _)
  · rw [fine]
    funext W
    change s*V (i+1) W = ∑ _b : Unit, s*V (i+1) W
    simp
  · rw [coarse]
    funext W
    change s*V i W = ∑ _b : Unit, s*V i W
    simp

theorem original (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) {σ C Λ δ w : ℝ}
    (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D) (N m b q i : ℕ)
    (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) (live : i < b) (cut : b ≤ N)
    (law : (Ψ i).Lawful σ C Λ δ w)
    (fineEq : (Ψ (i+1)).eval = (R.family.path.rep N p (i+1)).eval)
    (coarseEq : (Ψ i).eval = (R.family.path.rep N p i).eval)
    (book : ∀ j, ι → Config G ((𝓒).side j p) → ℂ)
    (emitted : Fin (q+1) → ι → Config G ((𝓒).side i p) → ℂ)
    (u v : Fin (q+1) → ι → ℝ)
    (paid : ∀ k t, WilsonTrueProjectedFiledSource.Paid R (d:=d) (N:=N) Ψ
      (book (i+1) t) (emitted k t)
      (submitted R (book i) (fun z => matrix R a wood depth N i (q-k.val) (g i) z t)) (u k t) (v k t))
    (intake : ∀ t, Integrable (WilsonMeasuredOriginalColumnTransition.upper R (d:=d)
      (Ψ (i+1)) (book (i+1) t)) (prior G _)) (anchor : ι) :
    let X := income R a wood depth N b q g top
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (density R m q Ψ book X) i
      (mesh R d m i * ∑ k : Fin (q+1), ∑ t, ‖X (i+1) k t‖*(u k t+v k t)) := by
  dsimp only
  let X := income R a wood depth N b q g top
  let f (W : Config G ((𝓒).side (i+1) p)) := ∑ k, submitted R (fun t =>
    WilsonMeasuredOriginalColumnTransition.upper R (d:=d) (Ψ (i+1)) (book (i+1) t)) (X (i+1) k) W
  let lower := WilsonTrueProjectedFiledGrades.layer R a wood depth N i q (g i) (X (i+1))
  let c (W : Config G ((𝓒).side i p)) := ((Ψ i).eval W : ℂ) * submitted R (book i) (fun t => ∑ e, lower e t) W
  let raw := WilsonTrueProjectedFiledSource.edge R f c
  have step := WilsonTrueProjectedFiledSource.original R Ψ law (live.le.trans cut) fineEq coarseEq
    a wood depth q (g i) (book (i+1)) (book i) emitted u v paid intake anchor (X (i+1))
    raw (WilsonTrueProjectedFiledSource.fine R ..) (WilsonTrueProjectedFiledSource.coarse R ..)
  have source : Integrable (raw (i+1)) (prior G _) := by
    rw [show raw (i+1)=f from WilsonTrueProjectedFiledSource.fine R ..]
    unfold f submitted weighted
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun t _ =>
      (intake t).const_mul (X (i+1) k t)
  have fee : ‖(mesh R d m i : ℂ)‖ = mesh R d m i := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    exact pow_nonneg (div_nonneg ((𝓒).S.a_pos _).le ((𝓒).S.a_pos _).le) _
  rw [←fee]
  apply change_units R Ψ law (density R m q Ψ book X) raw (mesh R d m i : ℂ) step source
  · funext W
    change (mesh R d m (i+1) : ℂ) * _ * _ = _ * raw (i+1) W
    rw [show raw (i+1)=f from WilsonTrueProjectedFiledSource.fine R ..]
    unfold f
    rw [incoming R, next_mesh]
    push_cast
    ring
  · funext W
    change (mesh R d m i : ℂ) * _ * _ = _ * raw i W
    rw [show raw i=c from WilsonTrueProjectedFiledSource.coarse R ..]
    unfold c
    rw [sum_grades R]
    have here : X i=lower := previous R a wood depth N b q g top live
    rw [here]
    ring

end YM.Integration.WilsonTrueProjectedPhysicalProgram
