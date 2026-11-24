import YM.Integration.WilsonTrueProjectedFiledTransfer

/-! Keep the coupling grades of the original finite field program through a
shared date. A grade k entering that date has exactly order Q-k remaining. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedFiledGrades
open Function Filter Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PowerSeries PhysicalNext Repeat Legato Graces Roost
open WilsonTrueProjectedDualHistory WilsonTrueProjectedFiledTransfer
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d D N p i : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
local notation "𝓒" => R.family

def degree {q : ℕ} (k : Fin (q+1)) (ν : Fin (q-k.val+1)) : Fin (q+1) :=
  ⟨k.val+ν.val,by have := ν.isLt; have := k.isLt; omega⟩

def coefficient (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N i n : ℕ) (g : ℝ) (u b : ι) : ℂ :=
  ((g^n*coeff n (Primer.fieldStep (𝓒) a wood depth N i u b) : ℝ) : ℂ)

/-- The product on the dated angular program is truncated in total degree.
The field and addressed test axes remain on each retained coefficient. -/
def layer (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N i q : ℕ) (g : ℝ) (x : Fin (q+1) → ι → ℂ) (e : Fin (q+1)) (u : ι) : ℂ :=
  ∑ k : Fin (q+1), ∑ ν : Fin (q-k.val+1),
    if e = degree k ν then moved R (coefficient R a wood depth N i ν.val g) (x k) u else 0

theorem total (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D)
    (N i q : ℕ) (g : ℝ) (x : Fin (q+1) → ι → ℂ) (u : ι) :
    (∑ e, layer R a wood depth N i q g x e u) =
      ∑ k : Fin (q+1), moved R (matrix R a wood depth N i (q-k.val) g) (x k) u := by
  unfold layer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,moved,matrix,coefficient,Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem evaluated {X : Type*} (columns : ι → X → ℂ) {T : Type*} [Fintype T]
    (weights : T → ι → ℂ) (W : X) :
    submitted R columns (fun b => ∑ t, weights t b) W = ∑ t, submitted R columns (weights t) W := by
  simp only [submitted,weighted,Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A single measured original return receives all coupling grades. The
uncompensated hard rows on the shared vacuum are summed at their real keys. -/
theorem original (Ψ : ∀ j, RG.Rep G ((𝓒).side j p)) {σ C Λ δ w : ℝ}
    (law : (Ψ i).Lawful σ C Λ δ w)
    (a : hue G) (wood : Primer.Families (𝓒)) (depth : d < D) (q : ℕ) (g : ℝ)
    (columns : Fin (q+1) → ι → Spaces R p) (basis : ι → Config G ((𝓒).side i p) → ℂ)
    (bills : Fin (q+1) → ι → ℝ)
    (receipts : ∀ k b, WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (columns k b) i (bills k b))
    (intake : ∀ k b, Integrable (columns k b (i+1)) (prior G _))
    (reused : ∀ k b, columns k b i =
       submitted R basis (fun u => matrix R a wood depth N i (q-k.val) g u b))
    (anchor : ι) (x : Fin (q+1) → ι → ℂ) (F : Spaces R p)
    (upper : F (i+1) = fun W => ∑ k, submitted R (fun b => columns k b (i+1)) (x k) W)
    (lower : F i = submitted R basis (fun b => ∑ e, layer R a wood depth N i q g x e b)) :
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F i
      (∑ k : Fin (q+1), ∑ b, ‖x k b‖*bills k b) := by
  let family (k : Fin (q+1)) (j : ℕ) : Config G ((𝓒).side j p) → ℂ :=
    submitted R (fun b => columns k b j) (x k)
  let cost (k : Fin (q+1)) := ∑ b, ‖x k b‖*bills k b
  have step (k : Fin (q+1)) : WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ (family k) i (cost k) := by
    apply WilsonTrueProjectedFiledTransfer.original R Ψ law a wood depth (q-k.val) g (columns k)
      basis (bills k) (receipts k) (intake k) (reused k) anchor (x k) (family k) rfl
    funext W
    simpa only [family,submitted,weighted,reused] using
      (relocated R basis (matrix R a wood depth N i (q-k.val) g) (x k) W).symm
  have integral (k : Fin (q+1)) : Integrable (family k (i+1)) (prior G _) := by
    unfold family submitted weighted
    exact integrable_finsetSum _ (fun b _ => (intake k b).const_mul (x k b))
  have one := WilsonTrueProjectedFiledTransfer.combine R Ψ law (0 : Fin (q+1)) family cost step integral
    (fun _ => (1:ℂ)) F
  have top : F (i+1) = weighted (fun k => family k (i+1)) (fun _ => 1) := by
    rw [upper]
    funext W
    simp only [weighted,one_mul,family]
  have bottom : F i = weighted (fun k => family k i) (fun _ => 1) := by
    rw [lower]
    funext W
    simp_rw [total R a wood depth N i q g x]
    rw [evaluated]
    simp only [weighted,one_mul,family]
    exact Finset.sum_congr rfl fun k _ => by
      simpa only [submitted,weighted,reused] using
        relocated R basis (matrix R a wood depth N i (q-k.val) g) (x k) W
  simpa only [norm_one,one_mul,cost] using one top bottom

end YM.Integration.WilsonTrueProjectedFiledGrades

