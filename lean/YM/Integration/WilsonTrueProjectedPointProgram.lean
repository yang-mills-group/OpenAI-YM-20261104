import YM.Integration.WilsonTrueProjectedPointSale
import YM.Integration.WilsonNeutralPointCourse

/-! Numerical transport on the independent field actually filed at one child
of each original Wilson block. The dated product is truncated in total
coupling degree. Each real comparison uses that child's own incoming film. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedPointProgram
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PowerSeries PhysicalNext Repeat Legato Graces Roost Org
open WilsonTrueProjectedFiledSource WilsonTrueProjectedFiledTransfer
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (R : Run G) {d D : ℕ}
local notation "ι" => Letter (R.family.labels.level d)
variable (wood : Primer.Families R.family) (a : hue G) (depth : d < D)
    (digit : ∀ i, Site (R.family.S.block i))
local notation "A" => WilsonNeutralPointCourse.transfer R wood a depth digit
local notation "deg" => WilsonTrueProjectedFiledGrades.degree

def term (N j : ℕ) (g : ℝ) (n : ℕ) (u b : ι) : ℂ :=
  ((g^n*coeff n (A N j u b) : ℝ) : ℂ)

def kept (N j : ℕ) (g : ℝ) (q : ℕ) (u b : ι) : ℂ :=
  ∑ n : Fin (q+1), term R wood a depth digit N j g n.val u b

def layer (N j q : ℕ) (g : ℝ) (x : Fin (q+1) → ι → ℂ) (e : Fin (q+1)) (u : ι) : ℂ :=
  ∑ k : Fin (q+1), ∑ n : Fin (q-k.val+1),
    if e = deg k n then moved R (term R wood a depth digit N j g n.val) (x k) u else 0

theorem total (N j q : ℕ) (g : ℝ) (x : Fin (q+1) → ι → ℂ) (u : ι) :
    (∑ e, layer R wood a depth digit N j q g x e u) =
      ∑ k : Fin (q+1), moved R (kept R wood a depth digit N j g (q-k.val)) (x k) u := by
  unfold layer
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,moved,kept,Finset.mul_sum]
  rw [Finset.sum_comm]

def walk (N q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) :
    ℕ → ℕ → Fin (q+1) → ι → ℂ
  | 0,_ => top
  | n+1,j => layer R wood a depth digit N j q (g j)
      (walk N q g top n (j+1))

def income (N stop q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) (j : ℕ) :=
  walk R wood a depth digit N q g top (stop-j) j

theorem previous (N stop q : ℕ) (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ) {j : ℕ} (h : j < stop) :
    income R wood a depth digit N stop q g top j = layer R wood a depth digit N j q (g j)
      (income R wood a depth digit N stop q g top (j+1)) := by
  unfold income
  rw [show stop-j=stop-(j+1)+1 by omega]
  rfl

def ordinary {T : Type*} {q : ℕ} (book : ι → T → ℂ) (x : Fin (q+1) → ι → ℂ) :=
  submitted R book (fun u => ∑ k, x k u)

private theorem split {T X : Type*} [Fintype T] (book : ι → X → ℂ) (c : T → ι → ℂ) (W : X) :
    submitted R book (fun u => ∑ k, c k u) W = ∑ k, submitted R book (c k) W := by
  simp only [submitted,weighted,Finset.sum_mul]
  rw [Finset.sum_comm]

theorem lower {X : Type*} (N j q : ℕ) (g : ℝ) (book : ι → X → ℂ)
    (x : Fin (q+1) → ι → ℂ) (W : X) :
    ordinary R book (layer R wood a depth digit N j q g x) W =
      weighted (fun t : Fin (q+1) × ι =>
        submitted R book (fun u => kept R wood a depth digit N j g (q-t.1.val) u t.2))
        (fun t => x t.1 t.2) W := by
  unfold ordinary
  simp only [total]
  rw [split]
  unfold weighted
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun k _ => relocated R book _ (x k) W

theorem original {N stop j p q : ℕ} (g : ℕ → ℝ) (top : Fin (q+1) → ι → ℂ)
    (Ψ : ∀ j, Rep G (R.family.side j p)) {σ C Λ δ w : ℝ} (law : (Ψ j).Lawful σ C Λ δ w)
    (next : j < stop) (cut : stop ≤ N)
    (fineEq : (Ψ (j+1)).eval = (R.family.path.rep N p (j+1)).eval)
    (lowerEq : (Ψ j).eval = (R.family.path.rep N p j).eval)
    (book : ∀ i, ι → Config G (R.family.side i p) → ℂ) (anchor : ι)
    (emitted : Fin (q+1) → ι → Config G (R.family.side j p) → ℂ)
    (u v : Fin (q+1) → ι → ℝ)
    (paid : ∀ k b, Paid R (d:=d) (N:=N) Ψ (WilsonTrueProjectedPointSale.charged R d (book (j+1) b))
      (emitted k b) (submitted R (book j) (fun s => kept R wood a depth digit N j (g j) (q-k.val) s b))
      (u k b) (v k b))
    (intake : ∀ b, Integrable (fun W => ((Ψ (j+1)).eval W : ℂ)*book (j+1) b W) (prior G _)) :
    let x := income R wood a depth digit N stop q g top
    let F := fun i W => ((Ψ i).eval W : ℂ)*ordinary R (book i) (x i) W
    WilsonTrueProjectedDualHistory.Signed R (d:=d) (N:=N) Ψ F j
      (∑ k, ∑ b, ‖x (j+1) k b‖*(u k b+v k b)) := by
  intro x F
  let T := Fin (q+1) × ι
  let fields (t : T) := book (j+1) t.2
  let rows (t : T) := submitted R (book j)
    (fun s => kept R wood a depth digit N j (g j) (q-t.1.val) s t.2)
  let weight (t : T) := x (j+1) t.1 t.2
  have sale := WilsonTrueProjectedPointSale.original R Ψ law (next.le.trans cut)
    fineEq lowerEq ((0 : Fin (q+1)),anchor) fields (fun t : T => emitted t.1 t.2) rows
    (fun t : T => u t.1 t.2) (fun t : T => v t.1 t.2) weight
    (fun t => paid t.1 t.2) (fun t => intake t.2)
  rw [Fintype.sum_prod_type] at sale
  obtain ⟨e,admitted,cap,report⟩ := sale
  refine ⟨e,admitted,cap,?_⟩
  rw [fine,coarse] at report
  have finer : F (j+1) = fun W => ((Ψ (j+1)).eval W : ℂ)*weighted fields weight W := by
    funext W
    dsimp only [F]
    congr 1
    change submitted R (book (j+1)) (fun b => ∑ k, x (j+1) k b) W =
      ∑ t : Fin (q+1) × ι, x (j+1) t.1 t.2 * book (j+1) t.2 W
    rw [split,Fintype.sum_prod_type]
    rfl
  have coarser : F j = fun W => ((Ψ j).eval W : ℂ)*weighted rows weight W := by
    funext W
    dsimp only [F]
    congr 1
    rw [show x j = _ from previous R wood a depth digit N stop q g top next]
    exact lower R wood a depth digit N j q (g j) (book j) (x (j+1)) W
  rwa [finer,coarser]

end YM.Integration.WilsonTrueProjectedPointProgram
