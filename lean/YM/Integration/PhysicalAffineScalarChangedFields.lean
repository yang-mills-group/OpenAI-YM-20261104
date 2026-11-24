import YM.Integration.PhysicalAffineScalarRootContraction

/-! Simultaneous ordinary and single-forest estimates for rows and active
charges in the two physical Gaussian normal equations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarChangedFields
open Filter Function Set Matrix Lattice FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open ConditionalAffineLoadPrices PhysicalAffineScalarRootContraction
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c : Side} {ι κ : Type*} [Fintype ι] [Fintype κ]
local notation "E" => Vec G c 1
local notation "ray₀" => ray G c
local notation "D" => native c

/-- Both original choices use one ordinary budget. Their genuine difference
keeps the actual changed site at the same budget. -/
structure Pair (p : ι→Site c) (z : Site c) (δ C : ℝ) (n : ℕ) (F U : E→ι→ℝ) : Prop where
  left : Paid p δ C n F
  right : Paid p δ C n U
  change : Rooted p z δ C n (fun b => U b-F b)

namespace Pair
variable {p : ι→Site c} {q : κ→Site c} {z : Site c} {δ γ C M N V : ℝ} {n : ℕ} {F U H W : FreeResolvent.Vec G c 1 → ι → ℝ}

private theorem mono_root (h : Rooted p z δ C n F) (hCM : C≤M) : Rooted p z δ M n F :=
  ⟨h.smooth,fun l hl => (h.priced l hl).mono le_rfl hCM⟩

theorem mono_fee (h : Pair p z δ C n F U) (hCM : C≤M) : Pair p z δ M n F U :=
  ⟨h.left.weaken le_rfl hCM,h.right.weaken le_rfl hCM,mono_root h.change hCM⟩

/-- A common unprojected physical source carries exactly zero one-tree difference. -/
theorem same (h : Paid p δ C n F) (hC : 0≤C) : Pair p z δ C n F F := by
  refine ⟨h,h,?_⟩
  have e : (fun b => F b-F b) = (fun _ : E => (0 : ι→ℝ)) := funext fun b => sub_self _
  rw [e]
  refine ⟨contDiffAt_const,fun l _ => ?_⟩
  have h0 : jet ray₀ (column (fun _ : E => (0 : ι→ℝ))) l 0=0 := by
    cases l with
    | nil => rw [zeroth]; rfl
    | cons i l => exact jet_const ray₀ (i :: l) (by simp) (0 : Matrix ι Unit ℝ) 0
  rw [h0]; exact Mark.Rates.zero hC

theorem sum (h : Pair p z δ C n F U) (h' : Pair p z δ M n H W) :
    Pair p z δ (C+M) n (fun b => F b+H b) (fun b => U b+W b) := by
  refine ⟨h.left.sum h'.left,h.right.sum h'.right,?_⟩
  convert h.change.sum h'.change using 1
  ext b i; simp only [Pi.add_apply,Pi.sub_apply]; ring

theorem diff (h : Pair p z δ C n F U) (h' : Pair p z δ M n H W) :
    Pair p z δ (C+M) n (fun b => F b-H b) (fun b => U b-W b) := by
  refine ⟨h.left.diff h'.left,h.right.diff h'.right,?_⟩
  convert h.change.diff h'.change using 1
  ext b i; simp only [Pi.sub_apply]; ring

/-- Ordinary common cut/full/cut-minus-full Jacobian applied to both forests.
The same Schur fee transports its already changed input. -/
theorem action (h : Pair p z δ C n F U) (hC : 0≤C) {J : E→Matrix κ ι ℝ}
    (hJ : Bundle ray₀ (marks G c δ) D q p J 0 n γ M) (hM : 0≤M) (hδ : 0≤δ) (hγ : δ+n*δ≤γ) :
    Pair q z δ (2^n*(C*M)) n (fun b => J b *ᵥ F b) (fun b => J b *ᵥ U b) := by
  have hγ' : n*δ≤γ := by linarith
  refine ⟨h.left.action hC hJ hM hδ hγ',h.right.action hC hJ hM hδ hγ',?_⟩
  convert h.change.action hC hJ hM hδ hγ using 1
  ext b i; exact congrFun (Matrix.mulVec_sub (J b) (U b) (F b)).symm i

/-- A changed covariance contributes its original marked action on one
ordinary endpoint and its original ordinary action on the changed endpoint. -/
theorem inverse (h : Pair p z δ C n F U) (hC : 0≤C) {A B : E→Matrix ι ι ℝ} {d : ℝ}
    (hA : Bundle ray₀ (marks G c δ) D p p A 0 n γ M)
    (hB : Bundle ray₀ (marks G c δ) D p p B 0 n γ M)
    (hH : ∀ l : List (raw G c), l.length≤n → Lever.Here ray₀ D p hearth d γ z l N A B)
    (hM : 0≤M) (hN : 0≤N) (hδ : 0≤δ) (hd : δ≤d) (hγ : δ+n*δ≤γ)
    (hV : (native c).Volume p δ V) (hv : 0≤V) :
    Pair p z δ (2^n*(N*C*V)+2^n*(C*M)) n (fun b => A b *ᵥ F b) (fun b => B b *ᵥ U b) := by
  have hγ' : n*δ≤γ := by linarith
  have HC : 2^n*(C*M)≤2^n*(N*C*V)+2^n*(C*M) := le_add_of_nonneg_left (by positivity)
  refine ⟨(h.left.action hC hA hM hδ hγ').weaken le_rfl HC,
    (h.right.action hC hB hM hδ hγ').weaken le_rfl HC,?_⟩
  have hmarked := Rooted.inverse h.right hC hA.smooth hB.smooth hH hN hδ hd
    (by push_cast; nlinarith only [hγ]) hV hv
  have hother := h.change.action hC hA hM hδ hγ
  convert hmarked.sum hother using 1
  ext b i
  simp only [Pi.add_apply,Pi.sub_apply,Matrix.sub_mulVec,Matrix.mulVec_sub]
  abel

/-- Difference of the exact two rowwise products, with its true tag entering
each factor exactly once; this is the last contraction in a rooted square. -/
theorem changed_product (h : Pair p z δ C n F U) (h' : Pair p z δ M n H W) (hC : 0≤C) (hM : 0≤M) :
    Rooted p z δ (2^n*(C*M)+2^n*(M*C)) n (fun b i => U b i*W b i-F b i*H b i) := by
  have h₁ := h.change.product h'.right hC hM
  have h₂ := h'.change.product h.left hM hC
  convert h₁.sum h₂ using 1
  ext b i; simp only [Pi.sub_apply,Pi.add_apply]; ring

end Pair
end YM.Integration.PhysicalAffineScalarChangedFields
