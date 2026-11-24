import YM.Integration.WilsonTrueProjectedLocatedSalary

/-! Feed the literal signed filed column at each real site to the original
Wilson transfer. The weights come from the very same dated numerical
program and its own child itinerary. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedHistory
open Function Filter MeasureTheory Finset Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open FormalBulk08 City Pose PhysicalNext Repeat Legato RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedFiledTransfer WilsonTrueProjectedLocatedBasis
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {d D N p stop : ℕ}
local notation "C₀" => R.family
local notation "ι" => Letter (R.family.labels.level d)

def film {X : Type*} (vacuum : X → ℝ) (field : X → ℂ) (g : ℝ) (k : ℕ) (U : X) : ℂ :=
  ((g^k:ℝ):ℂ)*((vacuum U:ℂ)*field U)

theorem unscale {Q : ℕ} {X : Type*} (vacuum : X → ℝ) (f : Fin (Q+1) × ι → X → ℂ)
    (x : Fin (Q+1) → ι → ℂ) {g : ℝ} (positive : 0 < g) (U : X) :
    table (fun t : Fin (Q+1) × ι => film vacuum (f t) g t.1.val)
      (fun t => x t.1 t.2/(g^t.1.val:ℝ)) U =
      (vacuum U:ℂ)*weighted f (fun t => x t.1 t.2) U := by
  unfold table film weighted
  rw [mul_sum]
  refine sum_congr rfl (fun t _ => ?_)
  have h : ((g^t.1.val:ℝ):ℂ) ≠ 0 := by exact_mod_cast (pow_pos positive t.1.val).ne'
  field_simp

theorem all_fields {Q : ℕ} {T : Type*} (book : ι → T → ℂ) (x : Fin (Q+1) → ι → ℂ) (W : T) :
    ordinary R book x W = weighted (fun t : Fin (Q+1) × ι => book t.2) (fun t => x t.1 t.2) W := by
  change (∑ u, (∑ k, x k u)*book u W)=∑ t : Fin (Q+1) × ι, x t.1 t.2*book t.2 W
  rw [Fintype.sum_prod_type]
  simp only [sum_mul]
  rw [sum_comm]

theorem intake {Q : ℕ} {j : ℕ} (P : Rep G ((C₀).side j p)) (book : ι → Config G ((C₀).side j p) → ℂ)
    (paid : ∀ l, Integrable (fun W => (P.eval W:ℂ)*book l W) (prior G _))
    (x : Fin (Q+1) → ι → ℂ) :
    Integrable (fun W => (P.eval W:ℂ)*ordinary R book x W) (prior G _) := by
  let v (b : ι) := ∑ k, x k b
  have pts (U : Config G ((C₀).side j p)) : (P.eval U:ℂ)*ordinary R book x U =
      ∑ b, v b • ((P.eval U:ℂ)*book b U) := by
    simp only [ordinary,submitted,weighted,mul_sum,smul_eq_mul,v]
    exact sum_congr rfl (fun _ _ => mul_left_comm _ _ _)
  simp_rw [pts]
  exact integrable_finsetSum _ (fun b _ => (paid b).smul (v b))

def earnedValue (wood : Primer.Families R.family) (a : hue G) (depth : d<D)
    (digit : ∀ j, Site ((C₀).S.block j)) (N stop Q : ℕ) (g : ℕ → ℝ)
    (top : Fin (Q+1) → ι → ℂ) (W : ∀ j, Rep G ((C₀).side j p))
    (book : ∀ j, ι → Config G ((C₀).side j p) → ℂ) (j : ℕ) (U : Config G ((C₀).side j p)) : ℂ :=
  ((W j).eval U:ℂ)*WilsonTrueProjectedPointProgram.ordinary R (book j)
    (WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top j) U

def datedFee (wood : Primer.Families R.family) (a : hue G) (depth : d<D)
    (digit : ∀ j, Site ((C₀).S.block j)) (N stop Q : ℕ) (g : ℕ → ℝ)
    (top : Fin (Q+1) → ι → ℂ) (j : ℕ) (u : Fin (Q+1) → ι → ℝ) : ℝ :=
  ∑ k : Fin (Q+1), ∑ b : ι,
    (‖WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (j+1) k b‖/(g j)^k.val)*u k b

def nextWord (wood : Primer.Families R.family) (a : hue G) (depth : d<D)
    (digit : ∀ j, Site ((C₀).S.block j)) (N i Q : ℕ) (g : ℝ)
    (book : ι → Config G ((C₀).side i p) → ℂ) (k : Fin (Q+1)) (b : ι) : Config G ((C₀).side i p) → ℂ :=
  WilsonTrueProjectedFiledTransfer.submitted R book
    (fun l => WilsonTrueProjectedPointProgram.kept R wood a depth digit N i g (Q-k.val) l b)


/-- The two sides are evaluated with their full original Wilson vacua. The
local return has already been bought with the power on the same lower
date. Here it is removed exactly once from the numerical coefficients. -/
theorem sale {i Q : ℕ} (wood : Primer.Families R.family) (a : hue G) (depth : d<D)
    (digit : (j : ℕ) → Site (R.family.S.block j))
    (W : (j : ℕ) → Rep G (R.family.side j p))
    (book : (j : ℕ) → Letter (R.family.labels.level d) → Config G (R.family.side j p) → ℂ)
    (g : ℕ → ℝ) (top : Fin (Q+1) → Letter (R.family.labels.level d) → ℂ) (y : Site ((C₀).side i p)) (next : i<stop) (positive : 0<g i)
    {σ C Λ δ w : ℝ} (law : (W i).Lawful σ C Λ δ w) (anchor : ι)
    (u : Fin (Q+1) → ι → ℝ)
    (ready : ∀ b : Letter (R.family.labels.level d),Integrable (fun U => ((W (i+1)).eval U:ℂ)*book (i+1) b U) (prior G _))
    (funded : ∀ (k : Fin (Q+1)) (b : ι), ∃ z : store C₀ d p i, Paid R (d:=d) (p:=p) (i:=i) (W i) y z (u k b) ∧
      transition (C:=C₀) d N p i (film (W (i+1)).eval (book (i+1) b) (g i) k.val)=
        film (W i).eval (nextWord R (p:=p) wood a depth digit N i Q (g i) (book i) k b) (g i) k.val+z.density y ((C₀).localSection d) (W i)) :
    ∃ z : store C₀ d p i, Paid R (d:=d) (p:=p) (i:=i) (W i) y z (datedFee R wood a depth digit N stop Q g top i u) ∧
      transition (C:=C₀) d N p i (earnedValue R (p:=p) wood a depth digit N stop Q g top W book (i+1))=earnedValue R (p:=p) wood a depth digit N stop Q g top W book i+z.density y ((C₀).localSection d) (W i) := by
  classical
  let T := Fin (Q+1) × ι
  let f (t : T) := book (i+1) t.2
  let l (t : T) := nextWord R (p:=p) wood a depth digit N i Q (g i) (book i) t.1 t.2
  let x (t : T) := WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (i+1) t.1 t.2/((g i)^t.1.val:ℝ)
  have hf (t : T) : Integrable (film (W (i+1)).eval (f t) (g i) t.1.val) (prior G _) :=
    (ready t.2).const_mul _
  obtain ⟨z,pz,signed⟩ := WilsonTrueProjectedLocatedBasis.original R (d:=d) (N:=N) (p:=p) (i:=i) ((0 : Fin (Q+1)),anchor) (W i) y law
    (fun t : T => film (W (i+1)).eval (f t) (g i) t.1.val)
    (fun t : T => film (W i).eval (l t) (g i) t.1.val) (fun t : T => u t.1 t.2) x hf
    (fun t => funded t.1 t.2)
  have cost : (∑ t : T, ‖x t‖*u t.1 t.2) =
      ∑ k : Fin (Q+1), ∑ b, (‖WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (i+1) k b‖/(g i)^k.val)*u k b := by
    rw [Fintype.sum_prod_type]
    simp only [x,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg positive.le _)]
  rw [cost] at pz
  refine ⟨z,pz,?_⟩
  have upper : table (fun t : T => film (W (i+1)).eval (f t) (g i) t.1.val) x = earnedValue R (p:=p) wood a depth digit N stop Q g top W book (i+1) := by
    funext U
    exact (unscale R (W (i+1)).eval f (WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (i+1)) positive U).trans
      (congrArg (fun v : ℂ => ((W (i+1)).eval U:ℂ)*v) (all_fields R (book (i+1)) (WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (i+1)) U).symm)
  have lower : table (fun t : T => film (W i).eval (l t) (g i) t.1.val) x = earnedValue R (p:=p) wood a depth digit N stop Q g top W book i := by
    funext U
    change _ = ((W i).eval U:ℂ)*ordinary R (book i) (WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top i) U
    rw [previous R wood a depth digit N stop Q g top next]
    exact (unscale R (W i).eval l (WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (i+1)) positive U).trans (congrArg (fun v : ℂ => ((W i).eval U:ℂ)*v)
      (WilsonTrueProjectedPointProgram.lower R wood a depth digit N i Q (g i) (book i) (WilsonTrueProjectedPointProgram.income R wood a depth digit N stop Q g top (i+1)) U).symm)
  rwa [upper,lower] at signed

end YM.Integration.WilsonTrueProjectedLocatedHistory
