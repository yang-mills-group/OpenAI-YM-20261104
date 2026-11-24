import YM.Integration.WilsonOriginalReceivedFreshQ

/-! The original submitted curvature stencils pay the one larger exponent in
the second-step regular inventory. Their radii are fixed before the regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFreshQCover
open Function Filter Finset Lattice Wilson RG Marker Source Labels Push
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Affinity
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1 FullQLocal FullQLocal.RenderedStep
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureLamps
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p ℓ n : ℕ} {hn : n ≤ ℓ} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p ℓ n hn V)
  (labels : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ) (σ : ℝ) (extra : V → ℕ)
  {E : V → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
  (A : ∀ i, Set (E i)) (K : ∀ i, Submodule ℝ (E i))
  (P : Passport (R.family.side ℓ p) V) (old fresh : Finset V) (apart : Disjoint old fresh)
local notation "G₁" => WilsonOriginalProjectedCurvatureTableau.actors D
local notation "L₁" => (fun i => (WilsonOriginalProjectedCurvatureTableau.nulls D i).restrictScalars ℝ)
local notation "T₁" => WilsonMixedTestTableau.actors A G₁
local notation "t₁" => WilsonMixedTestTableau.right A G₁ fresh (WilsonOriginalMixedTestTableau.zero D)
local notation "J₀" => WilsonMixedPassportRows.passport (WilsonMixedPassportRows.owner P (paper D labels) old)
local notation "Y" => cohort Q D labels μ orders N σ extra
local notation "X" => WilsonOriginalRightBirthLamp.rows A G₁ Y P old fresh apart (WilsonOriginalMixedTestTableau.zero D)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N p ℓ
local notation "r₀" => ActualOriginalQLayout.rankCap R labels
local notation "toll" => WilsonOriginalProjectedCurvatureLoan.toll (R:=R) labels
local notation "v₀" => Fintype.card V*toll
local notation "head" => r₀+v₀+1

open WilsonMixedPassportRows
open private lengths from YM.Integration.WilsonMixedPassportRows

def span : ℕ := Finset.univ.sup (fun s : ActualOriginalQPackets.Row (R:=R) labels =>
  (paper D labels).height s.1.1 + extra s.1.1 + ActualOriginalQCharges.rowFall labels s)

def radius : ℕ := 1000 + (head) + Fintype.card V + span D labels extra

omit [DecidableEq V] in
theorem fixed (R : Run G) (J : Request V) (ℓ p : ℕ) (o : V → Site (R.family.side ℓ p)) :
    radius (ActualOriginalQPointSetup.pointDatum R J p ℓ o) labels extra =
      radius (ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _ => 0)) labels extra := rfl

omit [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)] in
theorem within (point : BudgetPoint) {w : V → ℝ} {c : ℝ}
    (book : Scene.Armada Y w (fun _ => toll) σ c r₀ (Fintype.card V) v₀)
    (i : Face Y fresh) : Lattice.coverNumber point.B ((X i).ground point) ≤ radius D labels extra := by
  have ranks : (X i).lamp.r ≤ (head) :=
    (Scene.Armada.degreeR (fun _ : V => toll) book.toMinistry (Y i.val) (book.purchases.usable i.val)).2.2
  have ht : (X i).length = (Y i.val).length :=
    lengths (owner P (paper D labels) old) (Y i.val)
      (fun _ hv => if_neg (fun ho => Finset.disjoint_left.mp apart ho (i.property hv))) t₁
  have given := (WilsonOriginalProjectedCurvatureRender.geometry Q D labels μ orders N i.val.1 σ
      (extra i.val.1.1.1) i.val.2).2.2
  have short : (X i).length ≤ span D labels extra := by
    rw [ht,show (Y i.val).length = _ from given]
    exact Finset.le_sup (f:=fun s : ActualOriginalQPackets.Row (R:=R) labels =>
      (paper D labels).height s.1.1 + extra s.1.1 + ActualOriginalQCharges.rowFall labels s) (Finset.mem_univ i.val.1)
  have count := (X i).mode.val.card_le_univ
  have tiles := (X i).tiles point.B point.B_pos
  apply Nat.le_of_mul_le_mul_left _ point.B_pos
  apply tiles.trans
  change _ ≤ point.B*(1000+(head)+Fintype.card V+span D labels extra)
  calc _ ≤ (1000+(head)+Fintype.card V)*point.B + span D labels extra * point.B := by
            apply Nat.add_le_add
            · exact Nat.mul_le_mul_right point.B (by omega)
            · exact short.trans (Nat.le_mul_of_pos_right _ point.B_pos)
       _ = _ := by ring

section raised
variable {T I : Type} {n₁:Side} {P₁:BudgetPoint} {origin : V → Site n₁} {C₁:Census V}
  (M:Lamps T I G P₁ origin C₁)
omit [Fintype V] in
theorem raised (w : V → ℝ) (pos : ∀ i, 0 < w i) {B₁ d : ℕ} {a price : ℝ}
    (purchase : M.Paid w B₁ a price) (cap : ∀ i, Lattice.coverNumber B₁ (M.ground i) ≤ d) :
    M.Paid w B₁ (a+1) (Real.exp (d:ℝ)*price) := by
  obtain ⟨f,hf,support,bill⟩ := purchase.budget
  refine ⟨f,hf,support,?_⟩
  intro x
  apply Push.AbsoluteSums.budget_mono (Push.AbsoluteSums.budget_scale (Real.exp_pos (d:ℝ)).le (bill x))
  · intro i
    split
    · exact mul_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (pos v).le) (hf i)) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    split
    · let c := (Lattice.coverNumber B₁ (M.ground i) : ℝ)
      change Poly.toll w (M.mode i)*f i*Real.exp ((a+1)*c) ≤ Real.exp (d:ℝ)*(Poly.toll w (M.mode i)*f i*Real.exp (a*c))
      have he : Real.exp c ≤ Real.exp (d:ℝ) := Real.exp_le_exp.mpr (Nat.cast_le.mpr (cap i))
      rw [add_mul,one_mul,Real.exp_add]
      have inc : 0 ≤ Poly.toll w (M.mode i)*f i*Real.exp (a*c) :=
        mul_nonneg (mul_nonneg (Finset.prod_nonneg fun v _ => (pos v).le) (hf i)) (Real.exp_pos _).le
      calc _ = Real.exp c*(Poly.toll w (M.mode i)*f i*Real.exp (a*c)) := by ring
           _ ≤ _ := mul_le_mul_of_nonneg_right he inc
    · rw [mul_zero]
end raised

end YM.Integration.WilsonOriginalFreshQCover
