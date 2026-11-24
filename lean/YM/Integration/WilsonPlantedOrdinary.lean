import YM.Integration.WilsonPlantedOrdinaryRoster

/-! The ordinary polynomial of the precomputed group words, including
every partition, is a source on this Wilson representation itself. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPlantedOrdinary
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureRegularAtoms WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftRoster
open WilsonRootedKioskOccupiedSlip Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] {R : Census V}
    {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}

open WilsonCapturedPrimarySoftMount (cost)
theorem partition [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (q : (parts R).Mode) (admitted : q∈shards R s) (y : Site n) (Z : Support n) (hold : y∈Z)
    (landing : ∀j∈s.val,o j∈Z) (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C)
    {D : ℝ} (gross : Gross L w P.p.B (P.p.supportExponent+2) D)
    {σ E Λ δ κ v μ : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (cartage P.p Y S μ v κ (cost P.p Z w C rad q+tariff P.p Z w D q) 0)
      (fun U=>(P.eval U:ℂ)*∏ t∈q.val,(bare L x U).part t.val) := by
  let J := Fin q.val.card
  let A := Rows L (block q)
  let sets (a : A) (j : J) := (a j).val
  let T (a : A) := domain L univ (sets a) Z
  let f (a : A) := nominal L univ (sets a) x
  let ranks (j : J) := o (root q j)
  have width : 0 ≤ P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  have head (j:J):o (root q j)∈Z:=landing _ (inside q admitted j)
  obtain ⟨e,ep,caps,book⟩:=WilsonCapturedPrimarySoftRoster.original L (block q) (root q) (seated q) Z head w hw width paid
  obtain ⟨b,bp,capb,grossBook⟩:=WilsonPlantedOrdinaryRoster.original L (block q) (root q) (seated q) Z head w hw width gross
  let en (a:A):=stage P.p rad (univ:Finset J)*∏j,e (sets a j)
  let bn (a:A):=∏j,b (sets a j)
  have g (a:A) := WilsonCenteredCaptureRegularAtoms.original L univ (sets a) x Z y ranks rad
    (fun j _=>near _ (inside q admitted j)) e
    (fun j _=>caps _ x (ranks j) (L.roots _ _ ((a j).property.symm ▸ seated q j)))
  have full (a:A) (U:Config G n) : ‖f a U‖ ≤ bn a := by
    simp only [f,nominal,Finset.prod_apply,norm_prod,bn]
    exact prod_le_prod (fun j _=>norm_nonneg _) (fun j _=>capb _ _ _)
  have reg : SumBudget (fun a=>reservedMass P.p (T a) (en a)) (cost P.p Z w C rad q) := by
    convert budget_scale (zero_le_one.trans (funded P.p rad (univ:Finset J))) book using 1
    funext a
    unfold en reservedMass
    ring
    rfl
  have raw : SumBudget (fun a=>reservedMass P.p (T a) (bn a)) (tariff P.p Z w D q) := by
    convert grossBook using 1
    funext a
    dsimp only [T,bn,sets,reservedMass];ring
    rfl
  obtain ⟨h,fmt,rem,entry⟩:=WilsonPlantedGroupWords.mounted P y T f (fun a=>mem_union_left _ hold)
    (fun a=>(g a).1) en bn (fun a=>(g a).2.1.1) (fun a=>prod_nonneg fun _ _=>bp _)
    (fun a=>(g a).2.1) full reg raw S Y K law reader div hv room
  refine ⟨h,fmt,rem,fun U=>?_⟩
  change h.density y S P U=(P.eval U:ℂ)*∏t∈q.val,(bare L x U).part t.val
  rw [entry U,←enumerate q (fun t=>(bare L x U).part t)]
  exact congrArg ((P.eval U:ℂ)*·) (WilsonPlantedOrdinaryRoster.full L x (block q) U w hw width gross).tsum_eq

def fare (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (C D : ℝ) (rad : ℕ)
    (S : SectionData F) (Y : Hol G) (μ v κ : ℝ) (s : R.Mode) :=
  ∑q∈shards R s,cartage p Y S μ v κ (cost p Z w C rad q+tariff p Z w D q) 0

theorem original [Fintype V] [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (y : Site n) (Z : Support n) (hold : y∈Z) (landing : ∀j∈s.val,o j∈Z)
    (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C)
    {D : ℝ} (gross : Gross L w P.p.B (P.p.supportExponent+2) D)
    {σ E Λ δ κ v μ : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p Z w C D rad S Y μ v κ s) (fun U=>(P.eval U:ℂ)*(Poly.pass (bare L x U)).part s) := by
  let Q (q : (parts R).Mode) (U : Config G n) := (P.eval U:ℂ)*∏t∈q.val,(bare L x U).part t.val
  let bill (q : (parts R).Mode) := cartage P.p Y S μ v κ (cost P.p Z w C rad q+tariff P.p Z w D q) 0
  have gather (I : Finset (parts R).Mode) (valid : I⊆shards R s) :
      Store P S Y y κ (∑q∈I,bill q) (fun U=>∑q∈I,Q q U) := by
    induction I using Finset.induction_on with
    | empty =>
      have vacant : Store P S Y y κ 0 (fun _ : Config G n=>(0:ℂ)) := WilsonCenteredFiledAtoms.empty S Y y div
      simpa only [sum_empty] using vacant
    | @insert q I hq ih =>
      have a:=partition L x s q (valid (mem_insert_self ..)) y Z hold landing rad near w hw paid gross K law div hv room S Y reader
      have b:=ih (fun _ h=>valid (mem_insert_of_mem h))
      rw [sum_insert hq]
      simp_rw [sum_insert hq]
      exact WilsonCenteredFiledAtoms.add law div a b
  have result := gather (shards R s) (Subset.rfl)
  have values : (fun U=>∑q∈shards R s,Q q U) = (fun U=>(P.eval U:ℂ)*(Poly.pass (bare L x U)).part s) := by
    funext U
    have width : 0≤P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
    rw [pass_partition _ (WilsonRootedKioskCompleteFiling.quiet L hw width gross x U),mul_sum]
  rw [values] at result
  exact result

theorem transferred [Fintype V] [Countable ι] {p : BudgetPoint} (L : Lamps X ι G p o R) (same : P.p=p) (x : X) (s : R.Mode)
    (y : Site n) (Z : Support n) (hold : y∈Z) (landing : ∀j∈s.val,o j∈Z)
    (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w p.B (p.supportExponent+2) C)
    {D : ℝ} (gross : Gross L w p.B (p.supportExponent+2) D)
    {σ E Λ δ κ v μ : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p Z w C D rad S Y μ v κ s) (fun U=>(P.eval U:ℂ)*(Poly.pass (bare L x U)).part s) := by
  subst p
  exact original L x s y Z hold landing rad near w hw paid gross K law div hv room S Y reader

end YM.Integration.WilsonPlantedOrdinary
