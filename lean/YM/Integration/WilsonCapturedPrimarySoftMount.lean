import YM.Integration.WilsonCapturedPrimarySoftInventory
import YM.Integration.WilsonCenteredFiledAtoms
/-! The original unrestricted ordinary lamp polynomial is presented as one
formatted and rooted native field on the actual quiet Wilson representation. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySoftMount
open Function Finset RG Lattice Wilson Marker Multi QuadraticLocal Ac Push.Local Corona Push.AbsoluteSums Push.Corrected
open Source Labels Planned.GuardedAtom Extra.Histories WilsonCenteredCaptureRegularAtoms WilsonCenteredLampCapture
open WilsonCenteredFiledAtoms WilsonCapturedPrimarySoftPartition WilsonCapturedPrimarySoftRoster
open Comparison.RG02.Cumulants
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V]
    {R : Census V} {o : V→Site n} {P : Rep G n} {d : ℕ} {F : Frame G d}

def cost (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (C : ℝ) (rad : ℕ) (q : (parts R).Mode) :=
  stage p rad (univ : Finset (Fin q.val.card))*tariff p Z w C q

theorem partition [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (q : (parts R).Mode) (admitted : q∈shards R s) (y : Site n) (Z : Support n) (hold : y∈Z)
    (landing : ∀j∈s.val,o j∈Z) (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C)
    {σ E Λ δ κ v μ : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (cartage P.p Y S μ v κ (cost P.p Z w C rad q) 0)
      (fun U=>(P.eval U:ℂ)*∏ t∈q.val,(L.log x U).part t.val) := by
  let J := Fin q.val.card
  have width : 0≤P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
  obtain ⟨e,pos,cap,quote⟩:=WilsonCapturedPrimarySoftRoster.original L (block q) (root q) (seated q)
    Z (fun j=>landing _ (inside q admitted j)) w hw width paid
  let each (_ : Rows L (block q)) := (univ : Finset J)
  let sites (row : Rows L (block q)) (j : J) := (row j).val
  let seats (_ : Rows L (block q)) (j : J) := o (root q j)
  let gain (_ : Rows L (block q)) := (1:ℂ)
  have cash : SumBudget (fun z : Rows L (block q)=>reservedMass P.p (domain L (each z) (sites z) Z)
      (‖gain z‖*(stage P.p rad (each z)*∏ j∈each z,e (sites z j)))) (cost P.p Z w C rad q) := by
    have H:=budget_scale (zero_le_one.trans (funded P.p rad (univ : Finset J))) quote
    convert H using 1
    funext z
    change Real.exp _*(‖(1:ℂ)‖*(_* _)) = _*(_*Real.exp _)
    rw [norm_one,one_mul]
    ring
    rfl
  have no : ForceCost P.p P.activities (0 : ℕ→ Config G n→ℂ) (κ*0) := by
    rw [mul_zero]
    exact ⟨fun _=>0,Extra.Histories.budget0 _ _,by simp⟩
  have blank : ForceFormat P.p P.activities y 0 :=
    ⟨by simp,by simp,fun _ _ _=>rfl,fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
  have rates (row : Rows L (block q)) (j : J) (_ : j∈each row) :=
    cap (sites row j) x (seats row j) (L.roots _ _ (by exact (row j).property.symm ▸ seated q j))
  obtain ⟨Q,form,account,filed⟩:=counted L x y Z hold each sites seats rad
    (fun _ j _=>near _ (inside q admitted j)) gain (fun _=>e) rates cash K law div hv room S Y reader 0 0 blank no
  refine ⟨Q,form,account.bound le_rfl,?_⟩
  intro U
  change Q.density y S P U = (P.eval U:ℂ)*∏ t∈q.val,(L.log x U).part t.val
  rw [filed,←enumerate q (fun t=>(L.log x U).part t)]
  have output := (WilsonCapturedPrimarySoftRoster.complete L x (block q) U (paid.sums width hw x U)).tsum_eq
  simpa only [gain,one_mul,map_zero,Pi.zero_apply,tsum_zero,mul_zero,add_zero,zero_add,
    viewed,each,sites] using congrArg (fun z:ℂ=>(P.eval U:ℂ)*z) output

def fare (p : BudgetPoint) (Z : Support n) (w : V→ℝ) (C : ℝ) (rad : ℕ)
    (S : SectionData F) (Y : Hol G) (μ v κ : ℝ) (s : R.Mode) :=
  ∑q∈shards R s,cartage p Y S μ v κ (cost p Z w C rad q) 0

theorem original [Fintype V] [Countable ι] (L : Lamps X ι G P.p o R) (x : X) (s : R.Mode)
    (y : Site n) (Z : Support n) (hold : y∈Z) (landing : ∀j∈s.val,o j∈Z)
    (rad : ℕ) (near : ∀j∈s.val,separation (o j) y≤rad)
    (w : V→ℝ) (hw : ∀v,0<w v) {C : ℝ} (paid : L.Paid w P.p.B (P.p.supportExponent+2) C)
    {σ E Λ δ κ v μ : ℝ} (K : Guard.Keeper P.p P.activities) (law : P.Lawful σ E Λ δ v)
    (div : 0<κ) (hv : 0≤v) (room : hitWidth P.p*v≤1)
    (S : SectionData F) (Y : Hol G) (reader : Readable Y S P.p n μ) :
    Store P S Y y κ (fare P.p Z w C rad S Y μ v κ s) (fun U=>(P.eval U:ℂ)*(Poly.pass (L.log x U)).part s) := by
  let Q (q : (parts R).Mode) (U : Config G n) := (P.eval U:ℂ)*∏t∈q.val,(L.log x U).part t.val
  let bill (q : (parts R).Mode) := cartage P.p Y S μ v κ (cost P.p Z w C rad q) 0
  have gather (I : Finset (parts R).Mode) (valid : I⊆shards R s) :
      Store P S Y y κ (∑q∈I,bill q) (fun U=>∑q∈I,Q q U) := by
    induction I using Finset.induction_on with
    | empty =>
      have vacant : Store P S Y y κ 0 (fun _ : Config G n=>(0:ℂ)) := WilsonCenteredFiledAtoms.empty S Y y div
      simpa only [sum_empty] using vacant
    | @insert q I hq ih =>
      have a:=partition L x s q (valid (mem_insert_self ..)) y Z hold landing rad near w hw paid K law div hv room S Y reader
      have b:=ih (fun _ h=>valid (mem_insert_of_mem h))
      rw [sum_insert hq]
      simp_rw [sum_insert hq]
      exact WilsonCenteredFiledAtoms.add law div a b
  have result := gather (shards R s) (Subset.rfl)
  have values : (fun U=>∑q∈shards R s,Q q U) = (fun U=>(P.eval U:ℂ)*(Poly.pass (L.log x U)).part s) := by
    funext U
    have width : 0≤P.p.supportExponent+2 := by linarith only [P.p.exponent_pos]
    rw [pass_partition _ (L.quiet_of_hasSum x U (paid.sums width hw x U)),mul_sum]
  rw [values] at result
  exact result

end YM.Integration.WilsonCapturedPrimarySoftMount
