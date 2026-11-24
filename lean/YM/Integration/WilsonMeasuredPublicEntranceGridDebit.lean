import YM.Integration.WilsonOriginalMicroscopicEntranceGridRow
import YM.Integration.WilsonAddressedRestartedFiled

/-! One before-cutoff threshold for all admissible physical grades. The
matrices are elected before the actual cutoff labels, the field and the test.
Each returned original source resolves the true N-born minus K-born unary on
every configuration of the separated reporter. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceGridDebit
open Function Filter Lattice RG Wilson Source Labels Extra.Histories Relay
open OPE.Therm Push.AbsoluteSums.Animals Next.Foundations WilsonOriginalNullPlacedGermMap
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Work.G08
open WilsonOriginalNullCorridor WilsonPositionProgramOriginalBlockedTrial
open WilsonAddressedRestartedColumn WilsonOriginalMicroscopicGuardedReporters
open WilsonOriginalMicroscopicEntranceGridRow
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G)

def fitted (d j N p : ℕ) (Y : R.family.label d) : R.family.label d :=
  page (C:=R.family) d p j ((R.family.factory d N p).entries j ((R.family.factory d N p).terminal.symm Y))

def bill (d K f : ℕ) (w : R.family.label d) : ℝ :=
  hike R.family K f rate*((1+4*stock R.family K)*(R.family.labels.level d).coeffSize w)

def named (d f N p : ℕ) (live : f ≤ N) (o : Site (R.family.side f p)) (Y : R.family.label d) :=
  R.family.O N p Y ((R.family.S.toDepth live p).embed o)

def trial (d f n N p : ℕ) (o : Site (R.family.side f p)) (w : R.family.label d) :=
  WilsonOriginalMicroscopicEntranceGridRow.entered R (fun _ : Fin 3 => d) (N:=N) (n:=n) (fun _ => o) (fun _ => w) 0

def settled (d j f n N p : ℕ) (high : f+n≤N) (A : R.family.label d ≃ₗ[ℂ] R.family.label d)
    (Y : R.family.label d) (o : Site (R.family.side f p)) : Prop :=
  let w := A.symm (fitted R d j N p Y)
  let B := bill R d (f+n) f w
  ∃ z : store R.family d p f,
    WilsonAddressedRestartedFiled.Filed R d N p f o
      (track R d N p (f+n) (numerator R d N p (f+n) 0 w) f-
         calValues (C:=R.family) d N p f ((R.family.factory d N p).terminal.symm Y)) B z ∧
    ∀U, actualTransport R.family (N:=N) (named R d f N p (by omega) o Y) (by omega) U-
      actualTransport R.family (N:=N) (trial R d f n N p o w) (Nat.le_add_right f n) U =
      -(z.density o (R.family.localSection d) (R.family.path.rep N p f) U)/
        ((R.family.S.a f:ℂ)^d*((R.family.path.rep N p f).eval U:ℂ))

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (wide : ∀j, 1 ≤ (R.family.path.levels.budget j).supportExponent)
    (quote : Poetry R.family.path.levels) (D target : ℕ) {η : ℝ} (pos : 0 < η) :
    ∃ L : ℕ, ∀ (I : Type) (d : I → Fin (D+1)) (j : I → ℕ) (f n N p : ℕ)
      (_ : ∀v, L ≤ j v) (before : ∀v, j v ≤ f) (live : f+n≤N) (_ : ∀v,j v<N),
      ∃ A : (v : I) → R.family.label (d v).val ≃ₗ[ℂ] R.family.label (d v).val,
        (∀v x, Arrived R (d v).val (j v) (f+n) N p target (by grind) live η (A v) x) ∧
        ∀v, R.family.ref (d v).val ≤ f →
          ∀ (Y : R.family.label (d v).val) (o : Site (R.family.side f p)),
          settled R (d v).val (j v) f n N p live (A v) Y o := by
  classical
  choose gates reports using fun a : Fin (D+1) => WilsonOriginalMicroscopicGuardedReporters.original R
    (fun _ => a.val) simple shop wide quote target pos
  choose leaves filed using fun a : Fin (D+1) => eventually_atTop.mp
    (WilsonAddressedRestartedFiled.original R a.val simple)
  refine ⟨Finset.univ.sup (fun a : Fin (D+1) => max (gates a) (leaves a)),?_⟩
  intro I d j f n N p starts before live deep
  have floor (v : I) := (Finset.le_sup (f:=fun a : Fin (D+1) => max (gates a) (leaves a))
    (Finset.mem_univ (d v))).trans (starts v)
  choose A read using fun v : I => reports (d v) (fun _ => j v)
    (fun _ => (le_max_left ..).trans (floor v)) (f+n)
    (fun _ => (before v).trans (Nat.le_add_right f n)) (fun _ => 0) N p live (fun _ => deep v)
  refine ⟨fun v => A v 0,fun v => (read v).1 0,?_⟩
  intro v ready Y o
  let x := (R.family.factory (d v).val N p).terminal.symm Y
  obtain ⟨z,held⟩ := filed (d v) (j v) ((le_max_right ..).trans (floor v)) N p (f+n)
    ((before v).trans (Nat.le_add_right f n)) live target η (A v 0) x
    ((read v).1 0 (fitted R (d v).val (j v) N p Y)) f (before v) (Nat.le_add_right f n) o
  refine ⟨z,held,?_⟩
  intro U
  exact WilsonOriginalMicroscopicEntranceGridRow.original R (fun _ => (d v).val) live
    (fun _ => Y) (fun _ => o) (fun _ => (A v 0).symm (fitted R (d v).val (j v) N p Y))
    0 ready _ z held U

end YM.Integration.WilsonMeasuredPublicEntranceGridDebit
end
