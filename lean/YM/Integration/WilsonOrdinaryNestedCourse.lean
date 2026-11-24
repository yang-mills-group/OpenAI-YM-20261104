import YM.Integration.WilsonOrdinaryNestedTariff
import YM.Integration.WilsonViewerBookedHierarchy

/-! All fixed finite trees on the same funded hierarchy and the same physical
viewer.  The exponent of the logarithmic coefficient price precedes the
perturbative order; every signed input is compared at its own radius. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedCourse
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom
open PhysMS Trace.Pilot WilsonCenteredNestedProgram WilsonCenteredNestedIntake WilsonCenteredNestedGross WilsonCenteredNestedSigned
open WilsonCenteredNestedLoggedRow WilsonOrdinaryNestedTariff WilsonCenteredNestedViewer
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}

theorem original (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort)
    (g:ℝ→ℝ) (clock:Coupling G g) {n:ℕ} (p:Fin n→Tree) (v:(fork n p).Leaf→S.Tag)
    (D:(fork n p).Inner→ℕ) (H:ℕ) {I:Type} [Fintype I] (ex:I→S.Tag)
    {M η ε δ:ℝ} (M0:0≤M) (ηp:0<η) (εp:0<ε) (δp:0<δ) :
    LogTrace F Q.port ∧ ∃ j B, 0≤B ∧
      ∀ (P:ℕ) (V:Rule F Q) (C:ℝ), 0≤C → WilsonCenteredNestedSigned.Signed F Q V g M η P 0 C (fork n p) v D H →
      ∃ b:Fin (H+1)→ℝ, (∀ k,0≤b k) ∧
      ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (s:(fork n p).Inner→ℝ) (z:(fork n p).Plot),Accept r M η s z →
        (∀ (k:Fin (H+1)) (c:Q.channels k),
          ‖Kernel.output F Q z v c - WilsonCenteredNestedProgram.run F Q V g (fork n p) s z v D k ⟨Fin.last k.val,c⟩‖ ≤
            price F Q v D k ε j (B+C) s g P) ∧
        ∀ (y:I→E4),Buffer z y δ → ∀ q:Viewers F,
          ‖whole (spectator F q) (Tree.profile z) (voices v) y (voices ex) -
            predicted F Q V g v ex H D s z y q‖ ≤
            footprint v s (H+1)*ratiosLoss s ε +
              ∑ k:Fin (H+1),∑ c:Q.channels k,price F Q v D k ε j (B+C) s g P *
                (b k*‖Q.actor k c‖) := by
  have ticket := OPE.tickets_suffice F run.facilities run.original run.matrix Q.spans
  refine ⟨ticket,?_⟩
  obtain ⟨j,B,Bn,allRows⟩ := WilsonCenteredNestedSigned.original F Q simple
    run.facilities.toServices ticket.toSingleLog g clock M0 ηp (fork n p) v D H
  refine ⟨j,B,Bn,?_⟩
  intro P V C Cn signed
  let cash:=wage j (B+C)
  have matched : localRows F Q V g cash (fun a=>|g a|^P) M η (fork n p) v D H := by
    simpa only [Nat.add_zero] using allRows 0 P V C Cn signed
  have nn (x:ℝ) : 0≤cash x := mul_nonneg (add_nonneg Bn Cn) (pow_nonneg ((shell_one x).trans' zero_le_one) _)
  have low (k:Fin (H+1)) : localRows F Q V g cash (fun a=>|g a|^P) M η (fork n p) v D k :=
    ⟨fun sel i c=>matched.1 sel ⟨i.val,Nat.lt_of_lt_of_le i.isLt
      (Nat.succ_le_succ (Nat.le_of_lt_succ k.isLt))⟩ c,matched.2⟩
  have enter:=Nesting.uniform F Q run.facilities.toServices
  have panels:=eventually_all.mpr (fun k:Fin (H+1)=>eventually_all.mpr (fun c:Q.channels k=>
    filed F Q enter V g cash nn P v D k c M η ε M0 ηp εp (low k)))
  obtain ⟨b,bn,view⟩:=WilsonCenteredNestedViewer.original F Q run.facilities.toServices V g cash nn P
    v ex H D M η ε δ M0 ηp εp δp matched
  refine ⟨b,bn,?_⟩
  filter_upwards [panels,view] with r exactRows watch
  intro s z ok
  have rate (k:Fin (H+1)) := WilsonOrdinaryNestedTariff.bill F Q s v D k j P (B+C) ε g ok.levels
  refine ⟨fun k c=>(exactRows k c s z ok).trans_eq (rate k),?_⟩
  intro y far q
  have output:=watch s z y ok far q
  simp_rw [show ∀k:Fin (H+1), bothToll (wages v) ε k D s +
    WilsonCenteredNestedPhysical.vertexFee F Q s v D k cash (fun a=>|g a|^P) =
    price F Q v D k ε j (B+C) s g P from rate] at output
  apply output.trans_eq
  congr 1
  simpa only [footprint,ratiosLoss,Nat.cast_add,Nat.cast_one] using
    WilsonOrdinaryNestedEngineering.loss (wages v) s ε ((H:ℝ)+1) ok.levels

end YM.Integration.WilsonOrdinaryNestedCourse
