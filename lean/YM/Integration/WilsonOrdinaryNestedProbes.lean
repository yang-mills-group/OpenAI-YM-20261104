import YM.Integration.WilsonOrdinaryNestedFixedInput
import YM.Integration.WilsonOrdinaryNestedHierarchy

/-! Signed finite fixed-basis probes on each comparable vertex of an arbitrary
finite tree and the complete separated ordinary physical run. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedProbes
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom OPE.Nesting.Composite
open PhysMS Trace.Pilot RG17 Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater
open WilsonOrdinaryNestedTariff WilsonCenteredNestedViewer
open FVA2 FVA2.Register FVA2.Scale WilsonCenteredNestedProgram WilsonCenteredNestedGross
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {f:Extraction.Order} {S:Table R.family.book}
    {F:Final R.family f S} {L:EveryPhase.Almanac F}
    {Q:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}
    {J:ℝ→PhysMS.tower S} {Y:(Bel R.family.book).Hierarchy} {A:Trace.Terrace.Arch R.family}
    {ℓ:Ultrafilter (ℕ×ℕ)} {simple:G.Simple} {cohort:Ultrafilter (ℕ×ℕ)→Prop}
    (run:WilsonViewerElectedHierarchy.Selected.{u} F L Q J Y A ℓ simple cohort) (Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ)
local notation "pub" => homogeneous F J Z
local notation "θ" => reading F J Z


def Probes (U η:ℝ) (p q:ℕ) : (t:Tree) → (t.Leaf→S.Tag) → (t.Inner→ℕ) → ℕ → Prop
 | bud,_,_,_=>True
 | fork _ arm,v,D,H=>
   (∀ (sel:Branches F Q (f:=arm) (rollCaps D)) (m:Fin (H+1)),
      WilsonOrdinaryNestedFixedInput.Fixed (Q:=Q) (J:=J) Z M ν U η p q m (degrees (echoTags F Q v sel))) ∧
   ∀i, Probes U η p q (arm i) (childWages i v) (childAge i D) (rollCaps D i)

include run in
theorem intake (clock:Coupling G θ) (U η:ℝ) (t:Tree) (v:t.Leaf→S.Tag) (D:t.Inner→ℕ) (H:ℕ):
    ∃W:ℕ,∀w,W≤w→∀P q:ℕ,Probes (Q:=Q) (J:=J) Z M ν U η (P+w) q t v D H →
      WilsonOrdinaryNestedDoses.Inventory (Q:=Q) (J:=J) Z M ν U η P q t v D H :=by
  induction t generalizing H with
  | bud=>exact ⟨0,fun _ _ _ _ _=>trivial⟩
  | fork n arm ih=>
    let T:=Branches F Q (f:=arm) (rollCaps D)
    have wallet (c:T):=WilsonOrdinaryNestedFixedInput.original run Z M ν clock U η (echoTags F Q v c)
    choose s root using wallet
    have heirs (i:Fin n):=ih i (childWages i v) (childAge i D) (rollCaps D i)
    choose k child using heirs
    let a:=∑c:T,s c
    let b:=∑i,k i
    refine ⟨a+b,?_⟩
    intro w total P q earned
    refine ⟨?_,?_⟩
    · intro c m
      have sc:s c≤a:=Finset.single_le_sum (f:=s) (fun j _=>Nat.zero_le (s j)) (Finset.mem_univ c)
      exact root c w (sc.trans ((Nat.le_add_right a b).trans total)) P q m (earned.1 c m)
    · intro i
      have ki:k i≤b:=Finset.single_le_sum (f:=k) (fun j _=>Nat.zero_le (k j)) (Finset.mem_univ i)
      exact child i w (ki.trans ((Nat.le_add_left b a).trans total)) P q (earned.2 i)
include run in
theorem original
    (clock:Coupling G θ) {n:ℕ} (p:Fin n→Tree) (v:(fork n p).Leaf→S.Tag)
    (D:(fork n p).Inner→ℕ) (H:ℕ) {I:Type} [Fintype I] (ex:I→S.Tag)
    {U η ε δ:ℝ} (U0:0≤U) (ηp:0<η) (εp:0<ε) (δp:0<δ) :
    LogTrace F Q.port ∧ ∃ W j B, 0≤B ∧ ∀ P q:ℕ,
    Probes (Q:=Q) (J:=J) Z M ν U η (P+W) q (fork n p) v D H →
    ∃ C:ℝ,0≤C ∧ ∃ b:Fin (H+1)→ℝ, (∀ k,0≤b k) ∧
    ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (s:(fork n p).Inner→ℝ) (z:(fork n p).Plot),Accept r U η s z →
      let V:= program F Q J Z M ν q
      (∀ (k:Fin (H+1)) (c:Q.channels k),
        ‖Kernel.output F Q z v c - WilsonCenteredNestedProgram.run F Q V θ (fork n p) s z v D k ⟨Fin.last k.val,c⟩‖ ≤
          price F Q v D k ε j (B+C) s θ P) ∧
      ∀ (y:I→E4),Buffer z y δ → ∀ view:Viewers F,
        ‖whole (spectator F view) (Tree.profile z) (voices v) y (voices ex) -
          predicted F Q V θ v ex H D s z y view‖ ≤
          footprint v s (H+1)*ratiosLoss s ε +
            ∑ k:Fin (H+1),∑ c:Q.channels k,price F Q v D k ε j (B+C) s θ P *
              (b k*‖Q.actor k c‖) := by
  obtain ⟨sharp,k,j,B,Bp,tree⟩:=WilsonOrdinaryNestedHierarchy.original Z M ν run clock p v D H ex U0 ηp εp δp
  obtain ⟨W,price⟩:=intake run Z M ν clock U η (fork n p) v D H
  refine ⟨sharp,k+W,j,B,Bp,?_⟩
  intro P q paid
  exact tree P q (price W le_rfl (P+k) q (by simpa only [Nat.add_assoc] using paid))

end YM.Integration.WilsonOrdinaryNestedProbes
