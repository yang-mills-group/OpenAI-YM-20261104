import YM.Integration.WilsonOrdinaryNestedShapeTest
import YM.Integration.WilsonOrdinaryNestedTestedPacket
import YM.Integration.WilsonOrdinaryNestedProbes

/-! Tested comparable vertices suffice on the original physical hierarchy at all scale ratios. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedSmoothTree
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom OPE.Nesting.Composite
open PhysMS Trace.Pilot RG17 Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater
open WilsonOrdinaryNestedTariff WilsonCenteredNestedViewer
open FVA2 FVA2.Register FVA2.Scale WilsonCenteredNestedProgram WilsonCenteredNestedGross
open WilsonPositionHomogeneousFrame WilsonOrdinaryNestedMSVertex WilsonOrdinaryNestedLocal
open MeasureTheory
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


def region (n:ℕ) (U η:ℝ) (positive:0<η):Set (Points n):=
  (WilsonOrdinaryNestedShapeTest.cover n U η positive).choose

theorem legal (n:ℕ) (U η:ℝ) (positive:0<η):
    IsCompact (region n U η positive) ∧ region n U η positive⊆conf n ∧
    ∀z∈WilsonOrdinaryNestedShapeTest.shapes n U η,region n U η positive∈𝓝 z:=
  (WilsonOrdinaryNestedShapeTest.cover n U η positive).choose_spec

variable {n:ℕ}

def Smooth (K:Set (Points n)) (p q h:ℕ) (d:Fin n→ℕ):Prop:=
  ∀c:WilsonOrdinaryNestedBasis.Choice G d, ∃C:ℝ,0≤C ∧ ∀ᶠr in trail,
    ∀ψ:Test n,tsupport (ψ:Points n→ℂ)⊆K →
      let v:=WilsonOrdinaryNestedBasis.axes (R:=R) d c
      ‖(homogeneous F J Z r h).symm (basket Q h (Frame.born (homogeneous F J Z) r v) r ψ) -
        WilsonMSDictionaryVector.prediction R.family d h Z M ν v ψ q (θ r)‖ ≤
        (C*(θ r)^p)*(∫x:Points n,‖ψ x‖)

variable {σ:Prescription (Press.portDeck G)} {dial:Bool} (ms:Main.Match Z simple M σ dial)

include ms in
theorem field (fac:Services R.family f S) (U η:ℝ) (sep:0<η) (p q h:ℕ) (d:Fin n→ℕ)
    (earned:Smooth (Q:=Q) (J:=J) Z M ν (region n U η sep) p q h d):
    WilsonOrdinaryNestedFixedInput.Fixed (Q:=Q) (J:=J) Z M ν U η p q h d:=by
  have box:=legal n U η sep
  intro c
  obtain ⟨C,cn,paid⟩:=earned c
  refine ⟨C,cn,?_⟩
  filter_upwards [paid,WilsonOrdinaryNestedTestedPacket.original F J Z M ν Q ms d fac h q _ box.1 box.2.1 c]
    with r invoice matched z size distinct
  exact WilsonOrdinaryNestedShapeTest.read box.2.1 (box.2.2 z ⟨size,distinct⟩) matched.1
    (fun φ supp=> (matched.2 φ supp) ▸ invoice φ supp)

def Docket (U η:ℝ)(sep:0<η)(p q:ℕ) :
    (t:Tree)→(t.Leaf→S.Tag)→(t.Inner→ℕ)→ℕ→Prop
  | bud,_,_,_=>True
  | fork n arm,v,D,H=>
    (∀sel:Branches F Q (f:=arm) (rollCaps D),∀m:Fin (H+1),
      Smooth (Q:=Q) (J:=J) Z M ν (region n U η sep) p q m (degrees (echoTags F Q v sel))) ∧
    ∀i,Docket U η sep p q (arm i) (childWages i v) (childAge i D) (rollCaps D i)

include ms in
theorem filed (fac:Services R.family f S) (U η:ℝ) (sep:0<η) (p q:ℕ) (t:Tree)
    (v:t.Leaf→S.Tag) (D:t.Inner→ℕ) (H:ℕ)
    (record:Docket (Q:=Q) (J:=J) Z M ν U η sep p q t v D H) :
    WilsonOrdinaryNestedProbes.Probes (Q:=Q) (J:=J) Z M ν U η p q t v D H:=by
  induction t generalizing H with
  | bud=>trivial
  | fork n arm children=>
    exact ⟨fun sel m=> field Z M ν ms fac U η sep p q m _ (record.1 sel m),
      fun i=>children i _ _ _ (record.2 i)⟩
include run ms in
theorem original
    (clock:Coupling G θ) {n:ℕ} (p:Fin n→Tree) (v:(fork n p).Leaf→S.Tag)
    (D:(fork n p).Inner→ℕ) (H:ℕ) {I:Type} [Fintype I] (ex:I→S.Tag)
    {U η ε δ:ℝ} (U0:0≤U) (ηp:0<η) (εp:0<ε) (δp:0<δ) :
    LogTrace F Q.port ∧ ∃ W j B, 0≤B ∧ ∀ P q:ℕ,
    Docket (Q:=Q) (J:=J) Z M ν U η ηp (P+W) q (fork n p) v D H →
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
  obtain ⟨sharp,k,j,B,Bp,tree⟩:=WilsonOrdinaryNestedProbes.original run Z M ν clock p v D H ex U0 ηp εp δp
  refine ⟨sharp,k,j,B,Bp,?_⟩
  intro P q earned
  exact tree P q (filed Z M ν ms run.facilities.toServices U η ηp (P+k) q (fork n p) v D H earned)
end YM.Integration.WilsonOrdinaryNestedSmoothTree
