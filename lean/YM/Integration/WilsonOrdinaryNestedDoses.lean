import YM.Integration.WilsonOrdinaryNestedOutput

/-! One fixed increase of the local perturbative order covers the entire
finite tree. The measured object is the full normalized public output field,
with its actual incoming labels on the occupied comparable configuration. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedDoses
open Filter Function Set Spec Extraction Table PhysicalNext.Repeat.Legato Climb
open OPE OPE.Log OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Atom OPE.Nesting.Composite
open PhysMS Trace.Pilot RG17 Maxwell XSpace Pert Pert.Position MS MS.Land MS.Menus MS.Theater
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

def fieldGap {n:ℕ} (m q:ℕ) (r:ℝ) (x:Fin n→E4) (o:E4) (v:Fin n→S.Tag) : Free R.family m :=
  let z:=placed r x o
  let a:=raised F J Z r v
  (pub r m).symm (WilsonPublicOutputRows.packet F pub Q m (degrees v) a r z) -
    WilsonOrdinaryNestedMSPoint.field Z M ν R.family (degrees v) m a z q (θ r)

def Vertex {n:ℕ} (U η:ℝ) (p q m:ℕ) (v:Fin n→S.Tag) : Prop :=
  ∃ C:ℝ,0≤C ∧ ∀ᶠr in trail, ∀(x:Fin n→E4) (o:E4),
    (∀i,‖x i-o‖≤U*r) → (∀i l,i≠l→η*r≤‖x i-x l‖) →
      ‖fieldGap (Q:=Q) (J:=J) Z M ν m q r x o v‖≤C*(θ r)^p

def Inventory (U η:ℝ) (p q:ℕ) : (t:Tree) → (t.Leaf→S.Tag) → (t.Inner→ℕ) → ℕ → Prop
 | bud,_,_,_=>True
 | fork _ arm,v,D,H=>
   (∀ (sel:Branches F Q (f:=arm) (rollCaps D)) (m:Fin (H+1)),
      Vertex (Q:=Q) (J:=J) Z M ν U η p q m (echoTags F Q v sel)) ∧
   ∀i, Inventory U η p q (arm i) (childWages i v) (childAge i D) (rollCaps D i)

include run in
theorem original (clock:Coupling G θ) (U η:ℝ) (t:Tree) (v:t.Leaf→S.Tag) (D:t.Inner→ℕ) (H:ℕ) :
    ∃ W:ℕ,∀w, W≤w → ∀ P q:ℕ,Inventory (Q:=Q) (J:=J) Z M ν U η (P+w) q t v D H →
      Receipts F Q J Z M ν θ U η P q t v D H := by
  induction t generalizing H with
  | bud=>exact ⟨0,fun _ _ _ _ _=>trivial⟩
  | fork n arm ih =>
    let α:=Σ m:Fin (H+1),Q.channels m
    have wallet (a:α):=WilsonOrdinaryNestedOutput.clocked run Z clock a.1 a.2
    choose l K Kp due using wallet
    have kids (i:Fin n):=ih i (childWages i v) (childAge i D) (rollCaps D i)
    choose k child using kids
    let a:=∑i:α,l i
    let b:=∑i,k i
    refine ⟨a+b,?_⟩
    intro w total P q rows
    refine ⟨?_,?_⟩
    · intro sel m c
      let s:α:=⟨m,c⟩
      let leg:=echoTags F Q v sel
      have small : l s≤w:=(Finset.single_le_sum (f:=l) (fun i _=>Nat.zero_le (l i))
        (Finset.mem_univ s)).trans ((Nat.le_add_right a b).trans total)
      obtain ⟨C,Cp,price⟩:=rows.1 sel m
      refine ⟨K s*C,mul_nonneg (Kp s) Cp,?_⟩
      filter_upwards [due s,price,clock.positive,(clock.conforms simple).eventually
        (ge_mem_nhds zero_lt_one)] with r paid observed gp g1 x o close apart
      let delta:=fieldGap (Q:=Q) (J:=J) Z M ν m q r x o leg
      change ‖ear F Q J Z r m c delta / (r:ℂ)^m.val‖≤_
      have normed:‖delta‖≤C*(θ r)^(P+w):=observed x o close apart
      have high: (θ r)^(P+w)≤(θ r)^(P+l s):=
        pow_le_pow_of_le_one gp.le g1 (Nat.add_le_add_left small P)
      have gross:=mul_le_mul_of_nonneg_left (normed.trans
        (mul_le_mul_of_nonneg_left high Cp)) (div_nonneg (Kp s) (pow_nonneg gp.le (l s)))
      refine (paid delta).trans (gross.trans_eq ?_)
      rw [abs_of_pos gp,pow_add]
      field_simp
    · intro i
      have ki:k i≤b:=Finset.single_le_sum (f:=k) (fun j _=>Nat.zero_le (k j)) (Finset.mem_univ i)
      exact child i w (ki.trans ((Nat.le_add_left b a).trans total)) P q (rows.2 i)

end YM.Integration.WilsonOrdinaryNestedDoses
