import YM.Integration.WilsonOrdinaryNestedDoses
import YM.Integration.WilsonOrdinaryNestedInput

/-! On one true vertex the entire normalized ordinary difference has an exact
finite multilinear expansion in the dictionary's own homogeneous input axes. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOrdinaryNestedBasis
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


open WilsonMSDictionaryVector
variable {n:ℕ} (d:Fin n→ℕ)
abbrev Choice (G:Gauge) (d:Fin n→ℕ) := (i:Fin n)→Dframe.Toon G (d i)
def axes (c:Choice G d) (i:Fin n):Free R.family (d i):=WilsonMSDictionaryVector.basis R.family (d i) (c i)
def due (a:(i:Fin n)→Free R.family (d i)) (c:Choice G d) : ℂ :=
  ∏i,(WilsonMSDictionaryVector.basis R.family (d i)).repr (a i) (c i)

def physical (m:ℕ) (r:ℝ) (z:Points n) :
    MultilinearMap ℂ (fun i=>Free R.family (d i)) (Free R.family m) :=
  (pub r m).symm.toLinearMap.compMultilinearMap (
    (∑j:Fin (m+1),(F.sector.derivatives.rise (Nat.le_of_lt_succ j.isLt)).compMultilinearMap
      ((Q.fresh j.val (fun i=>r • z i) 0).compLinearMap (fun i=>(pub r (d i)).toLinearMap))))

theorem paid (m:ℕ) (r:ℝ) (z:Points n) (a:(i:Fin n)→Free R.family (d i)):
    physical (Q:=Q) (J:=J) Z d m r z a =
      (pub r m).symm (WilsonPublicOutputRows.packet F pub Q m d a r z) := by
  unfold physical WilsonPublicOutputRows.packet Reader.packet
  simp only [LinearMap.compMultilinearMap_apply,_root_.sum_apply,MultilinearMap.compLinearMap_apply]
  rfl

theorem decompose {E:Type} [AddCommGroup E] [Module ℂ E]
    (A:MultilinearMap ℂ (fun i=>Free R.family (d i)) E) (a:(i:Fin n)→Free R.family (d i)):
    A a = ∑c:Choice G d,due (R:=R) d a c • A (axes (R:=R) d c) := by
  let term(i:Fin n)(b:Dframe.Toon G (d i)) := (WilsonMSDictionaryVector.basis R.family (d i)).repr (a i) b • WilsonMSDictionaryVector.basis R.family (d i) b
  have input(i:Fin n) : a i=∑b,term i b:=((WilsonMSDictionaryVector.basis R.family (d i)).sum_repr (a i)).symm
  calc
    A a = A (fun i=>∑b,term i b):=congr_arg A (funext input)
    _ = ∑ c : Choice G d, A (fun i=>term i (c i)):=by
      rw [A.map_sum_finset term (fun _=>Finset.univ),Fintype.piFinset_univ]
    _ = _:=Finset.sum_congr rfl fun c _=>A.map_smul_univ (fun i=>(WilsonMSDictionaryVector.basis R.family (d i)).repr (a i) (c i))
      (axes (R:=R) d c)

theorem on_axis (m:ℕ) (V:Choice G d→Dframe.Toon G m→ℂ) (c:Choice G d):
    WilsonMSDictionaryVector.assemble R.family d m (axes (R:=R) d c) V = ∑ b,V c b • WilsonMSDictionaryVector.basis R.family m b := by
  unfold WilsonMSDictionaryVector.assemble
  rw [Finset.sum_eq_single c]
  · simp [axes]
  · intro j _ ne
    obtain ⟨i,hi⟩:=Function.ne_iff.mp ne
    have zero : (WilsonMSDictionaryVector.basis R.family (d i)).repr (axes (R:=R) d c i) (j i)=0:=by
      simp [axes,hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) zero,zero_smul]
  · exact fun absent=>(absent (Finset.mem_univ c)).elim

def gap (m q:ℕ) (r:ℝ) (z:Points n) (a:(i:Fin n)→ Free R.family (d i)):Free R.family m:=
  physical (Q:=Q) (J:=J) Z d m r z a - WilsonOrdinaryNestedMSPoint.field Z M ν R.family d m a z q (θ r)

theorem original (m q:ℕ) (r:ℝ) (z:Points n) (a:(i:Fin n)→ Free R.family (d i)):
    gap (Q:=Q) (J:=J) Z M ν d m q r z a =
      ∑ c:Choice G d,due (R:=R) d a c • gap (Q:=Q) (J:=J) Z M ν d m q r z (axes (R:=R) d c) := by
  unfold gap WilsonOrdinaryNestedMSPoint.field
  rw [decompose d (physical (Q:=Q) (J:=J) Z d m r z) a]
  simp_rw [on_axis,smul_sub,Finset.sum_sub_distrib]
  rfl
end YM.Integration.WilsonOrdinaryNestedBasis
