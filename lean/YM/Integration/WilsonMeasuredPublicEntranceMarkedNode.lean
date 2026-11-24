import YM.Integration.WilsonMeasuredPublicEntranceWeakTestCost
import YM.Integration.WilsonMeasuredPublicEntranceOrderedRoster
import YM.Integration.WilsonMeasuredPublicEntranceSeparatedBudget

/-! The intrinsic field and its time adjoint are measured on the same original
cutoff sample. The product allows an independently marked subset of any finite roster. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 900000
namespace YM.Integration.WilsonMeasuredPublicEntranceMarkedNode
open Function Filter Set Finset Metric Lattice RG Wilson Cells Extraction Spec Table PhysicalNext.Repeat.Legato Climb
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceWeakTestCost (slot)
open WilsonMeasuredPublicEntranceOrderedRoster (enrolled raw)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)
    {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {D T n:ℕ}{r:Fin n→ℝ}(B:∀i,Book F (l:=l) H z D T (r i))
    (d:Fin n→Fin (D+1))(v:∀i,Bool→S.Field (d i).val)
local notation "C₀" => R.family
local notation "ds" => (fun i:Fin n=>(d i).val)

def turned {e:ℕ}(b:Bool)(x:(C₀).label e):(C₀).label e:=
  if b then (C₀).book.adj e timeAxis x else x

theorem continuous {e:ℕ}(b:Bool):Continuous (turned R (e:=e) b):=by
  cases b
  · exact continuous_id
  · exact ((C₀).book.mirrorGroup e (Signed.mirror timeAxis)).continuous_of_finiteDimensional.comp continuous_star

def field (b marked:Fin n→Bool)(w:ℕ×ℕ):(C₀).book.Vector ds:=
  fun i=>turned R (marked i) (raw F B d v i (b i) w)

theorem original (simple:G.Simple)(below:(l:Filter (ℕ×ℕ))≤f.fuse)(j:ℕ)(o:Fin n→ Cover)
    (safe:Extraction.Order.grid (C₀) j o∈conf n)(b marked:Fin n→Bool):
    let Y:=field R F B d v b marked
    let value:=fun w:ℕ×ℕ=>physical (C:=R.family) ds j o w.1 w.2 (Y w)
    let project:=fun w=>publicValue (S:=S) ds j o (Y w)
    (Tendsto (fun w=>value w-project w) f.fuse (𝓝 0)) ∧
      Tendsto value (l:Filter (ℕ×ℕ)) (𝓝 (S.classMoment S ds (Extraction.Order.grid (C₀) j o)
        (fun i=>slot F (marked i) (v i (b i))))):=by
  classical
  intro Y value project
  obtain ⟨first,cost,_,offered,source,_⟩:=WilsonMeasuredPublicEntranceOrderedRoster.original F B d v
  choose M bounded using fun i=>(isCompact_closedBall (0:(C₀).label ((d i).val)) (cost i (b i))).exists_bound_of_continuousOn
    (continuous R (e:=(d i).val) (marked i)).continuousOn
  have ready:∀ᶠ w:ℕ×ℕ in f.fuse,first≤w.1:=by
    rw [Extraction.Order.fused]
    exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop _
  constructor
  · rw [Metric.tendsto_nhds]
    intro ε ep
    have native:=WilsonMeasuredPublicEntranceSeparatedBudget.ordered R F ds j o simple safe M (half_pos ep)
    have issued:∀ᶠw:ℕ×ℕ in f.fuse,∀y:(C₀).book.Vector ds,(∀i,‖y i‖≤M i) →
        ‖physical (C:=R.family) ds j o w.1 w.2 y-publicValue (S:=S) ds j o y‖≤ε/2:=(Extraction.Order.fused f _).mpr native
    filter_upwards [ready,issued] with w late paid
    rw [dist_zero_right]
    apply (paid (Y w) _).trans_lt (half_lt_self ep)
    exact fun i=>bounded i _ (by simpa only [Metric.mem_closedBall,dist_zero_right] using offered w.1 w.2 late i (b i))
  · let y:=fun i=>turned R (marked i) (enrolled F B d v i (b i)).label
    have cv(i):Tendsto (fun w=>Y w i) (l:Filter (ℕ×ℕ)) (𝓝 (y i)):=(continuous R (marked i)).continuousAt.tendsto.comp (source i (b i)).1
    have native:=WilsonMeasuredPublicEntranceSeparatedPins.variation R F ds j o simple below Y y cv safe
    have eq(i:Fin n):S.project (ds i) (y i)=slot F (marked i) (v i (b i)):=by
      cases hm:marked i
      · simpa only [y,turned,hm,Bool.false_eq_true,if_false,slot] using (source i (b i)).2
      · simp only [y,turned,hm,if_true,slot,←S.adj_project F.room.kernel.spin,(source i (b i)).2]
    have read:=(S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) ds safe y)
    simp only [eq] at read
    rw [read]
    exact native

end YM.Integration.WilsonMeasuredPublicEntranceMarkedNode
end
