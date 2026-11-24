import YM.Integration.OriginalMarkedOrdinaryDensity
import YM.Integration.ManuscriptQLocalHealthyOffer
import YM.Integration.ManuscriptQLocalRawMaskCalendar
import YM.LocalLTE.Port.Shift

/-! All live rows of a finite physical marked source are installed together
at genuine ordinary slots in the original world, with its entire scalar gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalMarkedFiniteRegularMenu
open Function Finset Lattice Wilson RG Marker MergeProof Menu OPE.Therm
open Comparison.Density.RenderM Comparison.Density.RenderM.Token
open LocalComparison FullQLocal LocalLTE FVA1 PhysicalNext.Repeat.Legato
open Extra.Trajectories WardBin.Wheels Push.GridApprox RG.Supply Progress.DirectedRecipe
open ManuscriptQLocalOriginalConditionalTail
open scoped Classical BigOperators

variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
    {L : V→Support n} {C : Comparison.Density.Testing.Region (fun v=>(D v).Mood) n}
    {w : V→ℝ} {width budget : ℝ} {a b : ℕ} (Y : Rep G n)
    (H : P.Paid Y.p L C w 1 width budget a b) (o : V→Site n) (ho : ∀v,o v∈L v)
    (E : Finset ℕ) (all : ∀i,i∈E ↔ (P.packet i).isSome)

def enumerate : E ≃ Live P where
  toFun i := ⟨i.val,(all i.val).1 i.property⟩
  invFun i := ⟨i.val,(all i.val).2 i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq V] in
def cost (G : Gauge) (p : BudgetPoint) (rank power off : ℕ) (width budget : ℝ) : ℝ :=
  2*(Fintype.card V*((power+rank+1:ℕ)*ManuscriptQLocalMarkedRadius.price G p p rank off width 1 budget))

include H ho all in
theorem full {c d : ℝ} (law : Y.activities.Valid Y.p c d) (free : HasSlots Y.p Y.activities)
    (x : IndependentTests D) :
    ∃ (slot : E→ℕ) (m : E×Bool→Menu.Hat Γ Y),
      (∀i s,(m (i,s)).s=P.mode i ∧ Menu.WKey (m (i,s))=.logKey (slot i)) ∧
      Menu.Offer o m w Y.p.B Y.p.supportExponent (cost (V:=V) G Y.p P.rankCap P.powerCap a width budget) ∧
      (∀U,GapsLocal.Full.given m 0 U=(Y.eval U:ℂ) • Poly.pass (source P Y.p 1 x 1 U)) := by
  let e := enumerate P E all
  let T (i : E) := token P (e i)
  have chosen' (i : E) : P.packet i=some (T i) := chosen P (e i)
  let A (i : E) := ManuscriptQLocalHealthyOffer.address H o ho T chosen' i
  let slot (i : E) := blankRow n (A i,i.val)
  have placed (i : E) : (Y.activities.reg (slot i)).support=(T i).plot :=
    congrArg RegularAddress.support (Port.blanked free (A i) i.val)
  have spare (i : E) : Y.activities.E (slot i)=0 := free.regular (A i,i.val)
  have exponent : Y.p.supportExponent≤2*Y.p.supportExponent := by linarith [Y.p.exponent_pos]
  obtain ⟨m,keys,paid,invoice⟩ := ManuscriptQLocalHealthyOffer.offer H o ho T chosen' Y
    slot placed spare Y.p rfl rfl exponent P.rankCap le_rfl 1 1 1 x zero_lt_one le_rfl zero_le_one
    (by norm_num) le_rfl (by simpa only [one_mul] using Y.p.threshold_le)
  have unit (t : Menu.Hat Γ Y) (r : ℕ) : ManuscriptQLocalHealthyOffer.raised t 1 r=t := by
    cases t
    simp [ManuscriptQLocalHealthyOffer.raised]
  refine ⟨slot,m,keys,?_,?_⟩
  · simpa only [unit,cost] using invoice
  · intro U
    have original := OriginalMarkedOrdinaryDensity.original Y m (fun i=>slot i.1) law
      (fun i=>(keys i.1 i.2).2) U
    have sum : (∑j,Menu.amount (m j) U)=source P Y.p 1 x 1 U := by
      rw [Fintype.sum_prod_type,physical]
      simp_rw [paid]
      let f (i : Live P) := Poly.send (P.mode i) (field P Y.p 1 x i U)
      change (∑i:E,f (e i))=∑' i : Live P,f i
      simpa only [tsum_fintype] using e.tsum_eq f
    rw [sum] at original
    exact original

end YM.Integration.OriginalMarkedFiniteRegularMenu
end
