import YM.Integration.WilsonOriginalSeparatedPublicFields

/-! The public phase master, sharp matrix and literal reflected fields on a single
original extraction. The public objects precede every horizon and test. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalAllOrderPublicFields
open Climb Lattice Filter Function Spec OPE Next.Extract PhysMS Trace.Target Trace.Pilot
open PhysicalNext.Repeat.Legato WilsonLimitConstruction GapsContact.Seams GapsContact.Ascent
open scoped Classical Topology
variable {G : Gauge} {R : Run G} {simple : G.Simple}

/-- This is the one licensed physical master, including its independent
microscopic receipts and positive reflected prices in all fixed horizons. -/
def Master (R : Run G) (simple : G.Simple) (cohort : Ultrafilter (ℕ × ℕ) → Prop)
    (v : Extraction.Order) : Prop :=
  ∃ (w : Extraction.Order) (S : Table R.family.book)
    (F : Final R.family (v.refine w) S) (L : EveryPhase.Almanac F)
    (Q : Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (Y : (Bel R.family.book).Hierarchy) (Z : Trace.Terrace.Arch R.family)
    (l : Ultrafilter (ℕ × ℕ)) (_ : Bliss F l Z Y)
    (P P' : ℝ → Spin.change S 4) (J : ℝ → PhysMS.tower S)
    (φ : E4 → ℝ) (a d e : ℝ → ℝ),
    EveryPhase.Completed F L ∧ Trace.Target.Result.{u} F simple ∧ Trace.Target.Exclusion.{u} F ∧
    Facilities R.family (v.refine w) S ∧ Orbits.Foundation F Q ∧ SingleLog F Q.port ∧
    (∀ᶠ r in trail, J r 4 = P' r) ∧
    Trace.Target.XScheme F simple Y l P P' φ ∧ Trace.Target.FieldComparison F Y Z P P' a d e ∧
    Leading F J ∧ (∀ d, ∀ᶠ r in trail, Frame.obedient F Y (J r) d) ∧
    (l : Filter (ℕ × ℕ)) ≤ (v.refine w).fuse ∧ cohort l ∧
    Log.MatrixTicket (C := R.family) S F.sector.derivatives (l : Filter (ℕ × ℕ)) ∧
    ∀ D, ∃ t : ℕ, ∀ᶠ r in trail, ∃ j m, Pool F l r j m D (dock r ^ t)

theorem original {cohort : Ultrafilter (ℕ × ℕ) → Prop}
    (paid : WilsonMacroscopicFundedReader.Elected.{u} R simple cohort) (v : Extraction.Order) :
    Master.{u} R simple cohort v := by
  obtain ⟨w,S,F,L,Q,completed,result,exclusion,fac,found,laws,Y,Z,l,bliss,P,P',J,φ,a,d,e,
    top,scheme,comp,leading,obedient,lies,selected,ticket⟩ := paid v
  exact ⟨w,S,F,L,Q,Y,Z,l,bliss,P,P',J,φ,a,d,e,completed,result,exclusion,fac,found,laws,top,
    scheme,comp,leading,obedient,lies,selected,ticket,fun D => every_pool F simple bliss D⟩

/-- Select each genuine cylinder once for the whole finite frame. Its quota
and personal reflected card hold simultaneously at the same cutoffs.
'Cards.plant' takes these cards for any licensed finite number of copies. -/
theorem cylinders {v : Extraction.Order} {S : Table R.family.book}
    {F : Final R.family v S} {l : Ultrafilter (ℕ × ℕ)} {r A : ℝ} {j m D : ℕ}
    (paid : Pool F l r j m D A) {ι : Type*} [Finite ι] (d : ι → ℕ) (fit : ∀ i, d i ≤ D)
    (field : (i : ι) → S.Field (d i)) :
    ∃ (Z : (i : ι) → R.family.label (d i))
      (Y : (i : ι) → ℕ × ℕ → R.family.label (d i)),
      (∀ i, S.project (d i) (Z i) = field i ∧ Tendsto (Y i) (l : Filter (ℕ × ℕ)) (𝓝 (Z i))) ∧
      ∀ᶠ u : ℕ × ℕ in (l : Filter (ℕ × ℕ)), ∀ i,
        Next.UVStress.quota R.family (d i) j u.1 u.2 (Y i u) ≤
          R.family.S.a j^(d i)*A*cost F (d i) r (field i) ∧
        Cards.PaidAt R.family.S u.1 u.2 m (R.family.beta u.1 u.2)
          (A * cost F (d i) r (field i)) (R.family.O u.1 u.2 (Y i u) 0) := by
  choose Z Y proj conv fee using fun i => (paid.budget (d i) (fit i)).coin (field i)
  exact ⟨Z,Y,fun i => ⟨proj i,conv i⟩,eventually_all.mpr fee⟩

end YM.Integration.WilsonOriginalAllOrderPublicFields
end
