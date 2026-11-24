import YM.Integration.WilsonCenteredProductBooking
import YM.Integration.WilsonCenteredCanonicalFiling
import YM.Integration.WilsonMacroscopicRichEnrolledFiling

/-! Full engineering-horizon filing of a finite signed microscopic product
on the original Wilson hierarchy, including every independently placed child.
The finite book constructed at the top is sufficient for an exact fixed-date
reading. Its unrestricted top fare may depend on the regulators. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredPositiveFiling
open Function Finset Filter Lattice RG Wilson Labels Source Extra.Histories PhysicalNext.Repeat.Legato
open Trace.Physical Trace.Physical.GermGraph RG16 RG16.Literal RG12 Bid Next.Foundations
open WilsonCenteredProductBooking
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) (simple : G.Simple) {N p : ℕ} {J : Type}
  {I : J → Type} (grades : ∀ j,I j → ℕ) (v : ∀j t,R.family.label (grades j t))
  (sites : ∀j,I j → Site (R.family.side N p)) (faces : ∀j,Finset (I j)) (c : J → ℂ) (taken : Finset J)
local notation "Y" => source R grades v sites faces c taken
local notation "F" d:max => R.family.labels.level d

theorem booked (d m : ℕ) (refs : ∀j ∈ taken, ∀ t,R.t (grades j t) ≤ N) (start : R.family.ref d ≤ m) (top : m ≤ N)
    (funded : WilsonCenteredCaptureClock.first R simple ≤ N) :
    ∃ (z : R.family.label d) (E : ℝ), Next.UVStress.quota R.family d N N p z ≤ 2*E ∧
      ∀ i, m ≤ i → ∀ (live : i ≤ N) (opened : Opened R.family d i p),
        Booked R.family N p d Y i live ∧
        mCost R.family d N p i (topReport R.family N p d R.makes i opened live Y-
          (R.family.factory d N p).terminal.symm z) ≤ E/gainChart R.family.path N i :=by
  have gross := WilsonCenteredProductBooking.original R simple grades v sites faces c taken d refs (start.trans top) funded
  obtain ⟨q,r,⟨form,paid⟩,printed⟩:=gross
  let fee:=max r ((F d).coeffSize q.x)
  have rest : q.remBound 0 (R.family.path.rep N p N) (safety R.family N) fee :=by
    obtain ⟨a,b,h1,h2,spent,rest⟩:=paid
    exact ⟨a,b,h1,h2,spent.trans (le_max_left _ _),rest⟩
  have cont : Continuous Y := continuous_finsetSum _ fun j _=> continuous_const.mul
    (continuous_finsetProd _ fun t _ =>R.family.continuousO N p _ _ _)
  obtain ⟨z,quota,all⟩:=WilsonMacroscopicRichEnrolledFiling.original R.family N N m p d R.makes
    (R.again simple).1.scrim Y cont q fee 1 zero_lt_one start top le_rfl form rest (le_max_right _ _) printed
  exact ⟨z,_,quota,all⟩

/-- The actual booked cutoff panel can be heard on the received dated
representation whenever its literal numerator is the complete stated credit. -/
theorem original (d i : ℕ) (refs : ∀j ∈ taken, ∀ t,R.t (grades j t) ≤ N)
    (funded : WilsonCenteredCaptureClock.first R simple ≤ N) (opened : Opened R.family d i p) (live : i ≤ N)
    {P : Rep G (R.family.side i p)} (same : P.p=(R.family.path.rep N p i).p)
    (quiet : ∀U,(R.family.path.rep N p i).eval U=P.eval U)
    (q : Coefficient (F d) (R.family.side i p)) (form : q.Format 0 R.family.params P) {κ t : ℝ} (paid : q.remBound 0 P κ t)
    (printed : ∀U,credit R.family N p d Y i live U=q.density 0 (R.family.localSection d) P U) :
    readPage R.family N p d Y i live = Germ.projection (F d) R.family.params P.p.threshold 0 q ∧
    topReport R.family N p d R.makes i opened live Y = (fitting d N p i R.makes opened live).symm
      (Germ.projection (F d) R.family.params P.p.threshold 0 q) :=by
  obtain ⟨_,_,_,all⟩:=booked R simple grades v sites faces c taken d i refs opened.post live funded
  exact WilsonCenteredCanonicalFiling.original R Y opened opened.post live (all i le_rfl live opened).1
    same quiet q form paid printed

end YM.Integration.WilsonCenteredPositiveFiling
