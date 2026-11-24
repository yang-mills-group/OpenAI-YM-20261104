import YM.Integration.WilsonCapturedPrimaryOriginal
import YM.Integration.WilsonCapturedPrimaryReading
import YM.Integration.WilsonCapturedPrimarySmooth

/-! Two funded representations of the same Wilson numerator have identical
intrinsic measured field coefficients whenever they use the same threshold
and quiet density. Each retains all of its own compulsory addresses. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredCommonGerm
open Function Lattice Wilson RG Labels Source Next.Foundations Push.Local
open Trace.Physical.Germ WilsonCapturedPrimaryReading
open scoped Topology Classical

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d} {A : Hol G} {S : SectionData F}
  {o : Site n} {P Q : Rep G n} {u v : Coefficient F n}

private theorem measured {w κ t : ℝ} (read : Readable A S P.p n w) (form : u.Format o A P)
    (bill : u.remBound o P κ t) (p : Probe G d) :
    runProbe F p (projection F A P.p.threshold o u) = jet A p P.p.threshold o (reading S P o u) :=by
  have sectionPath := fun x => WilsonCapturedPrimaryOriginal.registered (o:=o) read x
  have regular := WilsonCapturedPrimarySmooth.original read.sound read.order sectionPath form bill
  exact WilsonCapturedPrimaryReading.probe read.sound read.fit read.order read.power sectionPath form bill regular p

/-- The chart quotient is the literal numerator divided by the full
Wilson vacuum. Its equality as a function determines every represented jet. -/
theorem original (point : P.p=Q.p) {w κ υ a b : ℝ} (read : Readable A S P.p n w)
    (left : u.Format o A P) (right : v.Format o A Q)
    (first : u.remBound o P κ a) (second : v.remBound o Q υ b)
    (quiet : ∀U,P.eval U=Q.eval U) (oath : ∀U,u.density o S P U=v.density o S Q U) :
    projection F A P.p.threshold o u=projection F A Q.p.threshold o v :=by
  have other : Readable A S Q.p n w :=point ▸ read
  have whole : reading S P o u=reading S Q o v :=by
    funext U
    unfold reading
    rw [quiet U,oath U]
  apply probes_injective F
  intro q
  rw [measured read left first,measured other right second,whole,point]

end YM.Integration.WilsonCenteredCommonGerm
