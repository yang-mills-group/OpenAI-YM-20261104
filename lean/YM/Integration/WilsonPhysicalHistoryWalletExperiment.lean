import YM.Integration.WilsonPhysicalHistoryWalletReceiver
import YM.Integration.WilsonOffsetJointWick
import YM.Integration.WilsonPosteriorProjectionCommonRooted

/-! The original signed wallet enrollment of a complete finite detector and
one displaced occupied mark, at each of its two true physical placements. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryWalletExperiment
open Function Filter Finset Set Lattice RG Wilson Source Labels Next.Foundations
open PhysicalNext.Repeat.Legato WilsonConditionalTaylorLabels WilsonOffsetJointRoster
open FVA1Physical.Wilson FVA1Physical.Marked FVA1Physical.Round2.Curvature
open RGComparison.Core16 RGComparison.Core16.Spool WilsonOffsetJointWick
open scoped BigOperators Classical
variable {G : Gauge}

def ceiling (a : Roster G) : ℕ := Finset.univ.sup (fun j : Fin a.length=>(a.get j).1)

def cover (a : Roster G) (s : Finset (Fin a.length)) (j : ↥s) : CoverLabel G (ceiling a) :=
  ⟨⟨(a.get j.val).1,Nat.lt_succ_of_le (Finset.le_sup (f:=fun i : Fin a.length=>(a.get i).1) (Finset.mem_univ _))⟩,
    (a.get j.val).2⟩

theorem lamps_eq (a : Roster G) (s : Finset (Fin a.length)) :
    freshLamps (cover a s) = packet ⟨a,s⟩ := rfl

def opens (R : Run G) (a : Roster G) : ℕ :=
  max (R.t 0) (Finset.univ.sup (fun j : Fin a.length=>R.t (a.get j).1))

theorem admitted (R : Run G) (a : Roster G) (s : Finset (Fin a.length)) {j u : ℕ}
    (begun : opens R a ≤ j) (ju : j ≤ u) :
    R.t 0 ≤ j ∧ R.t 0 ≤ u ∧ ∀ h : ↥s, R.t (cover a s h).1.val ≤ u+1 := by
  have zero : R.t 0 ≤ j := (le_max_left (R.t 0) _).trans begun
  refine ⟨zero,zero.trans ju,?_⟩
  intro h
  exact (Finset.le_sup (f:=fun i : Fin a.length=>R.t (a.get i).1) (Finset.mem_univ h.val)).trans
    ((le_max_right _ _).trans (begun.trans (ju.trans u.le_succ)))

/-- Actual finite occupied distance; no radius or volume bound is assumed
and each physical endpoint may select a different foreground centre. -/
def reach {n : Side} {I : Type} [Fintype I] (b : Site n) (o : I → Site n) : ℕ :=
  Finset.univ.sup (fun i=>separation (o i-b) 0)

theorem reaches {n : Side} {I : Type} [Fintype I] (b : Site n) (o : I → Site n) (i : I) :
    separation (o i-b) 0 ≤ reach b o := Finset.le_sup (f:=fun h=>separation (o h-b) 0) (Finset.mem_univ i)

theorem literal {n : Side} (a : Roster G) (s : Finset (Fin a.length)) (i : Fin a.length) (hi : i∈s)
    (o : Fin a.length→Site n) (z e : Site n) (U : Config G n) :
    tally (freshLamps (cover a s)) (seated a s o i z) U -
      tally (freshLamps (cover a s)) (seated a s o i e) U =
    field a (s.erase i) o U * (one a i z U-one a i e U) := by
  exact WilsonOffsetJointRoster.paired a s i hi o z e U

end YM.Integration.WilsonPhysicalHistoryWalletExperiment

