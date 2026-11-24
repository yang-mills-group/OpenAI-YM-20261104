import YM.Integration.WilsonPositionOriginalDressedQPathHearing
import YM.Integration.WilsonPositionOriginalDressedQFourTerms
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredSealedReplica
open Finset Lattice Wilson RG Cells Push.GridApprox OPE.Therm PhysicalNext.Repeat.Legato
open Set MeasureTheory QLocalPhysicalPathKernel WilsonMacroscopicForwardTransfer
open WilsonPositionOriginalDressedQFailedPath
open scoped Classical Topology BigOperators
variable {V:Type} {G:Gauge} {n:Side}
def word (B:V → Config G n → ℂ)(s:Finset V)(U:Config G n):ℂ:=∏v∈s,B v U

private theorem wordEmpty (B:V → Config G n → ℂ):word B ∅=fun _=>1:=by
  funext U
  simp [word]

private theorem wordInsert [DecidableEq V] (B:V → Config G n → ℂ)
    (v:V)(s:Finset V)(hv:v∉s):word B (insert v s)=B v*word B s:=by
  funext U
  simp only [word,prod_insert hv,Pi.mul_apply]

private theorem wordEnv (B:V → Config G n → ℂ)(h:∀v,Envelope (B v))(s:Finset V):
    Envelope (word B s):=by
  classical
  induction s using Finset.induction_on with
  | empty=>
    rw [wordEmpty]
    exact ⟨measurable_const,1,by simp⟩
  | insert v s hv ih=>
    rw [wordInsert B v s hv]
    exact (h v).mulC ih

private theorem wordLocal (B:V → Config G n → ℂ)(H:V → Set (Site n))
    (loc:∀v,LocalOn (H v) (B v))(s:Finset V):LocalOn (⋃v∈s,H v) (word B s):=by
  intro U W hit
  apply Finset.prod_congr rfl
  intro v h
  apply loc v U W (agrees_mono hit ?_)
  exact fun x hx=>Set.mem_iUnion₂.mpr ⟨v,h,hx⟩

variable (R:Run G){N per i:ℕ}
local notation "step" => backTo R.family.path N per (Nat.le_succ i)

/-- Every selected proper face of an independently supported coarse roster uses
one common draw of the original block. -/
theorem split (L:V → Config G (R.family.side i per) → ℂ)(H:V → Set (Site (R.family.side i per)))
    (paid:∀v,Interior (H v) (L v))(apart:Pairwise fun v u=>Disjoint (H v) (H u))(s:Finset V):
    step (word L s)=word (fun v=>step (L v)) s:=by
  classical
  induction s using Finset.induction_on with
  | empty=>
    simpa only [wordEmpty] using backTo_const R.family.path N per (Nat.le_succ i) 1
  | insert v s hv ih=>
    have hh:Disjoint (H v) (⋃u∈s,H u):=by
      apply Set.disjoint_iUnion_right.mpr
      intro u
      apply Set.disjoint_iUnion_right.mpr
      intro hu
      exact apart (fun eq=>hv (eq ▸ hu))
    have aligned:step (L v*word L s)=step (L v)*step (word L s):=by
      rw [backTo_next R.family.path N per (le_refl i),backTo_next R.family.path N per (le_refl i),backTo_next R.family.path N per (le_refl i)]
      simpa using back_factors (R.family.path.levels.blocks i per).branches (cylinder_env (paid v))
        (wordEnv L (fun j=>cylinder_env (paid j)) s) (paid v).localSites
        (wordLocal L H (fun j=>(paid j).localSites) s) hh _
    rw [ih] at aligned
    simpa only [wordInsert _ v s hv] using aligned

/-- A complete physical branch at two dates has the same upper microscopic
reading, retaining arbitrary correlations among all fine factors. -/
theorem branch (live:i<N)(F:Config G (R.family.side (i+1) per) → ℂ)(fine:Envelope F)
    (L:V → Config G (R.family.side i per) → ℂ)(H:V → Set (Site (R.family.side i per)))
    (paid:∀v,Interior (H v) (L v))(apart:Pairwise fun v u=>Disjoint (H v) (H u))(s:Finset V):
    (∫ω:ConfigurationPath R per,F (ω (i+1))*word L s (ω i) ∂path R.family R.makes N per)=
      ∫U,F U*word (fun v=>step (L v)) s U ∂scene R.family.path N per (i+1):=by
  classical
  letI:IsProbabilityMeasure (scene R.family.path N per (i+1)):=probability R.makes.wilson live
  have lc:=wordEnv L (fun j=>cylinder_env (paid j)) s
  have physical:=WilsonPositionOriginalDressedQPathHearing.measured R live F (word L s) fine lc
  have common:=joint (C:=R.family) R.makes (Nat.le_succ i) live F (fine.integrableC _) (word L s) lc
  rw [split R L H paid apart s] at common
  exact physical.trans common
end YM.Integration.WilsonRegisteredSealedReplica
