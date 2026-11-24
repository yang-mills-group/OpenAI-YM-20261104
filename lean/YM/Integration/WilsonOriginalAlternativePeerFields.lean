import YM.Integration.WilsonOriginalAlternativeHybrids
import YM.Integration.WilsonOriginalAlternativeHearing

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativePeerFields
open Finset Function Marker RG Lattice Wilson QuadraticLocal WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction
open WilsonOriginalAlternativeHybrids WilsonOriginalAlternativeHearing
open scoped Classical BigOperators
variable {V:Type} [Fintype V] [DecidableEq V] (J:Census V)

theorem struck (p:Poly J) (C:V→ℂ) (s:J.Mode) (X:Finset V) (j:V) (outside:j∉X) (inside:j∈s.val):
    (read J (Function.update (WilsonOriginalAlternativeHybrids.route X) j 2) (stamped J p C)).part s=
      (p.part (live J s (insert j X))-p.part (live J s X)*C j)*(∏z∈s.val\(insert j X),C z):=by
  rw [WilsonOriginalAlternativeExchange.original J p C (WilsonOriginalAlternativeHybrids.route X) j s inside]
  have all:Function.update (WilsonOriginalAlternativeHybrids.route X) j 0=WilsonOriginalAlternativeHybrids.route (insert j X):=by
    funext v
    by_cases eq:v=j
    · subst v;simp [WilsonOriginalAlternativeHybrids.route]
    · simp [WilsonOriginalAlternativeHybrids.route,eq]
  have rest:Function.update (WilsonOriginalAlternativeHybrids.route X) j 1=WilsonOriginalAlternativeHybrids.route X:=by
    funext v
    by_cases eq:v=j
    · subst v;simp [WilsonOriginalAlternativeHybrids.route,outside]
    · exact Function.update_of_ne eq .. 
  rw [all,rest,WilsonOriginalAlternativeHybrids.original,WilsonOriginalAlternativeHybrids.original]
  have matchSet : (s.val\X).erase j=s.val\(insert j X):=by
    ext v
    simp only [mem_erase,mem_sdiff,mem_insert]
    tauto
  have swap:(∏z∈s.val\X,C z)=C j*∏z∈s.val\(insert j X),C z:=by
    rw [←Finset.mul_prod_erase (s.val\X) C (mem_sdiff.mpr ⟨inside,outside⟩),matchSet]
  rw [swap];ring

theorem single (p:Poly J) (C:V→ℂ) (s:J.Mode) (j:V) (active:j∈s.val):
    (read J (Function.update (WilsonOriginalAlternativeHybrids.route ∅) j 2) (stamped J p C)).part s=
      (p.part (J.fire j)-p.part J.quiet*C j)*(∏z∈s.val.erase j,C z):=by
  rw [struck J p C s ∅ j (notMem_empty _) active]
  have fire:live J s (insert j ∅)=J.fire j:=by
    apply Subtype.ext
    simp [live,Census.fire,active]
  have quiet:live J s ∅=J.quiet:=by apply Subtype.ext;simp [live,Census.quiet]
  have set' : s.val\(insert j ∅)=s.val.erase j:=by ext v;simp;tauto
  rw [fire,quiet,set']

variable {G:Gauge} (C:Family G) {per f k N:ℕ} {o:V→Site (C.side k per)}
  {W:Rep G (C.side k per)} {X μ:Type} (A:Gallery X μ (o∘Prod.fst) W (board J))
  (x:X) (F:Config G (C.side k per)→Poly J) (P:Config G (C.side k per)→V→ℂ)
  (same:∀U,A.density x U=stamped J (F U) (P U))
include same in
theorem original (s:J.Mode) (kept:Finset V) (j:V) (outside:j∉kept) (inside:j∈s.val)
    (lower:f≤k):
    held C N per (source C per J A x (Function.update (WilsonOriginalAlternativeHybrids.route kept) j 2) s) lower=
      held C N per (fun U=>((F U).part (live J s (insert j kept))-(F U).part (live J s kept)*P U j)*
        ∏z∈s.val\(insert j kept),P U z) lower:=by
  apply congrArg (fun g=>held C N per g lower)
  funext U
  simp only [source,same]
  exact struck J (F U) (P U) s kept j outside inside

include same in
theorem peers (quiet:∀U,(F U).part J.quiet=(W.eval U:ℂ)) (s:J.Mode) (j:V) (inside:j∈s.val)
    (lower:f≤k):
    held C N per (source C per J A x (Function.update (WilsonOriginalAlternativeHybrids.route ∅) j 2) s) lower=
      held C N per (fun U=>((F U).part (J.fire j)-(W.eval U:ℂ)*P U j)*
        ∏z∈s.val.erase j,P U z) lower:=by
  apply congrArg (fun g=>held C N per g lower)
  funext U
  simp only [source,same,single J _ _ s j inside,quiet]

end YM.Integration.WilsonOriginalAlternativePeerFields
