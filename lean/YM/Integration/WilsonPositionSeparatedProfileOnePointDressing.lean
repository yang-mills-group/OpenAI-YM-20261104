import YM.Integration.WilsonPositionSeparatedProfileOnePointWave
import YM.Integration.WilsonPositionSeparatedProfileOnePointSpin

/-! Original field renormalization and coupling substitution preserve the
signed one-point Ward identity through every coefficient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileOnePointDressing
open Function Filter Set Finset Table Spec Pert Climb Lattice Maxwell
open XSpace XSpace.Normalize FVA2 FVA2.Scale MS MS.Book MS.Book.Program MS.Land PowerSeries
open scoped Classical BigOperators
variable {G : Gauge} {d : ℕ}

private theorem moved (T : Guard G d) (base : Base T) (s : Signed) (k : ℕ) (v : Sec G d) :
    (coeff k T) (ori s.ortho d v)=ori s.ortho d ((coeff k T) v) := by
  rcases eq_or_ne k 0 with rfl|hk
  · simp [base.zero]
  · exact (base.high k hk).2.2.2 s v

private theorem coupled (q : Program.Cn) (A : Way G d) (s : Signed) (x : Stage 1)
    (earlier : ∀k v,A 1 x k (fun _=>ori s.ortho d v)=A 1 x k (fun _=>v)) (k : ℕ) (v : Sec G d) :
    Facets.couple q A 1 x k (fun _=>ori s.ortho d v)=Facets.couple q A 1 x k (fun _=>v) := by
  unfold Facets.couple MS.Book.Program.substitute
  simp only [LinearMap.coe_mk,AddHom.coe_mk,_root_.sum_apply,smul_apply,smul_eq_mul,earlier]

theorem changed (T : Guard G d) (base : Base T) (q : Program.Cn) (A : Way G d) (s : Signed) (x : Stage 1)
    (earlier : ∀k v,A 1 x k (fun _=>ori s.ortho d v)=A 1 x k (fun _=>v)) (k : ℕ) (v : Sec G d) :
    Facets.actMark T (Facets.couple q A) 1 x k (fun _=>ori s.ortho d v)=
      Facets.actMark T (Facets.couple q A) 1 x k (fun _=>v) := by
  let Z:=Facets.couple q A 1 x
  change Dframe.status T Z k (fun _=>ori s.ortho d v)=Dframe.status T Z k (fun _=>v)
  rw [Dframe.seen,Dframe.seen]
  apply sum_congr rfl
  intro a _
  let w:=(coeff (a (some 0)) T) v
  have original : Normalize.pulseU a T (fun _ : Fin 1=>v)=fun _=>w := by
    funext i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    rfl
  have turned : Normalize.pulseU a T (fun _ : Fin 1=>ori s.ortho d v)=fun _=>ori s.ortho d w := by
    funext i
    have hi:i=0:=Subsingleton.elim _ _
    subst i
    exact moved T base s _ v
  rw [original,turned]
  exact coupled q A s x earlier _ w

theorem coefficient (C : Family G) (simple : G.Simple) {O : Booked (Press.portDeck G)} (M : MS_Data G O)
    (ν : ℝ) (T : Guard G d) (base : Base T) (q : Program.Cn) (s : Signed) (x : Stage 1) (k : ℕ) (v : Sec G d) :
    Facets.actMark T (Facets.couple q (Equator.wave ν M d)) 1 x k (fun _=>v-ori s.ortho d v)=0 := by
  rw [WilsonPositionSeparatedProfileOnePointSpin.subtraction,
    changed T base q (Equator.wave ν M d) s x (WilsonPositionSeparatedProfileOnePointWave.wave C M simple ν d s x) k v,
    sub_self]

end YM.Integration.WilsonPositionSeparatedProfileOnePointDressing
