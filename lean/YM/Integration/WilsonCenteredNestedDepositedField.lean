import YM.Integration.WilsonCenteredNestedRaised
import YM.Integration.WilsonCenteredNestedJointLinear

/-! Reassemble the entire inner field before applying the outer
multilinear response at the held real/rotation branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedDepositedField
open Function Filter Spec Extraction Table OPE OPE.Orbits OPE.Orbits.Reader
open OPE.Nesting OPE.Nesting.Atom WilsonCenteredNestedProjectedShadow
open WilsonCenteredNestedRealOrbit WilsonCenteredNestedJointLinear WilsonCenteredNestedRawRows WilsonCenteredNestedRawPair
open scoped Classical Topology BigOperators
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def grades (d f:ℕ) : Fin 2→ℕ := Fin.cons d (fun _:Fin 1=>f)
def roster (d:ℕ) (far:S.Tag) (w:S.Field d) : Labels S (grades d far.1) :=
  Fin.cons w (fun _:Fin 1=>far.2)

def outer (D H m:ℕ) (mc:Q.channels m) (far:S.Tag) (y:Fin 2→E4) (o:E4) (k:Ortho) (b:Bool) :
    S.Field D→ₗ[ℂ] ℂ :=
  (read F Q m H mc).comp ((field F Q.port H y o k b).toLinearMap (roster D far 0) 0)

lemma apply_outer (D H m:ℕ) (mc:Q.channels m) (far:S.Tag) (y:Fin 2→E4) (o:E4) (k:Ortho) (b:Bool)
    (w:S.Field D) : outer F Q D H m mc far y o k b w =
      read F Q m H mc (restored F Q.port H y (roster D far w) o k b) := by
  have hu (dec : DecidableEq (Fin 2)) :
      @update (Fin 2) (fun i=>S.Field (grades D far.1 i)) dec (roster D far 0) 0 w=roster D far w := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact @update_self (Fin 2) _ dec 0 w (roster D far 0)
    · exact @update_of_ne (Fin 2) _ dec j.succ 0 (Fin.succ_ne_zero j) w (roster D far 0)
  rw [outer,LinearMap.comp_apply]
  apply congrArg _
  have hh : ((field F Q.port H y o k b).toLinearMap (roster D far 0) 0) w =
      field F Q.port H y o k b (roster D far w) := congrArg (field F Q.port H y o k b) (hu _)
  exact hh.trans (WilsonCenteredNestedJointLinear.original F Q Q.port H y o k b _)

lemma actor {D:ℕ} (H m:ℕ) (mc:Q.channels m) (t:Menu.Cut Q D) (far:S.Tag)
    (y:Fin 2→E4) (o:E4) (k:Ortho) (b:Bool) :
    outer F Q D H m mc far y o k b (F.sector.derivatives.rise (Nat.le_of_lt_succ t.1.isLt) (Q.actor t.1.val t.2)) =
      face F Q Q.port H m mc y (placed F Q t far) o k b := by
  let v := placed F Q t far
  have small : degrees v ≤ grades D far.1 := by
    intro i
    fin_cases i
    · exact Nat.le_of_lt_succ t.1.isLt
    · exact le_rfl
  have h : (fun i=>F.sector.derivatives.rise (small i) (voices v i)) =
       roster D far (F.sector.derivatives.rise (Nat.le_of_lt_succ t.1.isLt) (Q.actor t.1.val t.2)) := by
    funext i
    fin_cases i
    · rfl
    · exact F.sector.derivatives.arrival Q.continuum.laws.toSymmetric Q.lifts _
  rw [apply_outer,←h,WilsonCenteredNestedRaised.original F Q]
  rfl

/-- The exact signed public contracted child sum is the nonlinear raw
prescription's outer response to the child's whole graded field. -/
theorem original (D H m:ℕ) (mc:Q.channels m) (v:Fin 2→S.Tag) (far:S.Tag)
    (x y:Fin 2→E4) (o:E4) (k:Ortho) (b:Bool) :
    joined F Q Q.port D H m mc v far x y o k b =
      outer F Q D H m mc far y o k b (restored F Q.port D x (voices v) (y 0) k b) := by
  let U := restored F Q.port D x (voices v) (y 0) k b
  let A := outer F Q D H m mc far y o k b
  have paid := congrArg A (assemble F Q D U)
  rw [map_sum] at paid
  simp_rw [map_sum,map_smul] at paid
  rw [←paid]
  unfold joined
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro c _
  change read F Q j.val D c U * _ = read F Q j.val D c U * _
  rw [←actor F Q H m mc (⟨j,c⟩ : Menu.Cut Q D) far y o k b]

end YM.Integration.WilsonCenteredNestedDepositedField
