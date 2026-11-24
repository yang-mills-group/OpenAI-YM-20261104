import YM.FVA2.Main
import YM.XSpace.Panorama

/-! The actual mass-independent adjustment selected by the original Wilson
prescription. Its formal coefficients are real permitted field changes, with
zero equal-dimension component at every positive perturbative order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousCoefficients
open Function PowerSeries Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale
open scoped Classical
variable {G : Gauge} (Z : WilsonPrescription G)

structure Warrant : Prop where
  scheme (d : ℕ) : Measure.PowerCondition d (Measure.start Z.scheme Z.criterion d) (Measure.adjust Z.scheme Z.criterion d)
  includes {d e : ℕ} (h : d≤e) : Walk h (Measure.adjust Z.scheme Z.criterion d) (Measure.adjust Z.scheme Z.criterion e)

theorem purchased {hG : G.Simple} {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b) : Warrant Z := by
  let B:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  exact ⟨fun d=>Measure.adj Z.scheme Z.criterion 0 M σ (d:=d) hG B.Taylor B.still B.base,
    fun h=>Measure.grades Z.scheme Z.criterion 0 M σ hG B.Taylor B.still B.base h⟩

def letter (d n : ℕ) : Change G d :=
  if n=0 then 0 else if h:coeff n (Measure.adjust Z.scheme Z.criterion d)∈Change G d then ⟨_,h⟩ else 0

def dossier (d n : ℕ) : MoveSpace G d := guide G d (letter Z d n)

theorem positive (H:Warrant Z) (d : ℕ) {n : ℕ} (hn:n≠0) :
    (letter Z d n).val=coeff n (Measure.adjust Z.scheme Z.criterion d) := by
  rw [letter,if_neg hn,dif_pos ((H.scheme d).scale.high n hn)]

theorem absent (H:Warrant Z) (d n : ℕ) : Level.diag (letter Z d n).val=0 := by
  by_cases h:n=0
  · subst n
    simp [letter]
  rw [positive Z H d h]
  have hc:=congrArg (coeff n) (H.scheme d).strict
  simpa only [diagonal,coeff_mk,coeff_one,if_neg h] using hc

theorem chart (H:Warrant Z) {d e : ℕ} (hd:d≤e) (n : ℕ) (v : Sec G d) :
    (letter Z e n).val (up hd v)=up hd ((letter Z d n).val v) := by
  by_cases h:n=0
  · subst n
    simp [letter]
  rw [positive Z H e h,positive Z H d h]
  exact H.includes hd n v

end YM.Integration.WilsonPositionHomogeneousCoefficients

