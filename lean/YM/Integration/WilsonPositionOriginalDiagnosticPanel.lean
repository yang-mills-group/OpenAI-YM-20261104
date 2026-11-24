import YM.Integration.WilsonReportingFactorySingleton
import YM.Integration.ActualOriginalDictionary
import YM.XSpace.NormStab

/-! Through one horizon take precisely the original homogeneous film basis. Its entries
have actual funded singleton rows at their own grades, on the same Wilson cutoff.
Their read coordinates recover every field and keep the complete forced allowance. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalDiagnosticPanel
open Function Filter Finset Lattice Wilson RG Source Extraction Table Spec RG12 RG05Readout Address Native
open Extra.Histories MergeProof.Ribbons PhysicalNext.Repeat.Legato
open MS MS.Local.Physical MS.Menus MS.Lifting MS.Theater Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (B:Deck G) {H:ℕ}

def entrance (H:ℕ) : ℕ := univ.sup (fun a:Glyph B H=>R.family.ref a.size)

def entry (a:Glyph B H) : R.family.label a.size :=
  ActualOriginalDictionary.coordinates R B a.size a.grade a.2.2

def screen (d:ℕ) : R.family.label d →ₗ[ℂ] WickPol G :=
  (observable G d).comp (R.family.labels.level d).coords.symm.toLinearMap

def entered (a:Glyph B H) (m N per:ℕ) := WilsonReportingFactorySingleton.row R.makes a.size m N per (entry R B a)

def height {h:ℕ} (g:h≤H) (a:Glyph B h) : Glyph B H :=
  ⟨⟨a.size,Nat.lt_of_lt_of_le a.1.isLt (Nat.add_le_add_right g 1)⟩,a.2⟩

theorem nested {h:ℕ} (g:h≤H) (a:Glyph B h) (m N per:ℕ) :
    entered R B (height B g a) m N per=entered R B a m N per := rfl

theorem original_field (a:Glyph B H) (n:Side) (x:Site n) (U:Config G n) :
    (((ActualOriginalDictionary.dictionary R B).cylinder a.size a.grade a.2.2).O n x U:ℂ) =
      (R.family.localSection a.size).places (entry R B a) x U :=
  ActualOriginalDictionary.original_section R B a.size a.grade a.2.2 n x U

theorem issued {m N per:ℕ} (age:entrance R B H ≤ m) (live:m≤N) (a:Glyph B H) :
    let q:=entered R B a m N per
    let rep:=R.family.path.rep N per m
    q.Format 0 R.family.params rep ∧ q.x=entry R B a ∧
      q.remBound 0 rep (Real.sqrt (R.family.path.levels.clock.forcedAllowance m))
        ((R.family.path.levels.params m).columns*mass R.family a.size (entry R B a)) :=
  WilsonReportingFactorySingleton.signed R.makes (per:=per)
    ((le_sup (s:=univ) (f:=fun j:Glyph B H=>R.family.ref j.size) (mem_univ a)).trans age)
    live (entry R B a)

theorem exposed {m N per:ℕ} (age:entrance R B H ≤ m) (live:m≤N) (a:Glyph B H) :
    screen R a.size (entered R B a m N per).x=((Daylight B H) a).val := by
  rw [(issued R B (per:=per) age live a).2.1,readHeight]
  change observable G a.size ((R.family.labels.level a.size).coords.symm
     ((R.family.labels.level a.size).coords (ActualOriginalDictionary.filmLabel B a.size a.grade a.2.2)))=_
  rw [LinearEquiv.symm_apply_apply]
  rfl

def fee (x:Sec G H) : ℝ := ∑ a:Glyph B H, ‖(Daylight B H).repr x a‖ * mass R.family a.size (entry R B a)

/-- The same finite, once-funded panel reconstructs all axes, including the exact unit
and every derivative that belongs to the horizon. Field tests and kinetic normalization
may be imposed after this filing. -/
theorem panel {m N per:ℕ} (age:entrance R B H ≤ m) (live:m≤N) (x:Sec G H) :
    (∑ a:Glyph B H, (Daylight B H).repr x a • screen R a.size (entered R B a m N per).x)=x.val ∧
    (∑ a:Glyph B H, ‖(Daylight B H).repr x a‖ *
       ((R.family.path.levels.params m).columns * mass R.family a.size (entered R B a m N per).x)) =
      (R.family.path.levels.params m).columns * fee R B x := by
  constructor
  · simp_rw [exposed R B age live]
    calc
      _ = (shellSector G H).subtype (∑ a:Glyph B H, (Daylight B H).repr x a • (Daylight B H) a) := by
        simp only [map_sum,map_smul];rfl
      _ = x.val := congrArg (shellSector G H).subtype ((Daylight B H).sum_repr x)
  · simp_rw [(issued R B (per:=per) age live _).2.1]
    unfold fee
    rw [Finset.mul_sum]
    exact sum_congr rfl (fun _ _=>by ring)

end YM.Integration.WilsonPositionOriginalDiagnosticPanel
