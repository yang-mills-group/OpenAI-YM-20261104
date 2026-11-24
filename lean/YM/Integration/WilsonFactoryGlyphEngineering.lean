import YM.Integration.WilsonFactoryPhysicalGlyphs
import YM.Pert.Scale.Bank
import YM.RG12.Roof.Layout

/-! The reporting-scale dilation reads exactly the independently declared
engineering height of each physical glyph; no slot parity is prescribed. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryGlyphEngineering
open Function Finset Lattice Wilson Labels Maxwell Pert.RawLabels Pert.Scale RG Spec RG12
open MS MS.Menus MS.Theater MS.Local.Physical
open FVAAlt2 WilsonFactoryOnShellGlyphs
open scoped Classical BigOperators
variable {G : Gauge} (B : Deck G) (P : Frames G) (d : ℕ)

def column (q : Glyph B d) := enroll P d (primitive B d q)
def read : (Maxwell.freeTable P).Field d →ₗ[ℂ] (Glyph B d → ℂ) :=
  (spectrum B d).comp (physicalLabel P d)

theorem unique (q t : Glyph B d) :
    read B P d (column B P d q) t = (Pi.single q (1:ℂ) : Glyph B d → ℂ) t := by
  have he := (enroll_eq P).mp (physical_round P (column B P d q))
  have line : (observable G d).rangeRestrict (physicalLabel P d (column B P d q)) = Daylight B d q :=
    Subtype.ext (he.trans (glyph B d q))
  change (Daylight B d).equivFun ((observable G d).rangeRestrict (physicalLabel P d (column B P d q))) t = _
  rw [line,Module.Basis.equivFun_apply]
  simp [Module.Basis.repr_self,Pi.single_apply,Finsupp.single_apply,eq_comm]

theorem height (q : Glyph B d) (t : ℝ) :
    gear P d t (column B P d q) = (t:ℂ)^q.1.val • column B P d q := by
  unfold column
  rw [gear_inherit]
  have h := (pure_grade _ _).mp (Shop.isSeated B q.2.2)
  have ht : (primitive B d q).val.IsWeightedHomogeneous generation q.1.val := by
    intro i hi
    exact congrArg Prod.fst ((weight_slot i).symm.trans (h hi))
  rw [grow_weights ht,map_smul]

theorem coordinates (a : (Maxwell.freeTable P).Field d) (t : ℝ) (q : Glyph B d) :
    read B P d (gear P d t a) q = (t:ℂ)^q.1.val * read B P d a q := by
  have expand : a = ∑ i : Glyph B d,read B P d a i • column B P d i := comparator B d P a
  have raised : gear P d t a = ∑ i : Glyph B d, (read B P d a i * (t:ℂ)^i.1.val) • column B P d i :=
    (congrArg (gear P d t) expand).trans (by rw [map_sum]; simp only [map_smul,height,smul_smul])
  rw [raised,map_sum,Finset.sum_apply]
  simp only [map_smul,Pi.smul_apply,smul_eq_mul,unique]
  simp [Pi.single_apply,mul_comm]

/-- Vanishing is exact for every unfilled engineering summand, including
all lower ones; no bound or estimate on a separately chosen grade matrix. -/
theorem off (a : (Maxwell.freeTable P).Field d) (h : ℕ) (eig : gear P d 2 a=(2:ℂ)^h • a)
    (q : Glyph B d) (away : q.1.val ≠ h) : read B P d a q=0 := by
  by_contra hn
  have hx := congrArg (fun w => read B P d w q) eig
  change read B P d (gear P d 2 a) q = read B P d ((2:ℂ)^h • a) q at hx
  rw [coordinates,map_smul,Pi.smul_apply,smul_eq_mul] at hx
  have hc : (2:ℂ)^q.1.val=(2:ℂ)^h := mul_right_cancel₀ hn (by push_cast at hx;exact hx)
  have hr : (2:ℝ)^q.1.val=(2:ℝ)^h := by exact_mod_cast hc
  exact away ((pow_right_injective₀ (a:=(2:ℝ)) (by norm_num) (by norm_num)) hr)

end YM.Integration.WilsonFactoryGlyphEngineering
