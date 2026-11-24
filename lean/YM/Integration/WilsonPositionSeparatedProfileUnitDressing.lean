import YM.FVA2.Scale.Functions

/-! This computes the field-change and coupling substitution on the ordinary
unit moments, keeping every original coefficient of their common program. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileUnitDressing

open Function Set Finset PowerSeries XSpace XSpace.Normalize XSpace.Structure1
  FVA2 FVA2.Scale MS MS.Book MS.Book.Program
open scoped Classical BigOperators

variable {G : Gauge} {d n : ℕ}

private theorem ticket {k : ℕ} {a : Normalize.Days n} (mem : a∈Normalize.tally k n)
    (zero : ∀i,a (some i)=0) : a=Finsupp.single none k := by
  have total := (Normalize.totaled a).mp mem
  have none : a none=k := by simpa [Fintype.sum_option,zero] using total
  ext o
  cases o with
  | none => simpa using none
  | some i => simp [zero]

theorem marked (T : Guard G d) (hT : Base T) (A : Way G d) (x : Stage n)
    (c : Fin n→ℂ) (k : ℕ) :
    Facets.actMark T A n x k (fun i=>c i • leaf G d)=A n x k (fun i=>c i • leaf G d) := by
  let v (i : Fin n) := c i • leaf G d
  let e : Normalize.Days n := Finsupp.single none k
  have bought : e∈Normalize.tally k n := (Normalize.totaled e).mpr (by simp [e])
  change Dframe.status T (A n x) k v=A n x k v
  rw [Dframe.seen,Finset.sum_eq_single e]
  · have fv : Normalize.pulseU e T v=v := by
      funext i
      simp [Normalize.pulseU,e,hT.zero]
    simp [e,fv]
  · intro a mem ne
    obtain ⟨i,hi⟩ : ∃i,a (some i)≠0 := by
      by_contra! h
      exact ne (ticket mem h)
    apply (A n x (a none)).map_coord_zero i
    change (coeff (a (some i)) T) (c i • leaf G d)=0
    rw [map_smul,(hT.high _ hi).1,smul_zero]
  · intro absent
    exact (absent bought).elim

theorem coupled (q : Program.Cn) (A : Way G d) (x : Stage n) (v : Fin n→Sec G d)
    (c : ℂ) (base : ∀k,A n x k v=if k=0 then c else 0) (k : ℕ) :
    Facets.couple q A n x k v=if k=0 then c else 0 := by
  unfold Facets.couple MS.Book.Program.substitute
  simp only [LinearMap.coe_mk,AddHom.coe_mk,_root_.sum_apply,smul_apply,smul_eq_mul,base]
  simp [MS.Book.Program.cut,PowerSeries.coeff_one,mul_ite]

end YM.Integration.WilsonPositionSeparatedProfileUnitDressing
