import YM.Integration.WilsonThermometerWeakLongOccurrences

/-! The charged finite list sums exactly to the signed physical long reading on every
group configuration before the recourse to the smaller healthy sheet. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakLongReading
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open WilsonThermometerWeakTaylor WilsonThermometerWeakRetainedRow WilsonThermometerWeakLongOccurrences
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {N k p d m:ℕ} {V:Type} [Fintype V] [DecidableEq V]
local notation "ℙ" => C.path.rep N p k

theorem original (X:Coefficient (C.labels.level d) (C.side k p)) (form:X.Format 0 C.params ℙ)
    {κ cash:ℝ} (income:X.remBound 0 ℙ κ cash) {ζ:V→Site (C.side k p)} (s:Signed) (r:Prop) (x:V)
    (U:Config G (C.side k p)):
    (∑ j,(filed (m:=m) X form (ζ:=ζ) s r x j).amount (ℙ).p.threshold U)=
      Poly.send (slot x) (dot r (distant X N m (pull s (ζ x) U))) := by
  let t:=(ℙ).p.threshold
  let K (j:Far (P:=ℙ) X m):Keepat (C.side k p):=⟨X.support j,form.origin j⟩
  let U':=pull s (ζ x) U
  let F (j:Far (P:=ℙ) X m):=X.maskedTerm ℙ j U'
  have hf:Summable F:=((Coefficient.regular_series income).summable U').subtype _
  let read (a:Keepat (C.side k p)):=masked t a.val (field X N m a) U'
  have he a:read a=∑' j,if K j=a then F j else 0:=by
    by_cases ha:Healthy t a.val U'
    · unfold read;rw [masked_eq _ _ _ _ ha];apply tsum_congr;intro j
      by_cases h:X.support j=a.val
      · rw [if_pos h,if_pos (Subtype.ext h)]
        exact (masked_eq t (X.support j) (X.regular j) U' (h.symm ▸ ha)).symm
      rw [if_neg h,if_neg (fun e=>h (congrArg Subtype.val e))]
    unfold read;rw [masked_ne _ _ _ _ ha];symm
    apply (tsum_congr (g:=fun _=>0) ?_).trans tsum_zero
    intro j;split
    · rename_i h;exact masked_ne t (X.support j) (X.regular j) U' (show ¬Healthy t (X.support j) U' from (show X.support j=a.val from congrArg Subtype.val h).symm ▸ ha)
    rfl
  have finite (a:Finset (Keepat (C.side k p))):
      (∑ j∈a,(filed (m:=m) X form (ζ:=ζ) s r x j).amount t U)=Poly.send (slot x) (dot r (∑ j∈a,read j)):=by
    induction a using Finset.induction_on with
    | empty => simp only [Finset.sum_empty,dot_zero,Poly.send_zero]
    | insert j a hj ia =>
      rw [Finset.sum_insert hj,ia,Finset.sum_insert hj,dot_add,send_plus];congr 1
      exact congrArg (Poly.send (slot x)) (pr_dot s (ζ x) r U j.val t (field X N m j)).symm
  rw [finite];apply congrArg (Poly.send _);apply congrArg (dot r)
  simp_rw [he];exact pack_complex F K hf

end YM.Integration.WilsonThermometerWeakLongReading
end
