import YM.Tree.Pines
/-!
# Center tree repeated blockwise even on auxiliary meshes.

No permutations claimed. The same tree orientation commutes with **all** sign flips (at non-root slots).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Woody
open Lattice Laurent Tree Function Filter Finset
open scoped Topology BigOperators ComplexConjugate
variable {L c f: Side}
def skew (q: Cover) := (univ: Finset Axis).filter fun i=> q i≠0
def firstA (q:Cover):Axis:= if h:(skew q).Nonempty then (skew q).min' h else 0
def riseA (p:Site L):Step := let x:=firstA (lift p); if lift p x < 0 then posDir x else negDir x
lemma firstAt (q:Cover)(hq:q ≠ 0) : q (firstA q) ≠ 0:=by
   have he:∃ i:Axis,q i≠0:=by by_contra! hx; exact hq (funext hx)
   obtain ⟨i,hi⟩:=he; have hb:(skew q).Nonempty:=⟨i,by simp [skew,hi]⟩
   rw [firstA,dif_pos hb]; exact (mem_filter.mp (min'_mem _ hb)).2
lemma rises (s:Signed)(hp:∀ i:Axis,s.perm i=i)(h:Odd L.val) {p:Site L}(hg:p ≠ 0): riseA (s.act p) = (riseA p).rotate s := by
    have he: lift p ≠ 0:=by intro hz; apply hg; rw [← wrap_lift p,hz,map_zero]
    let x := firstA (lift p)
    have hu(i): s.act (lift p) i = if s.flip i then - lift p i else lift p i:= by
        nth_rw 1 [← hp i]; rw [s.act_at]
    have hz: skew (s.act (lift p)) = skew (lift p):=by ext i; simp only [skew,mem_filter,hu]; by_cases hk:s.flip i<;>simp [hk]
    have hx:firstA (s.act (lift p))=x:=by unfold x firstA; simp only [hz]
    have hy: lift p x ≠ 0:=firstAt _ he
    change (ite (lift (s.act p) _ < _) _ _) = (ite _ (posDir x) (negDir x)).rotate s
    rw [Ratio.lift_signed_of_odd h]; simp only [hx,hu]
    change (if (if s.flip x then - lift p x else lift p x) < 0 then posDir x else negDir x) = (if lift p x < 0 then posDir x else negDir x).rotate s
    cases hk:s.flip x
    · by_cases hh : lift p x < 0 <;> simp [hh,Step.rotate,posDir,negDir,hk,hp]
    by_cases hh : lift p x < 0
    · simp [hh,hh.le,Step.rotate,posDir,negDir,hk,hp]
    simp [hh,(by omega : 0 < lift p x),Step.rotate,posDir,negDir,hk,hp]
lemma leaves (g: Ratio c f) (i: Site f): leaf g i ↔ g.residue i ≠ 0:=not_congr (g.root_id i)
-- oriented from more distant sites
lemma inward (g:Ratio c f)(h:Odd g.count.val)(x:Site f)(hx:leaf g x):
    let b:=x+(riseA (g.residue x)).vec
    size (lift (g.residue b)) < size (lift (g.residue x)) ∧ g.parent b= g.parent x:=by
    have he:lift (g.residue x)≠ 0:=by
        intro h; apply (leaves g _).mp hx; rw [← wrap_lift (g.residue x),h,map_zero]
    let q:=lift (g.residue x); let a:=firstA q; let d:=riseA (g.residue x); intro b
    have hD:d=if q a<0 then posDir a else negDir a:= rfl
    have ha: q a≠0:=firstAt _ he; let L:=g.count.val/2
    have hh(i : Axis)(hi:i≠a) : (q + d.vec:Cover) i = q i := by rw [hD]; split <;> simp [hi]
    have hz : q + d.vec ∈ box L := by
       rw [box_iff_layers]; intro i
       have hk:q i∈ layers L := (box_iff_layers ..).mp (g.half_box h (g.residue x)) i
       by_cases H : i=a
       · subst i; rw [hD]; unfold layers at *; split <;> simp at * <;> omega
       rw [hh _ H]; exact hk
    obtain ⟨h1,h2⟩:= g.internal (i:=d) h hz; refine ⟨?_,h2⟩
    change size (lift (g.residue (x+d.vec))) < size q; rw [h1]; change size (q+d.vec)< size q
    have hu: ((q+d.vec:Cover) a).natAbs<(q a).natAbs:=by rw [hD]; split <;> simp <;> omega
    refine sum_lt_sum (fun i _=>?_) ⟨a,mem_univ _,hu⟩; by_cases H: i=a
    · subst i; exact hu.le
    rw [hh _ H]
def forest (g:Ratio c f)(h:Odd g.count.val): Forest g where
  up i := riseA (g.residue i)
  height i := size (lift (g.residue i))
  rise i := fun hi=> (inward g h i hi).1
  stays i := fun hi=> (inward g h i hi).2
  bound i := by
    let q:=lift (g.residue i); unfold Laurent.size
    apply le_trans (b:=∑ _ : Axis, g.count.val) (sum_le_sum fun j _ ↦ ?_) (by simp [Axis])
    have hi : q j∈ layers (g.count.val/2) := (box_iff_layers ..).mp (g.half_box h (g.residue i)) j
    unfold layers at hi; rw [mem_Icc] at hi; change (q j).natAbs ≤ g.count.val; omega
end YM.OPE.Woody
