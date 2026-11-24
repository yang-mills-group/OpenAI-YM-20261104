import YM.LocalLTE.Brochure.Paged
import YM.LocalLTE.MarkPT.Sale
/-! overlay additive adjustments. uses HBump admissible.Up.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Overlay.Bands
open Function Filter Lattice RG Pressure Push Wilson Marker Finset MeasureTheory
open Next.Foundations Push.AbsoluteSums
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c:Side}(P:Rep G c) {V:Type} [DecidableEq V] {Qt: Marker.Census V}(A B D:Bands Qt P) {w:V→ℝ} {a b d s b' Y:ℝ}
-- `C` entries unchanged only.B
structure InInk : Prop where
    oil : A.origins=B.origins
    oilD: A.origins=D.origins
    creak: A.support=B.support
    creakD:A.support=D.support
    seats:A.rays=B.rays
    seatD:A.rays=D.rays
    H0:A.marks=B.marks
    source : A.units=B.units
    constant : A.entries=B.entries
variable (h:InInk P A B D) (c':ℂ) -- M change A→B with H_B=H_A + c*.H_D.
variable (hp:B.H=A.H+c' • D.H) (hA:A.Active)(hD:D.Active)
include h hp hA hD
lemma InInk.acts : B.Active:=by
    obtain ⟨hu,ho,hS,hS',he,hT,hy,hV,hG⟩:=h
    refine ⟨fun i=>he ▸ hA.proper i,fun i j ht=>?_,fun i=>?_,fun i j=>hy ▸ hA.occurs i j, fun i j hn n hn' => hu ▸ hA.retained i j (hG.symm ▸ hn) n (hy.symm ▸ hn'), fun i j=> hG ▸ hA.inspects i j,fun i j v hv=> hA.keeps i j v (hG.symm ▸ hv),fun i j=> hG ▸ hA.meas i j,fun i j=>hG ▸ hA.invi i j⟩
    · rw [← hu, ← hS]; exact hA.pins i j (he.symm ▸ ht)
    rw [←hS,hp]; exact regular_add (hA.regular i) (regular_smul c' (hS'.symm ▸ hD.regular i))
variable {a' Y':ℝ} (hr:A.Radial w a b d Y) (hv:D.Radial w a' b' s Y')
include hr hv
lemma InInk.pay : B.Radial w a (b+‖c'‖*b') d Y:=by
    obtain ⟨hu,ho,hS,hS',he,hT,hy,hV,hG⟩:=h
    refine ⟨hr.pure,fun i=> hV ▸ hr.localU i,hr.factor,?_,?_⟩; rotate_left
    · obtain ⟨s,h,hy'⟩:= hr.hits; exact ⟨s,hG ▸ h,hy ▸ hy'⟩
    obtain ⟨u,h,hf⟩:= hr.bulk; obtain ⟨v,hv',hg⟩:= hv.bulk; refine ⟨fun i=> u i+ ‖c'‖*v i,fun i=> ⟨add_nonneg (h i|>.1) (mul_nonneg (norm_nonneg _) (hv' i|>.1)),fun j hj=>?_⟩, fun i=>?_⟩
    · rw [← hu,← hS,hp]; refine bound_add (hA.regular i) (regular_smul c' (hS'.symm ▸ hD.regular i)) ((h i).2 j (?_)) (bound_smul c' (?_))
      · exact he.symm ▸ hj
      rw [ho,hS']; exact (hv' i).2 j ((hT ▸ (show j∈ (A.rays i).val from he.symm ▸ hj)))
    convert budget_plus (hf i) (budget_scale (norm_nonneg c') (hg i)) using 1; funext j; rw [← he, ← hT,← hS, ←hS']; unfold BudgetPoint.mass; split<;>ring
end YM.Overlay.Bands
