import YM.MergeProof.Summit
import YM.Pert.Deeper
import YM.Pert.Weak

import YM.Pert.Dense.Kernel
import YM.Pert.FirstTarget

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Dense
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec Next.UVStress
open scoped Topology ContDiff BigOperators
variable {G : Gauge}
open MergeProof.Acme in
lemma fromKernel (hG : G.Simple) {b : ℝ} (hb : 0<b) :∃ C:Family G, ∃ B: PhysicalNext.RankCovariance.Binding C,Rectangles C ∧
    C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∃ M : MaxwellData C,M.T.W = Maxwell.Free.scheme C.labels ∧ M.T.K = Maxwell.Free.gear C.labels ∧
    M.T.J = YM.UVNext.FreeStress.torch C.book.grid 1 ∧ Tensorial M.T.K M.T.J ∧ ∀ f : Extraction.Order,
    ∃ (g:Extraction.Order) (S:Table C.book)(I:IR (C:=C) S)(W:DiffPlan S)
      (X : Scaling S) (c : ℝ) (U : ∀ d, Spin.change S d) (J : S.Stress),
      ∃ l : Supplier (f.refine g) W M I X, Tab S W M I l.uv c U J ∧
      ∃ h : Final C (f.refine g) S, h.sector=⟨W,mill M I c U,J⟩ := by
  obtain ⟨C,B,hRect,hB,hP,hMat,hC,hM,hW,H,hQ,hF⟩:= deeperBinding hG hb
  obtain ⟨T',hM0,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M, hJ, hM, hK, _, _, ht0, hd⟩ := YM.UVNext.FreeStress.fire hG T' 1 one_ne_zero
  refine ⟨C,B,hRect,hB,hW,hMat,hP,M,hM.trans (congr_arg Lighthouse.W hM0),hK.trans (congr_arg Lighthouse.K hM0),hJ,hK.symm ▸ ht0,fun f => ?_⟩
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
  obtain ⟨hs,hG'⟩:= hQ (f.refine g) s.copies
  have hh := M.hT.smooth
  have hS := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=>
    hG' N D R (zero_lt_one.trans_le hr) hh _)
  obtain ⟨hf,I,X,hI,hX,hY,hZ,hM',hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready
    hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hS H
  let p : Supplier (f.refine g) E M I X :=
    ⟨⟨s,hf,hp,ha,hs⟩,hA.clean.ready,hA.clean.tilt,hI,hX,hd,hY,hZ,hM'⟩
  have ht := Bid.station M E I p.uv YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c, U, J, T, K, hK'⟩ := ht.picks E M I p.uv p.ider p.deriv
  exact ⟨g,_,I,E,X,c,U,J,p,T,withFinal hC p.uv c U J T hK'⟩

open Maxwell
set_option maxHeartbeats 4000000 in
theorem combined (hg : G.Simple) {b : ℝ} (hb : 0<b) : ∃ C : Family G, ∃ B: PhysicalNext.RankCovariance.Binding C, Rectangles C ∧ C.path.levels.clock.kernel.penalty=b ∧
    Extraction.Wcmain C ∧ MergeProof.Ribbons.Materials C ∧ MergeProof.Ribbons.Plenty C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book) (h : Final C (f.refine g) S), ∃ X : Scaling S, FirstExtension h X := by
  obtain ⟨C,B,hR,hc,hW,hMat,hP,M,hd,hK,hj,hT,hp⟩ := fromKernel hg hb
  refine ⟨C,B,hR,hc,hW,hMat,hP,fun f => ?_⟩
  obtain ⟨g,S,I,W,X,c,U,J,p,h,b,eqb⟩ := hp f
  have hm : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hg hd hj,inv_neg,inv_one,neg_smul,one_smul,hj,common_stress]
    rfl
  have he : b.sector.derivatives=W := congrArg Spec.Algebra.derivatives eqb
  refine ⟨g,S,b,X,?_,fun n j q is a K hK hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : b.sector.energy=J)]
    have hh := mixed_leading p h q is a j hK hsep he
    rw [hm] at hh; exact hh
  · revert he; cases b with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hK]
  exact rotation_lead p h d j
end YM.Pert.Dense
