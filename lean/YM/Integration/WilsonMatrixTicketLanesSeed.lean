import YM.RG17.Joint

/-! Keep the first physical field extension of the original RG17 construction
on a previously purchased base and seed of its actual family.  The base is
used intact, so other estimates on this particular field quotient survive. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonMatrixTicketLanesSeed
open YM.PhysicalNext YM.PhysicalNext.Repeat YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
open Spec Climb

section compare
open Pert Maxwell Org Next.UVStress
variable {C:Family G}
-- Factor the FirstExtension part from the baseline FirstTarget.
private lemma attached {S:Table C.book} {f : Extraction.Order} {I : IR (C:=C) S} {W : DiffPlan S}
    {M : MaxwellData C} {X : Scaling S} (p : Pert.Supplier f W M I X) {c U J} (h : Tab S W M I p.uv c U J)
    (F:Spec.Final C f S) (eqb:F.sector=⟨W,mill M I c U,J⟩) (hg:G.Simple)
    (hd : M.T.W=Maxwell.Free.scheme C.labels) (hK : M.T.K=Maxwell.Free.gear C.labels)
    (hj : M.T.J=YM.UVNext.FreeStress.torch C.book.grid 1) : Pert.FirstExtension F X := by
  have hm : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hg hd hj,inv_neg,inv_one,neg_smul,one_smul,hj,common_stress]
    rfl
  have he : F.sector.derivatives=W := congrArg Spec.Algebra.derivatives eqb
  refine ⟨?_,fun n j q is a K hp hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : F.sector.energy=J)]
    have hh := mixed_leading p h q is a j hp hsep he
    rw [hm] at hh; exact hh
  · revert he; cases F with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hK]
  exact rotation_lead p h d j
end compare
open Next.UVStress Analysis Org Acme

/-- Run the post-extraction part of RG17.Joint on the specified table and
its actual derivative map. The comparison grants concern this same Final. -/
theorem original (R : Run G) (hG : G.Simple)
    (L : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (f : Extraction.Order) {A : Table R.family.book} {L' : ℕ → Table R.family.book}
    {R' : Bin A} {S : Table R.family.book} {E : DiffPlan S}
    (hA : Base R.family f A L' R' S E) (s : Seed R.family f S) :
    ∃ (F : Spec.Final R.family f S) (X : Climb.Scaling S),
      F.sector.derivatives = E ∧ OPE.Services R.family f S ∧ Pert.FirstExtension F X := by
  obtain ⟨hT,hq,hV,-,-,-,-,hW⟩:= R.bought _ R.tuning.receipts _ R.accepts R.stories R.doors R.makes R.carries R.books
  obtain ⟨hc,hF,hQ,hS,hCn,B',-,-,U',F',X',-,h'⟩:= hT.reception
  let C:=R.family
  have hv: Ribbons.Created C:= ⟨_,R.t,R.stories,rfl⟩
  have hπ:Acme.Aroma C:= ⟨Ribbons.laurelE C hG hS hV hq hv hF,hq, Ribbons.fugacious C hG hV⟩
  obtain ⟨T₀,hM0,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M, hJ, hM, hK, _, _, ht0, hd⟩ := YM.UVNext.FreeStress.fire hG T₀ 1 one_ne_zero
  have hh := M.hT.smooth
  have hG' : East.CompleteWeak C f:= hW _
  have hs := grilled C hF hS hq s.copies
  have hL := realizes_stations s.cutoff s.generic s.ordered s.kernel.smooth hh M.hT.spin (fun N D R hr=>
    hG' N D R (zero_lt_one.trans_le hr) hh _)
  obtain ⟨hf,I,X,hI,hX,hY,hZ,hM',hp,ha⟩ := readyA s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready
    hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd hL hπ
  let p : Pert.Supplier f E M I X :=
    ⟨⟨s,hf,hp,ha,hs⟩,hA.clean.ready,hA.clean.tilt,hI,hX,hd,hY,hZ,hM'⟩
  have ht := Bid.station M E I p.uv YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c, U, J, H, K, hK'⟩ := ht.picks E M I p.uv p.ider p.deriv
  obtain ⟨F,hFa⟩:= Pert.withFinal hc p.uv c U J H hK'
  refine ⟨F,X,congrArg Spec.Algebra.derivatives hFa,⟨hs,hG,⟨_,_,_,L⟩,A,L',R',E,hA⟩,
    attached p H F hFa hG (hM.trans (congr_arg Lighthouse.W hM0)) (hK.trans (congr_arg Lighthouse.K hM0)) hJ⟩
end YM.Integration.WilsonMatrixTicketLanesSeed
