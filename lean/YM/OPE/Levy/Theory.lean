import YM.OPE.Nesting.Endpoint
import YM.OPE.Levy.Curve
import YM.Pert.FirstTarget

/-!
# Joint supplier: actual weak free measuring frames and common OPE

Take the same stronger start as F3's `OPE.through_final` (here using the
same `noel_columns` instance directly), keeping the Maxwell-Emanate branch
and its leading `Pert.FirstExtension` data. Do NOT conjoin existential
answers about theories picked independently. Proof below modifies the argument
of `Pert.Construction.fromBaseline` / `Pert.FirstTarget.firstTarget` to run on
those strengthened receipts. We don't alter imported proofs. Leading data
only; no coupling-power convergence or all-order comparison asserted here.
This can also use the arbitrary intermediate horizons of `Nesting.uniform` on
that one Final.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Cells Spec Next.UVStress
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}
open Pert MergeProof.Acme Orbits


variable {C:Family G}{S:Table C.book}{W:DiffPlan S}
lemma Anchored.narrow {X : Scaling S}(h:Anchored W (path X) (isoPanel X)) (p : Sequence) (w : ℕ → ℝ) (hw : ∀ k,0 < w k) : Anchored W (path (narrow X p w hw)) (isoPanel (narrow X p w hw)):=
    fun d e he x φ hx => (h d e he x φ hx).comp p.cofinal
theorem produce_meter (H : S.Hierarchy) (hW : W.Derivatives S) (ho : W.Orientation H.spin)
    (a : (Bel C.book).Hierarchy) (T : Lighthouse C.book) (hV : T.W.Derivatives (Bel C.book)) (p : T.W.Orientation a.spin)
    (hT : FreeDiv T a p) (X : Scaling S) (hp : Approaches (path X) (isoPanel X)) (ha:Anchored W (path X) (isoPanel X)) (h : Stable H.spin a.spin W T.W X) :
    ∃ J : KernelSpace H.spin,∃ Y : Scaling S,J.val ≠ 0 ∧ currentDiv W H.spin ho J=0 ∧
      Approaches (path Y) (isoPanel Y) ∧ Stable H.spin a.spin W T.W Y ∧ Anchored W (path Y) (isoPanel Y) ∧ Y.meter J.val T.J := by
  have hm := (differential_rank H a ho T p hT hW hV X hp h).2
  haveI : Nontrivial (LinearMap.ker (currentDiv W H.spin ho)) :=
    Module.finrank_pos_iff.mp (hm ▸ zero_lt_one)
  obtain ⟨⟨B,hB⟩,hn⟩ := exists_ne (0 : LinearMap.ker (currentDiv W H.spin ho))
  have hx : B ≠ 0 := fun e => hn (Subtype.ext e)
  have ht : B.val ≠ 0 := fun e => hx (Subtype.ext e)
  obtain ⟨s,R,hr,Hr⟩ := subsector X B.val T.J ht hT.sign
  let Y := narrow X s _ (fun k => positive_strength X (s k) ht hT.sign)
  have hY := narrow_path X s _ (fun k => positive_strength X (s k) ht hT.sign) hp
  have hS := narrow_stable X s _ (fun k => positive_strength X (s k) ht hT.sign) h
  obtain ⟨v,hv,hF⟩ := on_axis Y H hW ho B hB a hV p hY hS R Hr
  let t : KernelSpace a.spin := ⟨T.J,hT.enters⟩
  let j : LinearMap.ker (currentDiv T.W a.spin p) := ⟨t, (linear_cons _ _ p t).2 hT.origin⟩
  have he : j ≠ 0 := fun e => hT.sign (congr_arg (fun (x : LinearMap.ker (currentDiv T.W a.spin p)) => x.val.val) e)
  obtain ⟨c,hc⟩ := (finrank_eq_one_iff_of_nonzero' j he).1 hT.one ⟨v,hF⟩
  have hc : c • T.J = R := (congr_arg (fun (x : LinearMap.ker (currentDiv T.W a.spin p)) => x.val.val) hc).trans hv
  have hz := congr_arg norm hc; rw [norm_smul,hr,Real.norm_eq_abs] at hz
  have hz : |c|=1 := mul_right_cancel₀ (norm_pos_iff.mpr hT.sign).ne' (hz.trans (one_mul _).symm)
  suffices ht : ∃ J : KernelSpace H.spin, J.val ≠ 0 ∧ currentDiv W H.spin ho J = 0 ∧
      Tendsto (balanced_J Y J.val) atTop (𝓝 T.J) by
    obtain ⟨J,hJ,hj,HX⟩ := ht; refine ⟨J,Y,hJ,hj,hY,hS,ha.narrow s _ _,fun i j => ?_⟩
    refine (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp HX i) j).congr fun k => ?_
    apply (Y.U k 4).injective
    change Y.U k 4 (balanced_J Y J k i j) = Y.U k 4 ((Y.U k 4).symm _); rw [LinearEquiv.apply_symm_apply,balanced_value]
  change Tendsto (balanced_J Y B.val) atTop (𝓝 R) at Hr
  rcases le_total 0 c with hh|hh
  · rw [abs_of_nonneg hh] at hz; rw [hz,one_smul] at hc
    exact ⟨B,ht,hB,hc ▸ Hr⟩
  rw [abs_of_nonpos hh] at hz; rw [show c=-1 from neg_eq_iff_eq_neg.mp hz, neg_one_smul] at hc
  refine ⟨-B,neg_ne_zero.mpr ht,by rw [map_neg, show currentDiv _ _ _ B=0 from hB,neg_zero],?_⟩
  refine Tendsto.congr' ?_ (show Tendsto (fun k => -balanced_J Y B k) atTop (𝓝 T.J) from by
    convert Hr.neg using 1
    rw [← hc,neg_neg])
  exact Eventually.of_forall fun k => by change -balanced_J Y _ k = balanced_J Y (-B.val) k; simp [balanced_J,labelScale]

open Next.Extract Dash
variable {G : Gauge} {C : Family G} {F : Extraction.Order} {S : Table C.book} {W : DiffPlan S}
variable {B Z'}{A : Table C.book}
theorem readyM (L:Base C F A B Z' S W) (hG:G.Simple)(hQ:RoughFactory C)(he:Stocked C F) (hC : C.Makes) (h : F.Ordered C S) (hp : F.PointLimits C S) (H : S.Hierarchy)
    (hx : CellHyp C F) (hw : W.Inclusions S) (hv : W.Derivatives S)
    (above : DimAbove S) (T : Lighthouse C.book) (a : (Bel C.book).Hierarchy)
    (u : T.W.Inclusions (Bel C.book)) (v : T.W.Derivatives (Bel C.book)) (p : T.W.Orientation a.spin) (hF : FreeDiv T a p)
    (budget : Aroma C) :
    W.Orientation H.spin ∧ ∃ (I : IR (C:=C) S) (X : Scaling S),
      I.J≠0 ∧ I.J∈KernelSpace H.spin ∧ 
        Approaches (path X) (isoPanel X) ∧ Stable H.spin a.spin W T.W X ∧
          X.meter I.J T.J ∧ Anchored W (path X) (isoPanel X) ∧ Pre H W I.J I.p I.Y ∧ ActLaw W T I.J H.spin a.spin := by
  have hh := Work.D06.answer hC H.smooth H.laws.toSymmetric hp W hv hw H.spin
  obtain ⟨Y,hY,hy,hz⟩ := equivalences L hQ he h hp hG H a hw hh u p above
  obtain ⟨J,X,hn,hJ,hX,hZ,h_,ha⟩ := produce_meter H hv hh a T v p hF Y hY hz hy
  have hc := (linear_cons W H.spin hh J).1 hJ
  have ht := focused H hv a T v X hX hZ _ ha
  obtain ⟨p,A,hA⟩ := shells_law hC hx hp H hv J.val hc budget
  exact ⟨hh,⟨J.val,p,A⟩,X,hn,J.property,hX,hZ,ha,h_,⟨hc,(sym_mem.mp (kernel_mem.mp J.property).1).2.2,hA⟩,ht⟩
lemma constructed (hG : G.Simple) {b : ℝ} (hb : 0<b) :∃ C:Family G,
    C.path.levels.clock.kernel.penalty=b ∧ Extraction.Wcmain C ∧ ∃ M : MaxwellData C,M.T.W = Maxwell.Free.scheme C.labels ∧ M.T.K = Maxwell.Free.gear C.labels ∧
    M.T.J = YM.UVNext.FreeStress.torch C.book.grid 1 ∧ Tensorial M.T.K M.T.J ∧ ∀ f : Extraction.Order,
    ∃ (g:Extraction.Order) (S:Table C.book)(I:IR (C:=C) S)(W:DiffPlan S)
      (X : Scaling S) (c : ℝ) (U : ∀ d, Spin.change S d) (J : S.Stress),
      ∃ l : Supplier (f.refine g) W M I X, Services C (f.refine g) S ∧ Anchored W (path X) (isoPanel X) ∧ Tab S W M I l.uv c U J ∧
      ∃ h : Final C (f.refine g) S, h.sector=⟨W,mill M I c U,J⟩ := by
  obtain ⟨C,hB,hC,hM,hW,hpkg,H,hQ,hF⟩:= YM.PhysicalNext.Repeat.Legato.noel_levy hG hb
  obtain ⟨T',hM0,_⟩:= Maxwell.Free.maxwell_supplies C hG 1 one_ne_zero
  obtain ⟨M, hJ, hM, hK, _, _, ht0, hd⟩ := YM.UVNext.FreeStress.fire hG T' 1 one_ne_zero
  refine ⟨C,hB,hW,M,hM.trans (congr_arg Lighthouse.W hM0),hK.trans (congr_arg Lighthouse.K hM0),hJ,hK.symm ▸ ht0,fun f => ?_⟩
  obtain ⟨g,A,L,R,T,E,hA,s,hN⟩:= hF f
  obtain ⟨hs,hG'⟩:= hQ (f.refine g) s.copies
  have hh := M.hT.smooth
  have hsP : RoughFactory C:=by obtain ⟨a,b,c,h⟩:=hpkg; exact ⟨a,b,c,h.toTableTickets⟩
  obtain ⟨hf,I,X,hI,hX,hY,hZ,hM',hA',hp,ha⟩ := readyM hA hG hsP hG' s.cutoff s.ordered s.generic s.kernel s.copies hA.clean.ready
    hA.clean.tilt (cap_given s.corrected) M.T M.hT M.lit.edges M.lit.pales M.lit.hers hd H
  let p : Supplier (f.refine g) E M I X :=
    ⟨⟨s,hf,hp,ha,hs⟩,hA.clean.ready,hA.clean.tilt,hI,hX,hd,hY,hZ,hM'⟩
  have ht := Bid.station M E I p.uv YM.Outer.miles Work.A01.answer Work.A02.answer Work.A03.answer
    Work.A04.answer Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer
    Work.A09.answer Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer
    Work.A15.answer Work.A16.answer Work.A17.answer
  obtain ⟨c, U, J, b, K, hK'⟩ := ht.picks E M I p.uv p.ider p.deriv
  exact ⟨g,T,I,E,X,c,U,J,p,⟨hs,hG,hpkg,A,L,R,E,hA⟩, hA',b,withFinal hC p.uv c U J b hK'⟩

open Maxwell
set_option maxHeartbeats 900000 in
theorem simultaneous (G:Gauge) (hg : G.Simple) (β : ℝ) (hb : 0<β) : ∃ C : Family G, C.path.levels.clock.kernel.penalty = β ∧
    Extraction.Wcmain C ∧ ∀ f : Extraction.Order,
    ∃ (g : Extraction.Order) (S : Table C.book), Services C (f.refine g) S ∧ ∃ (h : Final C (f.refine g) S) (R:Reader h.sector.derivatives h.sector.turns h.room.kernel.spin) (X : Scaling S),
      FirstExtension h X ∧ Nesting.Uniform h R ∧ Anchored h.sector.derivatives (path X) (isoPanel X) ∧ Foundation h R ∧ Approaches (path X) (isoPanel X) := by
  obtain ⟨C,hc,hW,M,hd,hK,hj,hT,hp⟩ := constructed hg hb
  refine ⟨C,hc,hW,fun f => ?_⟩
  obtain ⟨g,S,I,W,X,c,U,J,p,hs,hd',h,b,eqb⟩ := hp f
  have hm : (M.T.κ)⁻¹ • M.T.J = freeStress C.labels := by
    rw [kappa_eq hg hd hj,inv_neg,inv_one,neg_smul,one_smul,hj,common_stress]
    rfl
  let t:=b.phase.transport
  obtain ⟨R,hR⟩:= Prescription.chosen b.room.kernel.laws.toSymmetric t.injection
  let r:Reader b.sector.derivatives b.sector.turns b.room.kernel.spin := ⟨R,hR,b.room.kernel,t.injection,t.rights,t.spots⟩
  have hf:= Orbits.produce b r hs
  refine ⟨g,S,hs,b,r,X,?_,Nesting.uniform b r hs,eqb.symm ▸ hd',hf,p.limit_⟩
  clear hf
  -- same leading comparison proof
  have he : b.sector.derivatives=W := congrArg Spec.Algebra.derivatives eqb
  refine ⟨?_,fun n j q is a K hK hsep ε he => ?_,?_,fun d => ?_,fun j d => ?_⟩
  · rw [← hd,he]; exact p.fit
  · rw [(congrArg Spec.Algebra.energy eqb : b.sector.energy=J)]
    have hh := mixed_leading p h q is a j hK hsep he
    rw [hm] at hh; exact hh
  · clear r R hR t
    revert he; cases b with | _ _ _ Z α phase B A action realization => cases Z with | _ E K' J' =>
      rintro rfl; exact one_line p
  · rw [he,← hd]; exact for_derivative p d
  rw [eqb,← hK]
  exact rotation_lead p h d j
end YM.OPE.Levy
