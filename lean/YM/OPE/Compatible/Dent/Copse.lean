import YM.OPE.Compatible.Dent.Lure
/-!
# Truncate V before derivative action. On acknowledged boundaries, delta U-vs-anchor from lobe = from full-lobe analytic. Uniform norm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset WilsonStartup
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ C s ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {X Y:Support f}{ι:Type}
namespace Deckery
def honey (A:Deckery R ι)(s:Signed)(k:ℕ)(U:Config G f):ℝ:= ∑' i: Site f ×ι, if A.len i.2<k then A.full i.1 i.2 (pull s 0 U) else 0
end Deckery
namespace Decked
variable {A:Deckery R ι}{w:ι→ℝ}(h:Decked R A σ E C w)(hs:0≤σ)
include h hs
lemma atlasSum (s:Signed)(k:ℕ)(U:Config G f): Summable (fun i:Site f ×ι=> if A.len i.2<k then A.moon s i U else 0) ∧ Summable (fun i:Site f ×ι=> if k ≤ A.len i.2 then A.moon s i U else 0):=by
   have hp:= (h.basin hs (s':=s)).absolute U; constructor
   · exact Summable.of_norm (hp.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=> by split; exact le_rfl; exact norm_zero.trans_le (norm_nonneg _))
   exact Summable.of_norm (hp.of_nonneg_of_le (fun _=> norm_nonneg _) fun i=> by split; exact le_rfl; exact norm_zero.trans_le (norm_nonneg _))
lemma orthoSum (s:Signed)(k:ℕ)(U:Config G f): A.lathe s k U+A.lobe s k U=∑ x:Site f,∑' j, A.moon s (x,j) U:=by
   have hy := (h.basin hs (s':=s)).summable U; have hp := h.atlasSum hs s k U; rw [← tsum_fintype (L:=SummationFilter.unconditional (Site f)), ← hy.tsum_prod, Deckery.lathe, Deckery.lobe, ← hp.2.tsum_add hp.1]; refine tsum_congr fun i=>?_ ; split_ifs <;> first|  omega|simp_all
-- Xsmall.Search any radius B etc
omit hs in
lemma writhes (s:Signed)(i:Site f ×ι){k:ℕ}(hp:C ≤ k)(hv:A.len i.2 ≤ R.p.B) (hs:¬ Disjoint X (A.tower s i)):
   A.tower s i⊆ halo ((k+1)*(4*R.p.B+2)+2*R.p.B) X:=by
    obtain ⟨x,hx,hA⟩:= Finset.not_disjoint_iff.mp hs; intro j hj; refine halo_spec.mpr ⟨x,hx, ((Corona.extent _ R.p.B hA hj).trans ?_)⟩; have hh:coverNumber R.p.B (A.tower s i) ≤ k+1:=by
       unfold Deckery.tower; rw [swath_cover]
       have ht:= h.space i.1 i.2; have he : 0 < (R.p.B:ℝ):=Nat.cast_pos.mpr R.p.B_pos
       exact_mod_cast (show (coverNumber R.p.B (A.home i.1 i.2):ℝ) ≤ ((k+1:ℕ):ℝ) from le_of_mul_le_mul_left (ht.trans (by push_cast; nlinarith only [show (A.len i.2:ℝ) ≤ (R.p.B:ℝ) from Nat.cast_le.mpr hv,mul_le_mul_of_nonneg_left hp he.le])) he)
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hh) _ -- tag eq Z vs ?
variable {J: Seats F} (hh : FoldsGrip F J X)  -- edit
include hh
omit hs in
lemma shiny (s: Signed)(i:Site f ×ι) (hL : Disjoint X (A.tower s i))(U:Config G f): A.moon s i U=A.moon s i (razed J U)∧ A.full i.1 i.2 (pull s 0 U)= A.full i.1 i.2 (pull s 0 (razed J U)):=by
    have he:Agrees (↑(A.tower s i)) U (razed J U) := fun u hu _=> (show razed J U u=U u from if_neg fun h=>Finset.disjoint_left.mp hL (hh.sites _ h (costPose F u).1) hu).symm
    refine ⟨Next.Rank.Thirst.final_swath s 0 _ _ (h.scope i.1 i.2) U (razed J U) he ?_, Next.Rank.Thirst.p_local s 0 _ (h.raw i.1 i.2) U (razed J U) he⟩
    ext j; simp only [mem_inter]; apply and_congr_right; intro hj; apply Iff.symm; apply edits_flags; intro hz; exact Finset.disjoint_left.mp hL (hh.flags (mem_union_left _ hz)) hj
lemma commissioned (s:Signed)(k:ℕ)(l:ℕ)(hp:k≤R.p.B)(hc:C≤l)(ht:halo ((l+1)*(4*R.p.B+2)+2*R.p.B) X ⊆ Y)
 (hx: ∀ U: Config G f,Summable fun j:Site f ×ι=> if A.len j.2<k then A.full j.1 j.2 (pull s 0 U) else 0)
 (U)(hy:Healthy R.p.threshold Y U)(he:Healthy R.p.threshold Y (razed J U)): tweak J (A.lobe s k) U=tweak J (A.honey s k) U:=by
   let V:= razed J U; unfold tweak Deckery.lobe Deckery.honey; rw [← (h.atlasSum hs s k U).1.tsum_sub (h.atlasSum hs s k (razed J U)).1, ← (hx U).tsum_sub (hx _)]
   refine tsum_congr fun i=>?_; split_ifs with hF
   swap; · rfl
   by_cases hh':Disjoint X (A.tower s i)
   · rw [(h.shiny hh s i hh' U).1,(h.shiny hh s i hh' U).2]
     simp
   have hj := (h.writhes s i hc (hF.le.trans hp) hh').trans ht
   exact congr_arg₂ (·-·) (h.matchV _ _ _ ((s_healthy s 0 _ U _).mpr (Disjoint.mono_left hj hy))) (h.matchV _ _ _ ((s_healthy s 0 _ _ _).mpr (Disjoint.mono_left hj he)))
end Decked
end YM.PhysicalNext.Repeat.Aroma
