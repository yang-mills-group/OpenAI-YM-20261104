import YM.Push.LOCAL_SPLITTING.Direct
import YM.Push.LOCAL_SPLITTING.Atoms
import YM.OPE.Compatible.Harms.Lien
/-!
# Activation along chase
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard AnalyticBridge.VerifiedReset Geo
open Next.Rank.Thirst YM.OPE
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open Push.Local Source
variable {G :Gauge}{X:Type}{L n c:Side}{k m:ℕ}{T S:StepData c n} {R:Rep G n}{β v w σ Λ K ξ0 a:ℝ}{b: ℕ→ℝ}
-- direct marker at any smooth
variable (p:ℂ→L[ℝ]ℝ) (g:Config G c)
variable {α γ t s : ℝ}{C:Labels.Frame G k}(V:SectionData C){o:Site n}{A:Hol G} {Y:Coefficient C n}
variable {F: Forest S.ratio}{Q Z:Support n}{I J:Seats F}{P:BudgetPoint}{f:Config G n→ℂ}
variable (x:ℝ)
section
variable (F)
noncomputable def poseC (I: Seats F)(w:World F I G): F.Slice G:= fun i=> if h:i∈I then w ⟨i,h⟩ else 1
lemma PoseM (I:Seats F) :Continuous (poseC (G:=G) F I):=by
       apply continuous_pi; intro i; unfold poseC; split_ifs with h; exact continuous_apply _; exact continuous_const
variable {F}
lemma tugs {F:Forest S.ratio}(I:Seats F) (x:World F I G):curveF F I (poseC F I x)=x:=by funext i; exact dif_pos i.property
lemma selfTone (x: Config G n): pantone F x= F.drape (fun i=> pantone F x i.val):=by funext i; by_cases h:i∈ F.trunks; exact (F.compress x i h).trans (F.on_tree _ ⟨i,h⟩).symm; exact (F.off_tree (fun i=>pantone F x i.val) ⟨i,h⟩).symm
def pledgesF (Y:Support n)(I:Seats F):Prop:= ∀ i:F.Free,i.val.1∈ RG.inspected Y → i∈ I
abbrev cashX (B:BudgetPoint)(Q:Support n)(p:ℂ→L[ℝ]ℝ)(f:Config G n→ℂ) :Config G n→ℝ:= p ∘ masked B.threshold Q f
noncomputable def powerA (I:Seats F) (B:BudgetPoint)(Q:Support n)(p:ℂ→L[ℝ]ℝ)(f:Config G n→ℂ) (W:World F I G):= cashX B Q p f (F.drape (poseC F I W))
variable (hp:P.Regular Q f)(hv:P.supBounds o Q f x)
include hp
lemma crownX (U:Config G n) (hw: pledgesF Q I):cashX P Q p f U=powerA I P Q p f (chant F I U):=by
       let z:= masked P.threshold Q f; change p (z U)=p (z _); apply congr_arg; unfold z; conv_lhs => rw [← Push.Local.Kernel.mask_gauge _ _ hp.symmetry (F.foldAt U) U]
       rw [show gauge (F.foldAt U) U=pantone F U from rfl,selfTone]; exact UsesFinal.allReads _ _ _ (uses_mask _ hp.sites) _ _ (stroll _ _ (by rw [tugs];rfl) _ hw)
include hv
omit hp in
lemma sightW (U:Config G n):‖cashX P Q p f U‖≤ ‖p‖*x:=by
       apply (p.le_opNorm _).trans; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); by_cases he:Healthy P.threshold Q U
       · rw [masked_eq _ _ _ _ he]; exact hv.2 U he [] (Nat.zero_le _) (by simp)
       rw [masked_ne _ _ _ _ he,norm_zero]; exact hv.1
lemma wrapX : Envelope (powerA (F:=F) I P Q p f):=by
       exact ⟨p.continuous.measurable.comp ((masked_measurable _ _ _ hp.borel).comp (F.continuous_drape.comp (PoseM _ _) |>.measurable)),_,fun w=> sightW p x hv _⟩
omit hp hv
lemma filmC {r B : ℝ}(ht:0≤r)(hu:4*r≤B) (hf: pledgesF Q I)(U:Config G n)(hx:¬ Healthy B Q U) : 1 ≤ slipF F I r U:=by
       let f i := film F i U r; let v(i:F.Free):=pantone F U i.val
       suffices h:∃ i∈I,r<G.chord (pantone F U i.val) by
           obtain ⟨i,hi,h⟩:=h; exact (show (1:ℝ)=f i from (if_pos h).symm).trans_le (Finset.single_le_sum (s:=I) (fun j _=>show 0 ≤film F j U r from by unfold film;split <;> norm_num) hi)
       have he:¬ Healthy B Q (F.drape v):=by
           rw[show F.drape v=_ from (selfTone U (F:=F)).symm]; unfold pantone Healthy; rwa [gauge_flags]
       by_contra! h; apply he; refine Finset.disjoint_left.mpr fun i hi hj=>?_
       obtain ⟨p,hp,hb⟩:= (RG.flags_spec ..).1 hj
       exact not_le.mpr hb ((shutterCh p (F.drape v) r (fun u hw _=>by
            by_cases hk:u∈ F.trunks; · rw[F.on_tree v ⟨u,hk⟩,G.chord_one]; exact ht
            let j:F.Free:=⟨u,hk⟩; rw [show F.drape v u= v j from F.off_tree _ j]; refine h _ (hf j (Finset.mem_union_right _ (mem_biUnion.mpr ⟨p,mem_univ _,?_⟩))); rw [if_neg]; exact hw; exact Finset.not_disjoint_iff.mpr ⟨i,hi,hp⟩)).trans hu)
end
end YM.PhysicalNext.Repeat.Aroma
