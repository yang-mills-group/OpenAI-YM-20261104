import YM.OPE.Compatible.Minuet.Talc
/-! # Local lenses. Payload extends globally by canonical folding. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Aroma
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03 Work.F03
open Bloch Laurent Progress.DirectedRecipe Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat Matter
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Gas Ursell Trees Animals Corona Daisy Leaf
open Planned.GuardedAtom.Guard
open AnalyticBridge.VerifiedReset
open Next.Rank.Thirst
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {R : Rep G f}
    {p : BudgetPoint} {m n: ℕ} {W a r t σ E Λ μ x κ C w ε D b: ℝ} {Ñ:ChartRatio G}
    (F:Forest S.ratio) (I J : Seats F)
-- O all tested, I edited. Paying Halo of I inside Test. masks.
structure Primacy (F: Forest S.ratio)(I O: Seats F)(Y X Z:Support f)(q:Support c)(B n:ℕ):Prop where
  nested:I ⊆ O
  small: FoldsGrip F I Z
  supports : halo (ySpan B) Z⊆Y
  broad:FoldsGrip F O X
  flagged : ∀ i:F.Free, i.val.1 ∈ RG.inspected Y→i∈O
  modest : ∀ i:F.Free, S.ratio.parent i.val.1 ∈ halo (max n (predReach S.patch+1)) q → i∈ O
  apart : ∀ i∈I,S.ratio.parent (i:F.Free).val.1∉halo (predReach S.patch+1) (qᶜ)
-- any forest. Curtain saturated by borrowers.
abbrev World (F:Forest S.ratio)(J:Seats F) (G:Gauge) := J → G.El
def curveF (J:Seats F)(W: F.Slice G):World F J G :=fun i=> W i.val
def chant (J:Seats F)(W:Config G f):World F J G:=fun i=>pantone F W i.val.val
lemma chant_m : Measurable (chant F J (G:=G)):= by unfold chant pantone Lattice.gauge; fun_prop
lemma chant_eq (u: F.Slice G): chant F J (F.drape u)=curveF F J u:=by funext i; unfold chant curveF; rw [pantone_self,F.off_tree]
variable {F I J} {X Y Z : Support f}
lemma stroll (u v: F.Slice G) (hz:curveF F J u=curveF F J v) (W:Support f)(hp:∀ i:F.Free, i.val.1∈ W → i∈J) : Agrees (↑W) (F.drape u) (F.drape v):=by
   intro i hi _; by_cases h : i∈F.trunks
   · rw [F.on_tree u ⟨i,h⟩,F.on_tree v ⟨i,h⟩]
   let j:F.Free:=⟨i,h⟩; exact (F.off_tree _ j).trans ((congr_fun hz ⟨j,hp _ hi⟩).trans (F.off_tree _ j).symm)
lemma crease (h:FoldsGrip F J X) {f:World F J G→ℝ} (hv:Measurable f)(hh:∀ i, ‖f i‖≤κ) : Paced R X S (f∘chant F J) κ:=⟨fun U V hV _=> congr_arg f (show chant F J U=chant F J V from funext (fun i=> poses F _ U V (agrees_mono hV (by exact_mod_cast (h.sites _ (show (i.val:F.Free).val ∈chairMap F J from Finset.mem_image_of_mem _ i.property)))))), hv.comp (chant_m F J),fun k hp U=>congr_arg f (show chant F J (gauge k U)=_ from funext (fun j=>congr_fun (pantone_in F k hp U) j.val.val)),fun _=>hh _⟩
-- W editing U links, certificate all saturated. mask probability.
def shave (I:Seats F)(u:F.Slice G):F.Slice G:= fun i=> if i∈I then 1 else u i
def capstone (I:Seats F)(u:F.Slice G):F.Slice G:= fun i=> if i∈I then u i else 1
lemma draped (u:F.Slice G): razed I (F.drape u)=F.drape (shave I u):=by
   have hf : F.foldAt (F.drape u)=F.foldAt (1:Config G f):= F.names (F.drape u) _ fun j hj=> F.on_tree u ⟨j,hj⟩; have hg (x):F.foldAt (1:Config G f) x=1:=by
       unfold Forest.foldAt; suffices hv : travel (1:Config G f) x (F.hike x)=1 from by rw [hv];simp
       have h (p:Site f)(t:Walk): travel (1:Config G f) p t=1:= by induction t generalizing p; rfl; next i t ih=> rw [travel,ih,mul_one]; unfold Step.read; split <;> simp
       exact h ..
   ext1 i; unfold razed; rw [hf]; split
   next hv=> obtain ⟨p,hj,rfl⟩:= mem_image.mp hv; rw [hg,hg,F.off_tree]; simp [shave,hj]
   next hb=>
     by_cases hi:i∈F.trunks
     · exact (F.on_tree u ⟨i,hi⟩).trans (F.on_tree _ ⟨i,hi⟩).symm
     let p:F.Free:=⟨i,hi⟩; have h:p∉I:=fun h=> hb (mem_image_of_mem _ h)
     change F.drape u p.val = F.drape (shave I u) p.val; rw [F.off_tree,F.off_tree,shave,if_neg h]
lemma sameShown (u v:F.Slice G)(he:curveF F J u=curveF F J v): curveF F J (shave I u)=curveF F J (shave I v):=by funext i;change (if _ then _ else _)=(if _ then _ else _);split; rfl; exact congr_fun he i
namespace Primacy
variable {q:Support c} (h:Primacy F I J Y X Z q R.p.B n)
include h
lemma travels (U:Config G f) (i: Bond f) (hh:S.ratio.parent i.1∈ halo (predReach S.patch+1) (qᶜ)):razed I U i=U i:=by
   refine if_neg fun he=>?_ ; obtain ⟨j,hj,hJ⟩:=mem_image.mp he; subst i; exact h.apart _ hj hh
lemma m_loop (u v:F.Slice G)(he:curveF F J u=curveF F J v)(i:Bond c)(hi:i.1∈q) : AgreeNear S.ratio.parent i.1 (predReach S.patch+1) (F.drape u) (F.drape v):=by
   intro j hj; by_cases ht:j∈F.trunks
   · exact (F.on_tree u ⟨j,ht⟩).trans (F.on_tree _ ⟨j,ht⟩).symm
   let a:F.Free:=⟨j,ht⟩; exact (F.off_tree _ a).trans ((congr_fun he ⟨a,h.modest _ (halo_spec.mpr ⟨i.1,hi,hj.trans (le_max_right ..)⟩)⟩).trans (F.off_tree _ a).symm)
lemma m_angle (H:S.patch.Branches S.kernel G)(u v:F.Slice G)(he:curveF F J u=curveF F J v)(k:S.Choices)(W:Config G c): tweak I (fun U=>R.beta*noiseTaylor S W U k) (F.drape u) = tweak I (fun U=>R.beta*noiseTaylor S W U k) (F.drape v):=by
   unfold tweak noiseTaylor; simp only; simp_rw [← mul_assoc,← mul_sub,← Finset.sum_sub_distrib]; apply congr_arg; refine Finset.sum_congr rfl fun i _=> ?_
   by_cases hi:i.1∈q
   · rw [(Emblems.choices _ _ i k k H rfl rfl rfl (h.m_loop u v he i hi)).2.2, draped, draped,(Emblems.choices _ _ i k k H rfl rfl rfl (h.m_loop _ _ (sameShown u v he) i hi)).2.2]
   have hv(v:F.Slice G) : S.prediction _ k i = S.prediction (razed I (F.drape v)) k i:=(Emblems.choices (F.drape v) _ i k k H rfl rfl rfl (farGlow (h.travels _) i.1 hi)).2.2
   rw [hv u,hv v]; abel
end Primacy
end YM.PhysicalNext.Repeat.Aroma
