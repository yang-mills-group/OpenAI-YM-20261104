import YM.OPE.Compatible.Minuet.Stage
/-!
 # Allgood needs at minimal Foot only. Actual cinematic kernel relative.
-/
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
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ C w ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {J:Seats F}{X Y Z:Support f}
abbrev ySpan (B : ℕ) := ((100+1)*(4*B+2)+2*B)
def Ruin (R:Rep G f)(W:Config G c)(m:ℕ)(J:Seats F)(k:S.Choices) :=fun U=> Real.exp (-tweak J (tasteU R m) U)*Real.exp (-tweak J (fun U=> R.beta*noiseTaylor S W U k) U)
lemma moved_mild (h:R.Lawful σ C Λ E w)(hh':FoldsGrip F J X)(hg:FoldsGrip F J Z)(U:Config G f)(hc:Healthy R.p.threshold Z U)(hk:Healthy R.p.threshold Z (razed J U)): mild R X U=mild R X (razed J U):=by
   have hp : RG.flags R.p.threshold U=RG.flags R.p.threshold (razed J U):=by
     ext x; by_cases h:x∈ Z
     · exact iff_of_false (Finset.disjoint_left.mp hc h) (Finset.disjoint_left.mp hk h)
     exact (edits_flags U x (fun he=> h (hg.flags (mem_union_left _ he))) _).symm
   unfold mild; refine tsum_congr fun i=>?_ ; split_ifs; next=>rfl
   next hm=>
     unfold Activities.gasOccurrence Activities.admissible; rw [hp]; split_ifs
     swap; · rfl
     refine Finset.prod_congr rfl fun j hj=> h.labels.forced.reads _ _ _ (fun v hv _=> ?_) (by rw [hp])
     exact Eq.symm (show razed J U v = U v from if_neg fun hz=> hm ⟨j,mem_filter.mpr ⟨hj, Finset.not_disjoint_iff.mpr ⟨_,hv,hh'.sites _ hz (costPose F v).1⟩⟩⟩)
lemma tallyW (H:S.patch.Branches S.kernel G) (h:R.Lawful σ C Λ E w)(hc:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)
 (hX:FoldsGrip F J X)(hg:FoldsGrip F J Z)(ht:halo (ySpan R.p.B) Z⊆Y)(hk:m ≤ R.p.B)(W:Config G c)(U)(hH: Healthy R.p.threshold Y U)(hx:Healthy R.p.threshold Y (razed J U))(q:Support c)
    (hr:∀ i,S.ratio.parent i.1∈halo (predReach S.patch+1) (qᶜ)→ (razed J U) i=U i)
 (ha:ordFrame S (halo 1 q) U) (hb:ordFrame S (halo 1 q) (razed J U)) (hp:ordBest S q U)(hd:ordBest S q (razed J U))(k:S.Choices):
    S.density R.beta U W*mellow R X U*Real.exp (cinnamon R m J U)=S.density R.beta (razed J U) W*mellow R X (razed J U)*Ruin R W m J k U:=by
       have he : mellow R X U*Real.exp (cinnamon R m J U)=mellow R X (razed J U)*Real.exp (-tweak J (tasteU R m) U):=by
         let V:= razed J U; have hw:= expr h hc hy hg ht hk U hH hx; rw [milk h,milk h, moved_mild h hX hg U (Disjoint.mono_left ((halo_subset _ _).trans ht) hH) (Disjoint.mono_left ((halo_subset _ _).trans ht) hx), mul_right_comm (Real.exp (R.exponent U)),mul_right_comm (Real.exp (R.exponent (razed J U)))]
         rw [← Real.exp_add, ← Real.exp_add, ← hw]; unfold tweak; apply congr_arg (· * mild R X V); apply congr_arg Real.exp; ring
       have hK:= contour H W hr ha hb hp hd R.beta k; rw [mul_assoc,he,hK,Ruin]; ring
-- Ruin independent outside marked Y. No summability at exact Q.B.R slack? Grow.
namespace Decked
variable {ι:Type}{A:Deckery R ι}{w:ι→ℝ} (h:Decked R A σ E C w)
include h
lemma lakes (s : Signed)(k l:ℕ)(ha:0≤σ)(ht:C ≤ l)(hm:halo ((l+1)*(4*R.p.B+2)+2*R.p.B) Z⊆Y)(hp:FoldsGrip F J Z)(hB:k≤R.p.B)(U V:Config G f)
 (hx:Agrees (↑Y) U V)(hH:Healthy R.p.threshold Y U)(hh:Healthy R.p.threshold Y V) (hj:Healthy R.p.threshold Y (razed J U))(hf:Healthy R.p.threshold Y (razed J V)): tweak J (A.lobe s k) U=tweak J (A.lobe s k) V:=by
    have hb(U:Config G f):=(h.atlasSum ha s k U).1; have hZ:= (halo_subset _ _).trans hm
    unfold tweak Deckery.lobe; rw [← (hb U).tsum_sub (hb (razed J U)),← (hb V).tsum_sub (hb (razed J V))]; refine tsum_congr fun i=>?_ ; split_ifs with hF
    swap; · rfl
    by_cases H: Disjoint Z (A.tower s i)
    · rw [(h.shiny hp s i H U).1,(h.shiny hp s i H V).1]; simp
    have hs : A.tower s i ⊆ Y:= (h.writhes s i ht (hF.le.trans hB) H).trans hm
    have he (U V:Config G f)(hx:Agrees (↑Y) U V)(hH:Healthy R.p.threshold Y U)(hh:Healthy R.p.threshold Y V) : A.moon s i U=A.moon s i V:=by
       refine Next.Rank.Thirst.final_swath s 0 _ _ (h.scope i.1 i.2) U V (agrees_mono hx (by exact_mod_cast hs)) ?_; rw [disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hs hH),disjoint_iff_inter_eq_empty.mp (Disjoint.mono_left hs hh)]
    have ht : Agrees (↑Y) (razed J U) (razed J V):=by
       have hf:Z ∪ Y=Y:= Finset.union_eq_right.mpr hZ
       have hh:= edits_agrees (Y:=Y) hp _ _ (hf.symm ▸ hx);rw [hf] at hh; exact hh
    rw [he _ _ hx hH hh, he _ _ ht hj hf]
end Decked
lemma spatial (h:R.Lawful σ C Λ E w)(hc:WilsonStartup.Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)
 (hg:FoldsGrip F J Z)(ht:halo (ySpan R.p.B) Z⊆Y)(hk:m ≤ R.p.B)(U V:Config G f)(hw:Agrees (↑Y) U V)(hH: Healthy R.p.threshold Y U)(hx:Healthy R.p.threshold Y (razed J U))(hJ:Healthy R.p.threshold Y V)(hv:Healthy R.p.threshold Y (razed J V)):
 tweak J (tasteU R m) U=tweak J (tasteU R m) V:=by
   have hf(s:Signed): tweak J (copeV R s m) U=tweak J (copeV R s m) V:=by
      rw [← whiteness h hc hy s hg ht hk U hH hx, ← whiteness h hc hy s hg ht hk V hJ hv]
      obtain ⟨_,hF⟩:= acidic hc h hy
      have he₁:= hF.lakes s m 100 (by linarith [h.paths.width]) (by norm_num [Geo.lowCount]) ht hg hk U V hw hH hJ hx hv
      have he₂ (d:ℕ)(hd:d≤4)(Z:ℕ→ Atom G d)(C:ℝ)(hp:SumBudget (fun i=>(Z i).budget σ) C)(hh':∀ i,(Z i).Invariant): tweak J ((emberY R Z).lobe s m) U=tweak J ((emberY R Z).lobe s m) V:=by
       obtain ⟨_,hS⟩:=soundsE (R:=R) Z hh' hp; have hb :(1:ℝ)+d*2 ≤ ((100:ℕ):ℝ):=by exact_mod_cast (show 1+d*2 ≤ 100 by omega)
       exact hS.lakes s m 100 h.paths.width.le hb ht hg hk U V hw hH hJ hx hv
      unfold brim groupsV; simp_rw [tweaktribes,tweakYaw]; simp_rw [tweaktribes,Pi.add_apply,Pi.smul_apply]; simp only [Pi.add_apply]; rw [he₁,he₂ 3 (by norm_num) _ _ h.paths.three (fun i=>(h.paths.invariant i).2.1),he₂ 4 (by norm_num) _ _ h.paths.four (fun i=>(h.paths.invariant i).2.2),he₂ 2 (by norm_num) _ _ h.paths.two (fun i=>(h.paths.invariant i).1)]
   unfold tweak tasteU; rw [← mul_sub,← mul_sub, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]; exact congr_arg (AnalyticBridge.VerifiedReset.factor *·) (sum_congr rfl fun i _=>hf i)
end YM.PhysicalNext.Repeat.Aroma
