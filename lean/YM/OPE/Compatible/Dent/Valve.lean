import YM.OPE.Compatible.Dent.Glow
/-!
 # V archive and mellow formula mastered.
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
    {p : BudgetPoint} {m d M: ℕ} {W a r t σ E Λ μ x κ C w ε D: ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {J:Seats F}{X Y:Support f}
open Geo
variable (h:R.Lawful σ C Λ E w)(hc:Decent R.clip R.p)(hy:Geo.Width R.p R.clip σ)
include h hc hy
lemma shelves (hh':FoldsGrip F J X)(ha:t+ε ≤ R.p.supportExponent)(hε:0<ε)(hp:0≤t)(hs:2*R.p.supportExponent ≤ R.p.B*(3*σ/4)) (m:ℕ):
     Sable R S X t (cinnamon R m J) (marksV R X σ ε C Λ m + 2*(X.card*(est R.p ε*E))):=by
   let v:= marksV R X σ ε C Λ m; let g s:= tweak J (smoke R s m); let f (b:Finset Signed):= ∑ s∈b,g s
   have hf A: Sable R S X t (f A) (A.card*v):=by
      induction A using Finset.induction_on with
      | empty=>
          unfold f; rw [sum_empty,card_empty,Nat.cast_zero,zero_mul]; exact Sable.solitary ⟨fun _ _ _ _=>rfl,measurable_const,fun _ _ _=> rfl,fun _=>norm_zero.le⟩
      | insert s b hh ih=> unfold f; rw [card_insert_of_notMem hh,sum_insert hh,Nat.cast_add, Nat.cast_one,add_mul,one_mul,add_comm]; exact ih.addition (nutrient J h hc hy hh' ha hε hp hs m s) hp
   have hy:= (hf univ).scale AnalyticBridge.VerifiedReset.factor; rw [Real.norm_of_nonneg factor_pos.le,card_univ,←mul_assoc,factor_card,one_mul] at hy
   rw [show cinnamon R m J = AnalyticBridge.VerifiedReset.factor • f univ +tweak J (R.activities.additive R.p) from funext (fun i=> by simp only [Pi.add_apply,Pi.smul_apply,f,g,Finset.sum_apply]; rfl)] -- edit
   exact hy.addition (childhood hh' h hε ha) hp
omit hc hy
local notation "p_"=> R.p
def mild (R:Rep G f)(X:Support f) (U:Config G f) := ∑' i, if (towY R.activities X i).Nonempty then 0 else R.activities.gasOccurrence R.p i U
lemma milk (U:Config G f) (X:Support f) : mellow R X U= Real.exp (R.exponent U)*mild R X U:=by
   let g(i):= stained R X (fun _=>1) i U
   have hv : Summable g:= ((sheer h (fun _=>1) (Envelope.const _) X).2).summable U
   have hs := ((Activities.gasSeries h.labels).summable U).mul_left (Real.exp (R.exponent U))
   unfold mellow Rep.eval Activities.gas smudge mild; rw [← tsum_mul_left,← tsum_mul_left,← hs.tsum_sub hv]
   refine tsum_congr fun i=>?_; unfold g stained; split_ifs <;> simp
lemma mollified (hh':FoldsGrip F J X) (U:Config G f)(hk: Healthy (p_).threshold X U)(he:Healthy (p_).threshold X (razed J U)): mild R X U=mild R X (razed J U):=by
   have hp : RG.flags R.p.threshold U=RG.flags R.p.threshold (razed J U):=by
     ext x; by_cases h:x∈ X
     · exact iff_of_false (Finset.disjoint_left.mp hk h) (Finset.disjoint_left.mp he h)
     exact (edits_flags U x (fun he=> h (hh'.flags (mem_union_left _ he))) _).symm
   unfold mild; refine tsum_congr fun i=>?_ ; split_ifs; next=>rfl
   next hm=>
     unfold Activities.gasOccurrence Activities.admissible; rw [hp]; split_ifs
     swap; · rfl
     refine Finset.prod_congr rfl fun j hj=> h.labels.forced.reads _ _ _ (fun v hv _=> ?_) (by rw [hp])
     exact Eq.symm (show razed J U v = U v from if_neg fun hz=> hm ⟨j,mem_filter.mpr ⟨hj, Finset.not_disjoint_iff.mpr ⟨_,hv,hh'.sites _ hz (costPose F v).1⟩⟩⟩)
include hc hy
lemma dial (hh':FoldsGrip F J X) {P:Support f}(hg: FoldsGrip F J P)
  (ht:halo ((100+1)*(4*R.p.B+2)+2*R.p.B) P⊆Y)(hk:m ≤ R.p.B)(U)(hH: Healthy R.p.threshold X U)(hx:Healthy R.p.threshold X (razed J U))(hG:Healthy R.p.threshold Y U)(he:Healthy R.p.threshold Y (razed J U)):
    mellow R X U*Real.exp (cinnamon R m J U)=mellow R X (razed J U)*Real.exp (-tweak J (tasteU R m) U):=by
       let V:= razed J U; have hw:= expr h hc hy hg ht hk U hG he; rw [milk h,milk h, mollified h hh' U hH hx, mul_right_comm (Real.exp (R.exponent U)),mul_right_comm (Real.exp (R.exponent (razed J U)))]
       rw [← Real.exp_add, ← Real.exp_add, ← hw]; unfold tweak; apply congr_arg (· * mild R X V); apply congr_arg Real.exp; ring
end YM.PhysicalNext.Repeat.Aroma
