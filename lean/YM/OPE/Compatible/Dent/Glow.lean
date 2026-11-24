import YM.OPE.Compatible.Dent.Tween
/-!
# Emollient rescreening. True 
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
include hc h hy
lemma whiteness (s:Signed)(hh: FoldsGrip F J X) (ht:halo ((100+1)*(4*R.p.B+2)+2*R.p.B) X ⊆ Y) (hk:m ≤ R.p.B)(U)(hg:Healthy R.p.threshold Y U)(he:Healthy R.p.threshold Y (razed J U)): tweak J (brim R s m) U=tweak J (copeV R s m) U:=by
   obtain ⟨_,hF⟩:= acidic hc h hy
   have hv {ι:Type} (f':Site f ×ι→ℝ)(hx:∀ x:Site f,Summable fun i=> f' (x,i)):Summable f':= .of_norm ((summable_prod_of_nonneg fun i=> norm_nonneg _).2 ⟨fun i=>(hx i).norm,.of_finite⟩)
   have hz:=hF.commissioned (by linarith [h.paths.width]) hh s m 100 hk (by norm_num [lowCount]) ht (fun V=> hv _ (fun x=> by
      let q:Low→ℝ:=fun i=> (acid R).full x i (pull s 0 V); have hx:Summable q:= Low.plain_sum h.paths x _; apply Summable.of_norm (hx.norm.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=> ?_)); split; rfl; exact norm_zero.trans_le (norm_nonneg _))) _ hg he
   have ht' (d:ℕ)(hd:d≤4)(Z:ℕ→ Atom G d)(C:ℝ)(hp:SumBudget (fun i=>(Z i).budget σ) C)(hh':∀ i,(Z i).Invariant):let Q:= emberY R Z; tweak J (Q.lobe s m) U=tweak J (Q.honey s m) U:=by
       intro Q; obtain ⟨_,hS⟩:=soundsE (R:=R) Z hh' hp; have hb :(1:ℝ)+d*2 ≤ ((100:ℕ):ℝ):=by exact_mod_cast (show 1+d*2 ≤ 100 by omega)
       apply hS.commissioned h.paths.width.le hh s m 100 hk hb ht ?_ _ hg he
       intro W; apply hv; intro x
       refine Summable.of_norm ((hp.2.1.mul_right (2^d)).of_nonneg_of_le (fun i=>norm_nonneg _) fun i=>?_); split
       · exact le_trans (Atom.unmasked_bound ..) (mul_le_mul_of_nonneg_right ((Z i).lower_budget _ h.paths.width) (pow_nonneg (show 0 ≤ (2:ℝ) by norm_num) d))
       rw [norm_zero]; exact mul_nonneg (hp.1 _) (pow_nonneg (show 0 ≤ (2:ℝ) by norm_num) d)
   unfold brim copeV groupsV; simp_rw [tweaktribes,tweakYaw]; simp_rw [tweaktribes,Pi.add_apply,Pi.smul_apply]; simp only [Pi.add_apply]; rw [hz, ht' 2 (by norm_num) _ _ h.paths.two (fun i=>(h.paths.invariant _).1),ht' 3 (by norm_num) _ _ h.paths.three (fun i=>(h.paths.invariant _).2.1),ht' 4 (by norm_num) _ _ h.paths.four (fun i=>(h.paths.invariant _).2.2)]
-- positive Δ exactly: compare True expansion cancellation in anchor reweight.
def tasteU (R:Rep G f) (m:ℕ)(U:Config G f):= AnalyticBridge.VerifiedReset.factor*∑ s, copeV R s m U
def cinnamon (R:Rep G f)(m:ℕ) (J:Seats F)(U:Config G f):= AnalyticBridge.VerifiedReset.factor*∑ s,tweak J (smoke R s m) U + tweak J (R.activities.additive R.p) U
lemma expr (hh':FoldsGrip F J X)(ht:halo ((100+1)*(4*R.p.B+2)+2*R.p.B) X⊆Y)(hk:m ≤ R.p.B)(U)(hg:Healthy R.p.threshold Y U)(he:Healthy R.p.threshold Y (razed J U)): tweak J R.exponent U+cinnamon R m J U = -tweak J (tasteU R m) U:=by
   let V:= razed J U; let f1(U:Config G f):= ∑ s:Signed, R.path.principal R.clip R.p R.beta (pull s 0 U); let g(U : Config G f):=∑ s,copeV R s m U
   have he':(∑ s,tweak J (smoke R s m) U)= (f1 U-f1 V)-(g U-g V):=by
      unfold f1 g; rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _=> ?_; have hp := reunited h hc hy i m U; have hx':=reunited h hc hy i m V; have hv := whiteness h hc hy i hh' ht hk U hg he
      change brim R i m U-brim R i m V=_-_ at hv; unfold tweak; unfold V at *; linarith
   unfold cinnamon; rw [he']; change (R.exponent U-R.exponent V)+(AnalyticBridge.VerifiedReset.factor*(_-_)+(_-_))= -(AnalyticBridge.VerifiedReset.factor*g U-AnalyticBridge.VerifiedReset.factor*g V)
   unfold Rep.exponent; change (_-AnalyticBridge.VerifiedReset.factor*f1 U-_-(_-AnalyticBridge.VerifiedReset.factor*f1 V-_)) + _ = _; unfold f1 g V; ring
end YM.PhysicalNext.Repeat.Aroma
