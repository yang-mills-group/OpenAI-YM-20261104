import YM.GradedFar.StampApproval
/-!
# Histogrammed variant, even preserving the very same joint test.

Uniform length prices; paired tails per those installations. Receding geometry, M.3 authenticated pulse for `m_N`
constant-reference version of actual (uncropped) cutoff moment. Can compare at unrounded points to both S-none and predictions. Packet
cost uses (already shown) continuum comparison, no estimation of m_N derivatives. This
budget is a consequence of earlier results, not requisite for inverse.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Auth
open Function Filter Set PowerSeries Metric
open Extraction Table Spec PhysMS Trace.Pilot OPE OPE.Orbits Lattice FullVolume
open XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale FVA2.Scale.Facets FVA2.Scale.Equator FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar FVA2.O.Enh
open MS MS.Native MS.Land MS.Fleet Neighbor Tariff Tariff.Playbill Tariff.Crosser Tariff.Billboard Tariff.Sunshine Batch
open Fork (Sold Safe)
open scoped Topology BigOperators Classical ContDiff
local instance {n:ℕ} : ContinuousSMul ℝ (Points n):= IsBoundedSMul.continuousSMul
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Final C f S)
   (R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (J P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
   {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true) (ν:ℝ)
    {t:ℝ→ℝ}(Ht:Pose F J Z t)(hF:Prepared F J P Z t)(Hq:LogTrace F R.port)
variable {n m h l p k :ℕ}{K:Set (Points n)}{N:Set (Points m)} {U B a η:ℝ}
local notation "g∴"=> strength G
local notation "Γx"=> Scale.Measure.outlook Z.scheme Z.criterion
local notation "X♯"=> GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "S•"=> moving G U B
local notation "Y₁"=> atLength F P
local notation "D₁"=> atCenter F P h
variable (hU:0<U)(hB:0<B)(hK:IsCompact K)(hx:K⊆conf n)(hN:IsCompact N)(hz:N ⊆ Outside m)
    (hQ:FullVolume.FixedBounds C)(hp:ClusterFrames C)(hC:C.Makes)
variable {d:Fin n→ℕ}{e:Fin m→ℕ}(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)
variable {X E: Type*}[TopologicalSpace X][MeasurableSpace X][OpensMeasurableSpace X] [CompactSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
open MeasureTheory
-- readable scheduler (can use any selections, even more complex estimates at higher powers,
-- not deriving the f-geometry margins of the estimator installations). Uses actual support on same X test
-- all Y & Z(c) etc. preimage-meas avoids requiring global Typeclasses on abstract reporter polls.
-- need continuous x,y when deriving integrability for prediction and packet; still arbitrary signed test on them.
def Readable {X A:Type*}[MeasurableSpace X](f:X→A):Prop:= ∀ i, MeasurableSet {x| f x=i}
lemma readable_pair {X T A:Type*}[MeasurableSpace X] (f:X→T)(g:X→A)(h:Readable f)(he:Readable g): Readable (fun i=>(f i,g i)) := by
 rintro ⟨x,y⟩; simp only [Prod.mk.injEq,setOf_and]; exact (h x).inter (he y)
lemma posted_value {X A:Type*}[MeasurableSpace X][Countable A] {f:X→A}(h:Readable f)(g:A→ℂ): Measurable (fun x=>g (f x)):= by
    intro b hb; let T:= {i:A | g i∈b}; rw [show (fun x=>g (f x)) ⁻¹' b = ⋃ i:↥T, {x | f x=i.val} from ?_]; · exact MeasurableSet.iUnion (fun i=> h i.val)
    ext x; constructor; · intro hx; exact mem_iUnion.mpr ⟨⟨f x,hx⟩,rfl⟩
    intro hx; obtain ⟨i,h⟩:= mem_iUnion.mp hx; exact Eq.mpr (congrArg (fun t=>g t∈b) h) i.property
-- existing Room margin for packet true.
set_option linter.unusedSectionVars false in
lemma packet_coord {r:ℝ}(x:X→Points n)(o:X→E4)(u:AppointedH140Inputs G d)(v: Toon G h)(hx: Continuous x)
    (ho:Continuous o)(hM:∀ i,∀ j≤h, orbitMargin R.port j (sites (o i) r (x i)) (o i)) : Continuous (fun i=> coord v (packet F P R h (o i) r (x i) u)) := by
 let f i:=sites (o i) r (x i); let L:= ((coord v).comp (assign P r _).symm.toLinearMap).toContinuousLinearMap; let M:= labels P r u
 have hL (j:ℕ): (∑ i:R.channels j, fun x:X=> R.coef j i (f x) M (o x) • R.actor j i)=fun i=> R.fresh j (f i) (o i) M:= funext fun x=> by rw [Finset.sum_apply, R.assemble]
 change Continuous (fun i=> L (R.packet _ (f i) M (o i)))
 apply L.continuous.comp; unfold Reader.packet; apply continuous_finsetSum; intro j _
 apply ((F.sector.derivatives.rise (d:=j.val) (e:=h) (Nat.le_of_lt_succ j.isLt)).toContinuousLinearMap).continuous.comp; simp_rw [← congr_fun (hL j.val)]; simp_rw [Finset.sum_apply]
 refine continuous_finsetSum _ (fun i _=> Continuous.smul (f:=fun a:X=> R.coef j.val i (f a) M (o a)) ?_ (continuous_const (y:=R.actor j.val i)))
 exact continuous_iff_continuousAt.mpr fun x'=> (R.coef_smooth j.val i (hM x' j.val (Nat.le_of_lt_succ j.isLt)) M).continuousAt.comp (f:=fun i:X=> (f i,o i)) ((continuous_sites x o ho hx r).prodMk ho).continuousAt
-- coord version of prediction. essential to read exact X through pulseRow before pairing.
include H ν in
set_option linter.unusedSectionVars false in
lemma fore_coord {r:ℝ}{x:X→Points n}(u:AppointedH140Inputs G d)(v: Toon G h)(hx:Continuous x)(hv:∀ i,x i∈conf n): Continuous (fun i=> coord v (croppedVector Γx h p u (x i) r)):= by
 have he(i:ℕ)(q:Scan G n)(v:Q G): Continuous (fun j=> coeff i (O.Canon.FarCoefficients Γx q (x j) v)):= by
    apply continuous_iff_continuousAt.mpr; intro j; exact ((((H.separatedOPE ν).wilson.far q).2.1 _ i).continuousAt ((conf_open _).mem_nhds (hv j))).comp hx.continuousAt
 simp_rw [croppedVector, map_sum,map_smul,crop_eq,ope,map_sum,coeff_C_mul]; fun_prop
set_option linter.unusedSectionVars false in
lemma discrete_pairs (p:X→Positions m)(x:X→Site (C.side n k))(hp:Readable p)(hx: Readable x)(v:AppointedH140Inputs G e)(u:X→ Sec G h)(hu:∀ i: Toon G h,Continuous (fun x=> coord i (u x))) (r s:ℝ):
    Measurable (fun i=> pulseRow F P h r s (x i) (p i) v (u i)):= by
 have Hp(i:X): u i=∑ j:Toon G h, coord j (u i) • theory j:=by
    exact (all_sig _).symm
 have Hcap(i:X):pulseRow F P h r s (x i) (p i) v (u i)=∑ j:Toon G h, coord j (u i) • pulseRow F P h r s (x i) (p i) v (theory j):=by
    nth_rw 1 [Hp i]; rw [map_sum]; exact Finset.sum_congr rfl fun _ _=> map_smul ..
 simp_rw [Hcap]; refine Finset.measurable_sum _ (fun i _=> (hu i).measurable.smul ?_)
 exact posted_value (readable_pair p x hp hx) (fun j => pulseRow F P _ r s j.2 j.1 v (theory i))
open Budget
-- approximation lemmas
set_option linter.unusedSectionVars false in
lemma closePrice {f g:X→ℂ} (μ:VectorMeasure X E) [IsFiniteMeasure μ.variation] (B:ℂ→L[ℝ] E→L[ℝ] ℂ) {d:ℝ}
    (hp:∀ i,‖f i-g i‖≤d)(hf: Measurable f)(hG:Measurable g)(he:μ.Integrable g): Attends μ B d f g:=by
    have hm:μ.Integrable (fun x=> f x-g x):= (integrable_const d).mono' ((hf.sub hG).aestronglyMeasurable) (Eventually.of_forall hp)
    have h:μ.Integrable f:= (hm.add he).congr (Eventually.of_forall fun x=> by rw [Pi.add_apply,sub_add_cancel])
    refine ⟨h,he,?_⟩; rw [← VectorMeasure.integral_sub h he]; exact VectorMeasure.norm_integral_le_of_norm_le_const (Eventually.of_forall hp)
end YM.Integration.GradedFar.Auth
