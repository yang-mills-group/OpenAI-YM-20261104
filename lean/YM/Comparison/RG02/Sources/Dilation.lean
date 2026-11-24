import YM.Comparison.RG02.Sources.Naming
/-!
# Diagonal marking units (engineering rescaling)

 Read with exactly the same actual data (can specialize W=0 there if needed for
 positivity/ratio only). We give exact identity on every monomial, no price across changing
 basis asserted beyond exact toll. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Sources
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open YM.Marker YM.Multi YM.Comparison.RG02.Order Integral Actual Local
open YM.Extra.Trajectories (Names Names.look connected pass_connected connected_quiet)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {V X : Type} [DecidableEq V] [Fintype V] {C : Census V} (a b : V→ℂ) (h : Lit C X)
local notation "P"=> dilation C a

def times := P ∘ h
def amount (i : C.Mode) := ∏ j∈i.val,a j
omit [Fintype V] in
lemma at_times (s : C.Mode) : atMark s (times a h)=amount a s • atMark s h := rfl
omit [Fintype V] in
lemma times_times : times a (times b h) = times (a*b) h := by ext i j; simp_rw [times, comp_apply,dilation_part, Pi.mul_apply, Finset.prod_mul_distrib, mul_assoc]
omit [Fintype V] in
lemma times_one : times (1:V→ℂ) h=h := by ext i j; simp [times,dilation_part]
open Cumulants (quiet_dilation log_map)
omit [Fintype V] in
lemma unit_dilate (x : Poly C) : P (unitScale x)= unitScale (P x) := by unfold unitScale; rw [map_smul, quiet_dilation]
omit [Fintype V] in
lemma price_times (x : Poly C) (w : V→ℝ) : Poly.price w (P x)=Poly.price (fun i=> w i* ‖a i‖) x := by
   unfold Poly.price; simp_rw [dilation_part, Poly.toll,norm_mul,norm_prod,Finset.prod_mul_distrib,mul_assoc]
omit [Fintype V] in
lemma measure_times [MeasurableSpace X] (μ : Measure X) : P (charge μ h)=charge μ (times a h) := by
   ext i; rw [components,dilation_part,components,at_times]; unfold amount; rw [show ∀ c : ℂ, (c • atMark i h)=fun x=> c * atMark i h x from fun _=>rfl,integral_const_mul]
omit [Fintype V] in
lemma leaf_times [MeasurableSpace X] (ht : Leaf.All h) : Leaf.All (times a h) := fun i=> Leaf.multiply (Envelope.constC (amount a i)) (ht i)

variable {c f : Side} (S : StepData c f) {G : Gauge} (X : Lit C (Config G f)) (g : ℝ)
omit [Fintype V] in
lemma push_times : times a (Actual.Push S g X)= Actual.Push S g (times a X) := by
  funext V; unfold times; rw [comp_apply]; unfold Actual.Push; rw [measure_times]; congr 1; funext U; rw [times,comp_apply,map_smul]; rfl
omit [Fintype V] in
lemma floor_times (R : Rep G f) (H : Floor R X) : Floor R (times a X):= ⟨fun i=> (quiet_dilation a (X i)).trans (H.vacancy i), leaf_times a X H.safe,fun _ _=> congrArg P (H.gauges ..)⟩

section normalized
variable (R : Rep G f) (J : Config G c) (A : S.patch.Branches S.kernel G) (H : Normal.Strong f R.eval) (I : Floor R X)
omit [Fintype V] in
lemma normalize_times : P (normalized R X S J)= normalized R (times a X) S J := by
   rw [normalized,unit_dilate]; exact congrArg unitScale (congrFun (push_times a S X R.beta) J)
omit [Fintype V] in
lemma floor_one (S : StepData c f) (J : Config G c) (R : Rep G f) (I : Floor R X) (H : Normal.Strong f R.eval) (A : S.patch.Branches S.kernel G) : (normalized R X S J).part C.quiet=1 := by
   apply unitScore (x:=Actual.Push S R.beta X J); rw [← Normal.scan_actual S R.beta J X A I.safe, Normal.scan_bare _ _ _ _ R.eval H A (fun _=> I.vacancy)]; exact_mod_cast (Normal.total_pos S R.beta J R.eval H A).ne'
include A H I in
lemma connected_times : P (Local.cumulant R X S J) = Local.cumulant R (times a X) S J := by
  unfold Local.cumulant; rw [log_map P (quiet_dilation a) (floor_one X S J R I H A), normalize_times]
end normalized

-- transmit formal packet after choosing dimensions
section formal
variable {S} {o : ℝ} {p : Clip} {P' : PathData G} {O : ChartRatio G} {r : ℕ}
  (Q : Bulk.Kernel S p P' O) (F : Forest S.ratio) (t : S.Choices)
  (W : Bulk.Colors C G f) (x : fieldDir G c 1) (y : Bulk.Joint S F (G:=G))

def scale : Bulk.Colors C G f := {vac:= W.vac,power:=W.power, mark i:= amount a i.val • W.mark i}
local notation "W'"=>scale a W
variable {W} (hW : Bulk.Well W)
include hW
open Assembly (GradeAt)
private def sax (z : ℂ) : ℂ→L[ℝ] ℂ:= z • ContinuousLinearMap.id ℝ _
omit hW in
private lemma degree_left {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E→ℂ} (k : GradeAt n x) (s : ℂ): GradeAt n (s • x) := by
  refine ⟨k.smooth.const_smul s,fun i hi=>?_⟩
  rw [show s • x=sax s ∘ x from rfl,(sax s).iteratedFDeriv_comp_left k.smooth le_top,k.vanish i hi]; ext e; exact (sax s).map_zero
-- omit include? here private doesn't depend on W
omit [Fintype V] in
lemma well_times : Bulk.Well W':= ⟨hW.suppose_vac,fun i=> degree_left (hW.suppose_mark i) (amount a i.val),hW.natural,
    fun i s k x=> congrArg ((amount a i.val) • ·) (hW.gauges i s k x),hW.envelope, fun i s=> Leaf.multiply (Envelope.constC (amount a i.val)) (hW.prices i s)⟩
omit hW in
omit [Fintype V] in
lemma standard_scale (hp : W.Standard): (W').Standard:= ⟨well_times _ hp.1,hp.2⟩
local notation "D₁"=> reweight (r:=r) (R:=C) a
local notation "B" => Bulk.geometric Q F t W
local notation "q" => Bulk.Fk Q F t W x r
local notation "w" => Bulk.Fk Q F t W' x r
private lemma exponent_charges : D₁ (series C r (Assembly.affine W.power (Bulk.markFn S F W) (B) y))=series C r (Assembly.affine (W').power (Bulk.markFn S F W') (B) y) := by
   apply Join.both_parts; intro s b
   rw [reweight_part,polarization,polarization]
   simp only [Assembly.affine,map_add,Poly.part_plus,Assembly.realCoeff,Assembly.beads]
   by_cases h:s.val.Nonempty
   · let i:Hot C:= ⟨s,h⟩
     have he:= (Cumulants.hot_iff_ne s).1 h
     rw [if_neg he,zero_add,zero_add]; unfold Assembly.curve;
     rw [PowerSeries.coeff_mk,PowerSeries.coeff_mk, (show ∀ z : Hot C→ℂ, (lit C z).part s=z i from fun z=> part_lit z i) _, (show ∀ z : Hot C→ℂ, (lit C z).part s=z i from fun z=> part_lit z i) _]
     have hk (j):= Assembly.jet_apply_left (sax (amount a i.val)) (Bulk.markFn S F W i) j ((Bulk.joint_receipt S F (hW.suppose_mark i)).smooth.of_le le_top:(ContDiffAt _ _ (Bulk.markFn S F W i) 0)) y
     rw [show Assembly.markLetter (W').power (Bulk.markFn S F W') i y b.val.card=_ from (hk (W.power i+b.val.card)).symm]
     change _=_*((∏ i∈s.val,a i)*Assembly.markLetter _ _ _ _ _); ring
   replace h : s=C.quiet:= of_not_not (mt (Cumulants.hot_iff_ne s).2 h)
   rw [h,Assembly.mark_curve_quiet,Assembly.mark_curve_quiet]; unfold Census.quiet; rw [prod_empty, one_mul]
lemma fk_scale : D₁ (q)=(w) := by
   ext i; rw [reweight, dilation_part, Bulk.Fk, Bulk.Fk]
   have h := Assembly.contracted (Bulk.stage Q F x) (Bulk.hinge F) W.power (Bulk.markFn S F W) (B) (Q.covariance F t) (Q.symm F t) (Q.positive F t) r i
   rw [h.2, (Assembly.contracted _ _ _ _ _ _ _ (Q.positive F t) r i).2,← integral_const_mul]; apply integral_congr_ae; filter_upwards with z
   rw [Assembly.exponent_identity,Assembly.exponent_identity,← dilation_part]; exact congrArg (Marker.Poly.part · i) ((pass_map (D₁) _ (Assembly.driver_quiet ..) ((quiet_dilation _ _).trans (Assembly.driver_quiet ..))).trans (congrArg Marker.Poly.pass (exponent_charges a Q F t _ hW)))

omit hW
lemma slides (z : Grade C r) (k : ℕ) : P (observe C r z k)=observe C r (D₁ z) k := by
   unfold observe; split
   · rw [map_smul]; congr 1; ext i; exact (reweight_part a z i _).symm
   rw [map_zero]
lemma denominator_scale (z : Grade C r) : D₁ (denominator z)=denominator z := by
   apply Join.both_parts; intro s t; rw [reweight_part,denominator, bottom_value]; split
   · subst s; unfold Census.quiet; rw [prod_empty,one_mul]
   rw [mul_zero]
lemma ratio_scale (z : Grade C r) (h : UnitLeading z) : D₁ (Order.ratio z)= Order.ratio (D₁ z) := by
   have hx : UnitLeading (D₁ z):= (quiet_dilation _ z).trans h
   apply ratio_unique hx; rw [reweight_denominator, ← denominator_scale a z,← map_mul,recovers h]
lemma log_scale (z : Grade C r) (h : UnitLeading z) : D₁ (logMarked z)=logMarked (D₁ z):= by rw [logMarked, log_map (D₁) (quiet_dilation _) (ratio_quiet h),ratio_scale a z h]; rfl
lemma value_scale (z : Grade C r) (v : ℂ) : P (value v z)=value v (D₁ z):= by unfold value; rw [map_sum]; apply sum_congr rfl; intro i _; rw [map_smul,slides]
end formal
end YM.Comparison.RG02.Sources
