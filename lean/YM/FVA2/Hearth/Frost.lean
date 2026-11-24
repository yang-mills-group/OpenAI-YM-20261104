import YM.FVA2.Hearth.Stamp
/-!
# Tree independence in the conditional prescription

Still a single finite inversion torus. Here see `any_tree`: even the **unmasked**
open-field reading on all these multiscale choices of trees gives the same
answer (e.g. for the whole `PreTest` from a product of Folio stencils).
This uses the same tagged predictors within one `Fabric`; see also `Hearth/Choice.lean`
for changing those. Does not mean independence from the choice of geometry or other
such claims!
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{L:Fabric G n}(T R:Cloth L)

lemma accounted {V E:Type}[Fintype V][Fintype E]{D:Loom V E}(X:D.Truss) : Fintype.card X.Bulk= Fintype.card E - Fintype.card {v:V// v ≠ D.origin}:= by
 let e: {v:V// v ≠ D.origin}→X.Tree := fun x=> ⟨X.wire x.val x.property,X.wire_branch ..⟩
 have he:Fintype.card {v:V// v≠D.origin}= Fintype.card X.Tree:=by
     apply Fintype.card_congr (Equiv.ofBijective e ?_); constructor
     · exact fun x y h=> Subtype.ext (X.distinguish _ _ _ _ (Subtype.ext_iff.mp h))
     rintro ⟨i,v,h,rfl⟩; exact ⟨⟨v,h⟩,rfl⟩
 rw [he]; exact Fintype.card_subtype_compl _
lemma kit : Fintype.card (Warm T)= Fintype.card (Used L) - Fintype.card {v:Hub L// v≠ (rift L).origin}:= by rw [Fintype.card_congr (leeway T), accounted]; congr 2; apply Subsingleton.elim
lemma rank_chart : Module.finrank ℝ (Facade.Panel T)= Module.finrank ℝ (Facade.Panel R) := by simp [Facade.Panel, Module.finrank_pi_fintype,kit]

variable (y:Flats G (Bottom L))(u:ℝ)
variable (O: Wilson.Config G n→ℝ)
local notation "a"=> expLinks G _ (u• y) -- local type?
-- integral = total.Enrolled over all Haar Used
local notation "μ"=> Chart.physical G (Used L)
local notation "ν"=> Chart.physical G (Warm T)
local notation "κ"=> Chart.physical G (Loom.Truss.Bulk (fir T))
variable (w:L.Accounts→ℝ→ℝ)
 def inspection (x:Used L→G.El):= attending L O (rear L a x)* Real.exp (-(u^2+L.spend (fun i=>w i u) (rear L a x))/u^2)
local notation "p"=> inspection y u O w
lemma rift_move (g:Hub L→ G.El)(v: Used L→G.El)(h:g (rift L).origin=1)(hO:PreTest O) : p ((rift L).spin g v) = p v := congr_arg₂ (· * ·) (rift_marks L O hO v g h a) (congr_arg (fun x=> Real.exp (-(u^2+x)/u^2)) (rift_price L (fun i=> w i u) v g h a))

variable (hO:PreTest O)
include hO
lemma complete (hf:∀ i, 0< w i u) : Integrable (p) μ := by
 let K:= rear L a
 have hb: Measurable K:= (rear_cont L).measurable.comp (measurable_const.prodMk measurable_id)
 have he:Measurable p := ((eligible L hO).reading.meas.comp hb).mul (Measurable.exp (((measurable_const.add ((L.measurable_cost _).comp hb)).neg).div_const _))
 obtain ⟨M,hp⟩:= (eligible L hO).reading.bounded
 apply (integrable_const M).mono' he.aestronglyMeasurable (Eventually.of_forall fun x=>?_)
 have hu : Real.exp (-(u^2+L.spend (fun i=> w i u) (K x))/u^2) ≤ 1:= Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (add_nonneg (sq_nonneg _) (L.nonneg_cost hf (K x)))) (sq_nonneg _)); unfold inspection; rw [norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]; exact (mul_le_of_le_one_right (norm_nonneg _) hu).trans (hp _)

local notation "E"=> MeasurableEquiv.arrowCongr' (leeway T) (MeasurableEquiv.refl G.El)
lemma fuel_points (hf:∀ i,0<w i u) :
 (∫ x,p x ∂μ)=∫ x,income T w y O u x ∂ν:= by
 rw [show (∫ x,p x ∂μ)=_ from (fir T).elimination (D:=rift L) G.probHaar _ (complete y u O w hO hf) (fun g h v=> rift_move y u O w g v h hO)];
 have he : MeasurePreserving E ν κ:= measurePreserving_arrowCongr' _ _ (leeway T) (MeasurableEquiv.refl G.El) (fun i=> MeasurePreserving.id _) -- infer Pi.Meas?
 exact (he.integral_comp' (fun i=> p ((fir T).board i))).symm
variable (z:L.Accounts→PowerSeries ℝ)(hz:∀ i,0<term (z i) 0){J J':ChartRatio G}(hj:LocalRatio J)(hr:LocalRatio J')
variable (N:ℕ)(hw:∀ i,ContDiffAt ℝ ω (w i) 0)(h:∀i,Through N (amount (w i)) (z i))
omit hO
include hz h hw
omit hw in
lemma zeroWeight (i:L.Accounts): 0<w i 0:= by have ht:=h i 0 (Nat.zero_le _); unfold amount at ht; rw [read_rise, jet_zero] at ht; rw [ht]; exact hz i
include hj hr
include hO
lemma freeze (hm:∀ i,Measurable (w i)) : constit T w y J (rad T O)=constit R w y J' (rad R O):= by
 have he: ∀ i,ContinuousAt (w i) 0:= fun i=> (hw i).continuousAt; have hp : ∀ i, 0<w i 0:=zeroWeight w z hz N h
 have hh:Tracks (Burn R w y O) (constit R w y J' (rad R O)):= aspirations R w y O hO hr he hp (steep R z hz w y hw N h) hm
 refine Tracks.seam (aspirations T w y O hO hj he hp (steep T z hz w y hw N h) hm) hh ?_
 have hx:∀ᶠ g in Tested.germ, ∀ i,0<w i g:= eventually_all.mpr fun i=> (he i).eventually (eventually_gt_nhds (hp i)) |>.filter_mono nhdsWithin_le_nhds
 filter_upwards [hx] with v hv; unfold Burn; rw [rank_chart T R,← fuel_points T y v O w hO hv, ← fuel_points R y v O w hO hv]
omit hO hw h
omit hz hj hr in
lemma one_register : PreTest (1:Wilson.Config G n→ℝ):= ⟨fun _ _ _=>rfl,Orb.one_test,continuous_const⟩
include h hw
lemma cold (hm:∀ i,Measurable (w i)): constit T w y J 1=constit R w y J' 1:= freeze T R y 1 w one_register z hz hj hr N hw h hm
omit h hw
include hO
-- measured at same coupling `u`. regulator arbitrary.Bare operator H theorem.No Ω
private lemma same_free (k:ℕ) : coeff k
 (Stack.read y (drive T (z∘some) (headquarters z) (imprintRoot O) J (collared T z hj hz)).2) = coeff k
 (Stack.read y (drive R (z∘some) (headquarters z) (imprintRoot O) J' (collared R z hr hz)).2):= by
 let f (i: L.Accounts) t:= sheet z k t i
 have hf(i:L.Accounts):ContDiffAt ℝ ω (f i) 0:= heated z i k
 have H(i:L.Accounts):Through k (amount (f i)) (z i):= traced_bare z i k
 have hi(i:L.Accounts):Measurable (f i):= by unfold f sheet peval Zone.eval; exact Finset.measurable_fun_sum _ (fun i _=> (measurable_id.pow_const i).smul_const _)
 rw [← attained T y z hz hj f k hf H O hO k le_rfl, ← attained R y z hz hr f k hf H O hO k le_rfl, freeze T R y O f hO z hz hj hr k hf H hi,cold T R y f z hz hj hr k hf H hi]

-- off-truss normalized evolution. No lookahead at next era.
theorem any_tree :
 (drive T (z∘some) (headquarters z) (imprintRoot O) J (collared T z hj hz)).2
 = (drive R (z∘some) (headquarters z) (imprintRoot O) J' (collared R z hr hz)).2:= Stack.into (fun x=> PowerSeries.ext (fun _=> same_free T R x O hO z hz hj hr _))
omit hO
local notation "X"=> drive T (z∘some) (headquarters z)
local notation "Y"=> drive R (z∘some) (headquarters z)
local notation "A₀"=> overheadC T z hz y J
local notation "A₁"=> overheadC R z hz y J'
local notation "p₀"=> collared T z hj hz
local notation "p₁"=> collared R z hr hz
variable (A B:Ticket (Flats G n))
lemma any_growth : PowerSeries.C A₀ * Stack.read y (X A J p₀).1.W = PowerSeries.C A₁ * Stack.read y (Y B J' p₁).1.W:= by
 apply PowerSeries.ext; intro i;
 let f(j:L.Accounts) t:=sheet z i t j; have hf : ∀ j, ContDiffAt ℝ ω (f j) 0:= fun j=> heated z j i
 have hg(j:L.Accounts):Measurable (f j):= by unfold f sheet peval Zone.eval; exact Finset.measurable_fun_sum _ (fun _ _=> (measurable_id.pow_const _).smul_const _)
 have H(j:L.Accounts):Through i (amount (f j)) (z j):= traced_bare z j i
 rw [←sales T z hj hz f y hf i H A i le_rfl, ←sales R z hr hz f y hf i H B i le_rfl, cold T R y f z hz hj hr i hf H hg]

omit hr in
lemma annex : constantCoeff (Stack.read y (X A J p₀).1.W)=1:= by rw [←avowed T _ _ (collared T z hj hz) hj A]; exact shape (Quadratic.upright _ _ _ (reserve T (z∘some) (headquarters z) J hj (OpenSlots.restores ..))) _
lemma any_head : overheadC T z hz y J= A₁:= by have h:= congr_arg constantCoeff (any_growth T R y z hz hj hr 1 1); rwa [map_mul,map_mul, constantCoeff_C,constantCoeff_C, annex T y z hz hj 1, annex R y z hz hr 1,mul_one,mul_one] at h
lemma any_price : (X A J p₀).1.W=(Y B J' p₁).1.W:= by
 apply Stack.into; intro x; have he:= any_growth T R x z hz hj hr A B; rw [any_head T R x z hz hj hr] at he
 exact ((isUnit_iff_ne_zero.mpr (ne_of_gt (high_pos R z hr hz x))).map (C (R:=ℝ))).mul_left_cancel he
-- also reduced price equals. Derive canon Haar determinant relative.S
omit hj hr in
lemma stamp_head : overheadC T z hz y J= Real.exp (-((reduced _ (policyready T z hz)).flourish y)/2) * overheadC T z hz 0 J:= by unfold overheadC craving; rw [constant0,← mul_assoc (Real.exp ..),← mul_assoc (Real.exp ..), ←Real.exp_add]; ring_nf
lemma any_Q : (X A J p₀).1.Q.P=(Y B J' p₁).1.Q.P:= by
 apply records; intro x; rw [receives,receives]; have he:= any_head T R x z hz hj hr; rw [stamp_head T,stamp_head R,any_head T R 0 z hz hj hr] at he; have hp:= Real.exp_injective (mul_right_cancel₀ (ne_of_gt (high_pos R z hr hz 0)) he); linarith

theorem any_state : (X A J p₀).1= (Y B J' p₁).1:= by
   have v:= any_price T R z hz hj hr A B; have w:= any_Q T R z hz hj hr A B
   generalize he:(X A J p₀).1=K, hK:(Y B J' p₁).1=P at *; rcases P with ⟨⟨L₁,u⟩,F⟩; rcases K with ⟨⟨M,k⟩,H⟩; congr

end YM.FVA2.Hearth
