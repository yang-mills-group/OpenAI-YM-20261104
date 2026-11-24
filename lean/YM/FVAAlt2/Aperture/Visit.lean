import YM.FVAAlt2.Aperture.Purchase
/-! Fits & Major of Aperture. Native analytic regulator tests **at fixed regulator**, not Uniform.Haar. Bound leakage & Integrable budgets deterministic at each horizon via Laplace.prism. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.FVAAlt2.Aperture
open Set Filter Finset MeasureTheory Function Lattice RG Precision Wilson Exterior Tree Bid
open PertExtension.Series Bulk Adjacent Order Assembly Marker Multi YM.Next.SectorChange Integral Gaussian
open Work.F03
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure Actual
open scoped Topology ContDiff Classical Matrix BigOperators ENNReal NNReal Matrix.Norms.Frobenius
variable {c f:Side}{G:Gauge}{P:PathData G}{p:Clip}{O:ChartRatio G}{S:StepData c f}
variable (K:Bulk.Kernel S p P O)(F:Forest S.ratio)(w:S.Choices)(C:UnitCost)
variable {V:Type} [DecidableEq V] {R:Census V}(W:Bulk.Colors R G f)
local notation "X"=>fieldDir G c 1
local notation "Y"=>fieldDir G f 1
local notation "T"=>Bulk.Joint S F (G:=G)
local notation "L"=>Precision.Key F G→ℝ
local notation "ρ" => C.enter
local notation "H" => F.Slice G
local notation "Q" => K.covariance F w
open Classical
variable (t:ℝ) (x:fieldDir G c 1)
local notation "ζ"=> Bulk.translated K F x
local notation:max "β_" z:max=> temperature (ρ z)
local notation:max "V_" z:max => sample z x
variable (A:Set (F.Slice G)) (D:BudgetPoint)
local notation "I" => F.Free
local notation "μ" => cloud (K.covariance F w)
local notation "Ω" => extent K F t x
open Laplace Laplace.Prism PertExtension.Series.Tested Affinity
-- translate so public Laplace.aperture at $0$ applies to prove budget
lemma repZero : repSample F t (0:X)=1:=by
   ext1 v; unfold repSample sample; rw [smul_zero, link_one,replica_one];rfl
local notation:max "u_" z:max=> deposit K F 1 z
local notation "dA"=> extent K F t x A
lemma enact (v:L) : Integral.offset K F t (0:X) (u_ x+v) = swing K F t x v:=by
    rw [offset,signal]; change t • (_+ gaugeCount (u_ x+ v))=_; unfold deposit; rw [map_zero,zero_add, one_smul,map_add, smul_add]; rfl
lemma translate_scope (v:L) : v∈dA ↔ ((u_ x)+v)∈scope K F t (0:X) A:=by
    unfold scope extent; simp only [Set.mem_inter_iff,Set.mem_preimage]; rw [walk, enact, repZero]
lemma changes (v:L) : let τ:=stage K F x; ‖ζ v‖ ≤ ‖translated K F (0:X) (u_ x+v)‖+ ‖τ- translated K F (0:X) (u_ x)‖:=by
    intro τ; refine _root_.le_trans (le_of_eq (congr_arg norm ?_)) (norm_add_le ..); unfold Bulk.translated Assembly.translate; rw [map_add]; unfold τ; abel
lemma zero_bill (t:ℝ): Integral.zone K D F t (0:X) = Integral.zone K D F 0 0 :=by unfold Integral.zone; rw [repZero,repZero]
variable {δ:ℝ}
lemma cheaper (h: covers0 F A K) {B} (hp:B⊆A)(hb : MeasurableSet B):covers0 F B K:= ⟨hb,hp.trans h.2.1, ( Set.image_mono hp ).trans h.2.2 ⟩
include D in
lemma surrounds (h:0<δ):∃ B∈𝓝 (1:F.Slice G), IsOpen B ∧ covers0 F B K ∧ ∀ A:Set (F.Slice G), A⊆B→ MeasurableSet A→ Prism.Fits (stage K F x) (hinge F) δ (fun t=>extent K F t x A) := by
    obtain ⟨B,hB,hp,H₁⟩:= Laplace.aperture K F (0:X) D (half_pos h); refine ⟨B,hB,hp, ⟨hp.measurableSet,?_ ,?_⟩, fun A ha hw=>?_⟩ -- repeated H.S
    · obtain ⟨t,h⟩:= (H₁ B (Set.Subset.refl _) hp.measurableSet).2.exists
      intro u hu; have hh:= (h hu).1; rw [repZero] at hh; exact hh
    · rintro u ⟨v,hv,rfl⟩; obtain ⟨t,h⟩:= (H₁ B (Set.Subset.refl _) hp.measurableSet).2.exists; exact (h hv).2.2
    let c:= ‖stage K F x- translated K F (0:X) (u_ x)‖; have hh : Tendsto (fun (t:ℝ) => t*c) along (𝓝 0):=by simpa using ((show Tendsto (fun t:ℝ=>t) (𝓝 0) (𝓝 0) from tendsto_id).mul_const c).mono_left (show along≤𝓝 0 from nhdsWithin_le_nhds) -- syntax
    filter_upwards [ (H₁ A ha hw).1, Tested.eventually_pos, hh.eventually (gt_mem_nhds (half_pos h)) ] with t H₁ ht hu v hv
    obtain ht' := ((H₁ (u_ x+v) ( (translate_scope K F t x A v).mp hv )))
    change t*(1+ ‖translated K F x v‖)≤_
    let l:= ‖translated K F (0:X) (u_ x+v)‖; change t*(1+l)≤ δ/2 at ht'; have hvh: ‖translated K F x v‖≤l+c:= changes K F x v; change t*c < δ/2 at hu; nlinarith only [ht',hvh,hu,ht]
-- reciprocal jump. persistent entire if any A. determin each cutoff
lemma root_bill (hp:A∈𝓝 1): Major (stage K F x) (hinge F) (fun v=> extent K F v x A) := by
   have hV : mouth O (ι:=F.Free)∈𝓝 (0: AxisChart G F):= (isOpen_set_pi Set.finite_univ (fun _ _=>Metric.isOpen_ball)).mem_nhds (fun _ _=>Metric.mem_ball_self K.ratio.patch)
   have hx : Tendsto (release (1:F.Slice G) ∘ starship F) (𝓝 0) (𝓝 1):=by
       have he := Continuous.tendsto ((release_continuous (1:F.Slice G)).comp ( starship (G:=G) F ).continuous) (0:T); rw [Function.comp_apply,map_zero] at he; rwa [show release (1:H) (0:AxisChart G F)=1 from ?_] at he; funext;simp [release]
   obtain ⟨r,hr,H₁⟩:= Metric.eventually_nhds_iff.mp (( ((show Continuous (starship (G:=G) F) from (starship F).continuous).tendsto (0:T)).eventually (show mouth O ∈𝓝 (starship F (0:T)) from by rw [map_zero];exact hV) ).and (hx.eventually hp))
   refine ⟨r,hr,Tested.eventually_pos.mono fun t ht v hv=>?_⟩
   by_contra! he; have h: t*(1+‖translated K F x v‖)<r:=he; have hl:dist (t • translated K F x v) 0 < r:= by rw [dist_zero_right, norm_smul, Real.norm_of_nonneg ht.le]; nlinarith
   exact hv (H₁ hl)
variable (s:R.Mode)[Fintype V]
def bank (r:ℕ):Order.Grade R r:= Assembly.prescription (stage K F x) (hinge F) W.power (scoreMark F C W) (core K F w C W) (K.covariance F w) (K.symm F w) r
lemma units (r:ℕ) : UnitLeading (bank K F w C W x r):= Assembly.prescription_unit ..
lemma symmetric (r:ℕ): Order.Symmetric (bank K F w C W x r):= Assembly.prescription_sym _ _ _ _ _ _ _ (K.positive F w)
variable (hW:Well W)(B:Bed)(hB: YM.FVAAlt2.Period.Rent.Right p P f B)
include hW hB
lemma isReady : Assembly.Admissible W.power (scoreMark F C W) (core K F w C W):= by
   have h:=matured K F w C W B hB hW
   exact ⟨⟨h.smooth.of_le le_top, Affinity.Buy.begins h,fun y=> h.jet_z y one_lt_two⟩, fun i=> ⟨(born_mark F C W hW i).smooth.of_le le_top, fun _ he v=> (born_mark F C W hW i).jet_z v he ⟩⟩
include D
lemma permits (r:ℕ): ∃ Z∈𝓝 (1:F.Slice G), IsOpen Z ∧ covers0 F Z K ∧ ∀ A:Set (F.Slice G), A⊆Z→MeasurableSet A→ A∈𝓝 1→ Trial (detail (bank K F w C W x r) s) (fun t=> (tale K F w C W t x A).part s) r:=by
    obtain ⟨δ,hδ,Dδ⟩:= Prism.squeeze (stage K F x) (Bulk.hinge F) r s (K.positive F w) (K.symm F w) (isReady K F w C W hW B hB); obtain ⟨Z,hZ,hv,H',ht⟩:= surrounds K F x D hδ
    refine ⟨Z,hZ,hv,H',fun A hi hp hl=>?_⟩; let M:= (fun t=> extent K F t x A); have he:= cheaper K F Z H' hi hp
    have hu: ∀ᶠ t:ℝ in along, Good μ ((M t).indicator (dims K F w C W t x)) ∧ charge μ ((M t).indicator (dims K F w C W t x))= tale K F w C W t x A:=by
       filter_upwards [Tested.eventually_pos, C.bright.filter_mono (show along≤𝓝 (0:ℝ) from nhdsWithin_le_nhds) ] with v hv hh
       exact purchase K F w C W v x A B hB hW hv hh he
    exact trial_congr (hu.mono fun _ h=> congr_arg (fun u=> Marker.Poly.part u s) h.2) (Dδ M (ht A hi hp) (root_bill K F x A hl) (hu.mono fun t u=>⟨extent_meas K F t x A hp,u.1 ⟩))
end YM.Comparison.RG02.FVAAlt2.Aperture
