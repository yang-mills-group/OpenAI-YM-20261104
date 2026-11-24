import YM.Integration.FVA1Physical.Wilson.FluctuationExterior
import YM.Integration.FVA1Physical.Sources.Round2.PosteriorReclock

/-! A copied, signed Wilson insertion in an actual block. Only its size on the
local hotel enters the transfer of its normalized resample to the physical
Haar conditional. Its values on all rough exterior configurations can vary. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Set MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior Push.Uniform
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk MSbar.Mosaic MSbar.Lis
open YM.Integration.FVA1Physical.Wilson
open scoped Classical Topology
variable {G:Gauge} {c f:Side} {S:StepData c f}

theorem copied_test_local (F:Forest S.ratio) (X Y:Support f) (V:Voice G) (O:Config G c)
    (μ:Positions (Key F G)) (a b:ℝ) (cle:Clear G V) (xy:X⊆Y) (φ:Config G f→ℝ) (me:Measurable φ)
    {M:ℝ} (hM:0 ≤ M)
    (cap:∀ W∈hotel F X Y V O μ a b, |φ (chambers F Y V O μ W)| ≤ M) :
    let H:=hotel F X Y V O μ a b
    let copy:=chambers F Y V O μ
    let ψ:=H.indicator (φ ∘ copy)
    GaugeLocal S (youth F Y) ψ ∧ (∀ W,|ψ W| ≤ M) := by
  intro H copy ψ
  have covering:=garden_main F X Y V O μ cle xy (A:=a) (B:=b)
  have data:=informed F X Y V O μ cle xy
  have bounded (W):|ψ W| ≤ M:=by
    by_cases hit:W∈H
    · exact (congrArg abs (Set.indicator_of_mem hit _)).le.trans (cap W hit)
    · exact (congrArg abs (Set.indicator_of_notMem hit _)).le.trans (abs_zero.le.trans hM)
  refine ⟨⟨⟨(me.comp data.1).indicator covering.from_here,M,fun W=>bounded W⟩,?_,?_⟩,bounded⟩
  · intro k inner W
    by_cases hit:W∈H
    · change H.indicator (φ ∘ copy) _=H.indicator (φ ∘ copy) W
      rw [Set.indicator_of_mem ((covering.within k inner W).1 hit),Set.indicator_of_mem hit]
      exact congrArg φ (invites F X Y V O μ cle xy k inner W)
    · change H.indicator (φ ∘ copy) _=H.indicator (φ ∘ copy) W
      rw [Set.indicator_of_notMem ((covering.within k inner W).not.mp hit),Set.indicator_of_notMem hit]
  · intro W W' agree
    by_cases hit:W∈H
    · change H.indicator (φ ∘ copy) W=H.indicator (φ ∘ copy) W'
      rw [Set.indicator_of_mem hit,Set.indicator_of_mem ((Iff.of_eq (covering.localized W W' agree)).mp hit)]
      exact congrArg φ (data.2.2 W W' agree)
    · change H.indicator (φ ∘ copy) W=H.indicator (φ ∘ copy) W'
      rw [Set.indicator_of_notMem hit,Set.indicator_of_notMem ((Iff.of_eq (covering.localized W W' agree)).not.mp hit)]

theorem resample_cut_invariant (F:Forest S.ratio) (X Y:Support f) (V:Voice G)
    (R:Rep G f) (i:S.Choices) (O:Config G c) (μ:Positions (Key F G)) (a b:ℝ) (φ:Config G f→ℝ) :
    let H:=hotel F X Y V O μ a b
    let r:=woolModel F X V R Y i O μ a b
    Rota.resample F (board F X) r H (H.indicator φ)=Rota.resample F (board F X) r H φ := by
  intro H r
  funext W
  apply integral_congr_ae
  filter_upwards [] with t
  let U:=twirl F (board F X) t W
  change spec H W*(r U*H.indicator φ U)=spec H W*(r U*φ U)
  by_cases hit:U∈H
  · rw [Set.indicator_of_mem hit]
  have hr:r U=0:=by
    unfold r woolModel
    change (spec H U * _)/_=0
    rw [show spec H U=0 from Set.indicator_of_notMem hit _,zero_mul,zero_div]
  rw [hr,zero_mul,zero_mul]

theorem cut_source_posterior (V:Voice G) (cle:Clear G V) (simple:G.Simple) (H H':Stage) (P:Patch)
    (K:KernelChoices) (br:P.Branches K G) {D q:ℝ} (hD:0 ≤ D) (hq:0 < q) :
    ∀ᶠ x:ℝ in atTop,∀ (A:Issue G),A.S.patch=P → A.S.kernel=K →
    Season V H H' x A.pre A.post A.S (courage G P.L x) →
    ∀ (z:Positions (Primary A.c G)) (b:Site A.f),‖z‖ ≤ D*room (tip G P.L x) →
    let y:=tip G P.L x;let X:=boxX y b;let Y:=boxY y b
    let O:=represent (tint G (Body 1 A.c) z);let μ:=vest (priced A.F A.v A.pre.clip A.pre.path) z
    let live:=hotel A.F X Y V O μ (pillow y) (room y);let copy:=chambers A.F Y V O μ
    let law:=woolModel A.F X V A.pre Y A.v O μ (pillow y) (room y)
    ∀ (φ:Config G A.f→ℝ),Measurable φ → ∀ (M W ε:ℝ),0<M → 0 ≤ ε →
    (∀ U∈live,|φ (copy U)| ≤ M) →
    (∀ U∈live,|Rota.resample A.F (board A.F X) law live (φ ∘ copy) U-W| ≤ ε) →
    |expect A.S A.pre O (live.indicator (φ ∘ copy))-W| ≤ 2*ε+10*M*y^(-q) := by
  filter_upwards [fluctuation_field_exterior V cle simple H H' P K br hD hq] with x exterior
  intro A hp hk season z b hz y X Y O μ live copy law φ me M W ε hM hε hbound point
  have xy:X⊆Y:=halo_subset ..
  let ψ:=live.indicator (φ ∘ copy)
  obtain ⟨loc,cap⟩:=copied_test_local A.F X Y V O μ (pillow y) (room y) cle xy φ me hM.le hbound
  have unit:GaugeLocal A.S (youth A.F Y) (M⁻¹ • ψ):=
    ⟨(Envelope.const _).mul loc.currency,fun k hk U=>congrArg (M⁻¹*·) (loc.turn k hk U),
      fun U U' e=>congrArg (M⁻¹*·) (loc.located U U' e)⟩
  have bounded (U):|(M⁻¹ • ψ) U| ≤ 1:=by
    change |M⁻¹*ψ U| ≤ 1
    rw [abs_mul,abs_of_pos (inv_pos.mpr hM)]
    exact (inv_mul_le_iff₀ hM).mpr ((cap U).trans_eq (mul_one M).symm)
  have reduce:=resample_cut_invariant A.F X Y V A.pre A.v O μ (pillow y) (room y) (φ ∘ copy)
  have result:=exterior A hp hk season z b hz (M⁻¹ • ψ) unit bounded (M⁻¹*W) (M⁻¹*ε)
    (mul_nonneg (inv_nonneg.mpr hM.le) hε) (fun U hit=>by
      rw [resample_vscale]
      change |M⁻¹*Rota.resample A.F (board A.F X) law live (live.indicator (φ ∘ copy)) U-M⁻¹*W| ≤ M⁻¹*ε
      rw [reduce,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hM)]
      exact mul_le_mul_of_nonneg_left (point U hit) (inv_nonneg.mpr hM.le))
  rw [e_mul,←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr hM)] at result
  apply ((inv_mul_le_iff₀ hM).mp result).trans_eq
  field_simp [hM.ne']
  ring

end YM.Integration.FVA1Physical.Round2.Curvature
