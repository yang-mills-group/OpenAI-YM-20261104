import YM.FrontierTrace.Primary.Wings

/-!
# Locus shift exact Ward identity at all r>0

Contour translation outside smaller interior. No hypothesis about dilation Ward at all
or value of d for this normalizer. ∑translations on Wing first leg send to ∂₀ pair.
Add the secondProbe term for literal Gauss test equality, avoid any EOM contact terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrontierTrace.Primary
open Function Set Filter Analysis Trace Table Work.A01 Work.A05 Next.UVStress MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace Interval Classical
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}(F:Spec.Final C f S)
    (ℓ:E4) {t:ℝ}
local notation "X"=> F.sector.turns
local notation "J"=> F.sector.energy
local notation "Ξ₀"=> firstProbe
local notation "Ξ₁"=> secondProbe

-- shapes of slot at center move v with first stress-neighbor measured; exterior spectator always origin.
def sightShape (r:ℝ)(v z:E4):= r • Points.cons (v+z) (atShape v)

def three (A A' B:S.Field 4)(x:Points 3) := S.useAt S x (Fin.cons ⟨4,B⟩ (Fin.cons ⟨4,A⟩ (fun _=>⟨4,A'⟩)))
def priceAt (r:ℝ) (K:Points 3→ℂ) (φ:E4→ℝ) (i:Axis) (v:E4) : ℂ :=
    ∫ y : E4, D (basis i) φ y • K (sightShape r v y)
local notation "σ"=> Finset.univ
variable (A : S.Field 4)
local notation "𝜏"=> three A A

lemma wing_price (hr:ℝ) {i:Axis} {v:E4} {K:Points 3→ℂ} {φ:E4→ℝ}
    (hw: tsupport (D (basis i) φ) ⊆ wing) : priceAt hr K φ i v = ∫ y : E4 in wing,D (basis i) φ y • K (sightShape hr v y) := by
    unfold priceAt; symm; apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht; rw [image_eq_zero_of_notMem_tsupport (fun H=> ht (hw H):t∉tsupport (D (basis i) φ)),zero_smul]
lemma price_scaling {r:ℝ}(hr:0<r)(K:Points 3→ℂ) (φ:E4→ℝ)(i:Axis)(v:E4)(hs:ContDiff ℝ ∞ φ):
    (∫ z:E4, D (basis i) (stretch r (seat v φ)) z • K (Points.cons z (r • atShape v))) = r^3 • priceAt r K φ i v := by
   let U:= D (basis i) (stretch r (seat v φ)); let P z:= U z • K (Points.cons z (r • atShape v));
   have he:=Measure.integral_comp_smul_of_nonneg volume P r (hR:=hr.le)
   have hk(z:E4) : P (r • (v+z)) = r⁻¹ • D (basis i) φ z • K (sightShape r v z):= by
       unfold P U; rw [D_stretch hr (seat_smooth v φ hs), seat_stretch i v z _ hs, mul_smul,← smul_cons]; rfl
   rw [show Module.finrank ℝ E4=4 from finrank_euclideanSpace_fin,
       ← integral_add_left_eq_self (μ:=volume) (fun x:E4=> P (r • x)) v] at he
   simp_rw [hk] at he; rw [integral_smul] at he; rw [priceAt]
   rw [←show (∫ z:E4,P z)=_ from rfl]
   apply smul_right_injective ℂ (inv_ne_zero (pow_ne_zero 4 hr.ne')); dsimp only; rw [← he,smul_smul]; congr 1; field_simp

lemma three_linear (A' B:S.Field 4)(x:Points 3)(u:ℝ):
    three A A' (u • B) x = u • three A A' B x := by unfold three; simp only [←front_eval,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
lemma price_linear {K:Points 3→ℂ} (r:ℝ)(u:ℝ)(χ:E4→ℝ)(i:Axis)(v:E4): priceAt r (u • K) χ i v=u • priceAt r K χ i v:=by
   simp_rw [priceAt, ← integral_smul, Pi.smul_apply]; congr with z; exact smul_comm ..
lemma price_add (r:ℝ) (s:E4→ℝ) {i:Axis} {v:E4} {K M:Points 3→ℂ}
    (h1 : Integrable fun y=> D (basis i) s y • K (sightShape r v y))
    (h2 : Integrable fun y=> D (basis i) s y • M (sightShape r v y)) :
    priceAt r (K + M) s i v=priceAt r K s i v + priceAt r M s i v:=by simp_rw [priceAt, Pi.add_apply,smul_add]; rw [integral_add h1 h2]
lemma price_sub (r:ℝ) (s:E4→ℝ) {i:Axis} {v:E4} {K M:Points 3→ℂ}
    (h1 : Integrable fun y=> D (basis i) s y • K (sightShape r v y))
    (h2 : Integrable fun y=> D (basis i) s y • M (sightShape r v y)) :
    priceAt r (K - M) s i v=priceAt r K s i v - priceAt r M s i v:=by simp_rw [priceAt, Pi.sub_apply,smul_sub]; rw [integral_sub h1 h2]
lemma price_int (r:ℝ) (s:E4→ℝ) {i:Axis} {v:E4} {K:Points 3→ℂ} (hr:0<r) (hv:1≤‖v‖) (hK:ContinuousOn K (conf 3))
    (hs:ContDiff ℝ ∞ s) (hS: tsupport (D (basis i) s) ⊆ wing) :
    Integrable fun y=> D (basis i) s y • K (sightShape r v y):=by
    have he : Continuous (D (basis i) s) := (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hV : Continuous (sightShape r v):=by
       unfold sightShape
       exact (continuous_cons_comp (x:=atShape v) v).const_smul r
    exact cutoff_integrable (wing_compact.of_isClosed_subset (isClosed_tsupport _) hS) he (fun y hy=>
      ((hK _ (smul_conf hr (wing_room3 hv (hS hy)))).continuousAt ((conf_open _).mem_nhds (smul_conf hr (wing_room3 hv (hS hy))))).comp (f:=sightShape r v) hV.continuousAt)
where
    continuous_cons_comp {x:Points 2}(v:E4): Continuous fun y:E4=> Points.cons (v+y) x:=by
       have h: Continuous fun z:E4=>Points.cons z x:=by rw [shifting_head]; fun_prop
       fun_prop
variable (r:ℝ){v:E4}
local notation "I"=> priceAt r
set_option maxHeartbeats 750000 in
lemma first_axis (hr:0<r)(hv:1≤‖v‖) : (∑ i:Axis, I (𝜏 (r^4 • J i 0)) Ξ₀ i v) = (-r) • D (basis 0) (fun z=>custom (atShape z) A A) (r • v):=by
    let K:= fun z=> custom (atShape z) A A; let L:= atShape v
    let x:=r • L; let χ:= stretch r (seat v Ξ₀)
    let q : Fin 1→ S.Tag:= fun _=>⟨4,A⟩
    have hx: x∈conf 2:= smul_conf hr (atRoom (norm_pos_iff.mp (by linarith)))
    have hx': x=atShape (r • v):= onShape v r
    have hs : shellGrad S J χ 0 x q A = D (basis 0) K (r • v):= by
       have he:= F.phase.transport.charges.translation hx q (window_stretch hr (first_window hv)) 0 4 A
       rw [he,hx']; exact (D_cons F.room.kernel.smooth _ F.phase.transport.derivatives A q (show atShape _∈_ from hx' ▸ hx) _).symm
    have he (i:Axis): r^ (3:ℕ) • I (𝜏 (J i 0)) Ξ₀ i v=∫ z:E4, D (basis i) χ z • 𝜏 (J i 0) (Points.cons z x):= (price_scaling hr _ _ i v first_smooth).symm
    have hK: shellGrad S J χ 0 x q A = -(r^3 • ∑ i:Axis, I (𝜏 (J i 0)) Ξ₀ i v):=by
       rw [shellGrad, Finset.smul_sum]; simp_rw [he,Complex.real_smul]; rfl
    have ht (i:Axis): (𝜏 (r^4 • J i 0))=r^4 • (𝜏 (J i 0)) := funext (fun z=> three_linear A ..)
    rw [← show _ = D _ _ _ from hs,hK]; simp_rw [ht,price_linear r,←Finset.smul_sum,neg_smul,smul_neg,neg_neg,smul_smul]; congr 1; ring

lemma second_axis (hr:0<r)(hv:1≤‖v‖) : (∑ i:Axis, I (𝜏 (r^4 • J i 1)) Ξ₁ i v)=0:=by
    let V:= fun _:E4=>basis 1; let x:= r • atShape v
    let χ:= stretch r (seat v Ξ₁); let L: E4→ E4:= fun y=> r⁻¹ • y
    have hc:HasCompactSupport Ξ₁ := wing_compact.of_isClosed_subset (isClosed_tsupport _) second_wing
    have hq:HasCompactSupport (seat v Ξ₁):= hc.comp_homeomorph (Homeomorph.subRight v)
    have hk:HasCompactSupport χ:=hq.comp_smul (inv_ne_zero hr.ne')
    have hl : ContDiff ℝ ∞ L:= by unfold L; fun_prop
    let q : Fin 2 → S.Tag:= Fin.cons (α:=fun _:Fin 2=>S.Tag) ⟨4,A⟩ (fun _=>⟨4,A⟩)
    have hχ : ContDiff ℝ ∞ χ:=(seat_smooth v _ second_smooth).comp hl
    have he:= cutoff_zero F.room.kernel.smooth _ F.phase.transport.derivatives _ F.phase.transport.conserved V
      (fun _=> contDiff_const) (killing_const _) x q _ hχ hk (fun z hz=> by
       have hs: L z∈ tsupport (seat v Ξ₁):= by by_contra H; exact (notMem_tsupport_iff_eventuallyEq.mpr ((notMem_tsupport_iff_eventuallyEq.mp H).comp_tendsto (g:=L) hl.continuous.continuousAt) : z∉ tsupport χ) hz
       have hv': r • L z=z:= smul_inv_smul₀ hr.ne' z; have hu:=smul_conf hr (second_room hv hs); rw [smul_cons,hv'] at hu; exact hu)
    have hl(i:Axis)(y:E4) : D (basis i) χ y • Work.A01.current J V x q i y = D (basis i) χ y • 𝜏 (J i 1) (Points.cons y x):= congr_arg (D (basis i) χ y • ·) (by
       change (∑ b:Axis,_) = _
       rw [Finset.sum_eq_single (1:Axis)]
       · unfold V; rw [basis_eq]; simp; rfl
       · intro b _ hb; unfold V; rw [basis_eq]; simp [hb]
       simp)
    change -(∑ i:Axis, ∫ y:E4, D (basis i) χ y • Work.A01.current J V x q i y)=0 at he
    simp_rw [hl,χ,x,price_scaling hr (three A A _) Ξ₁ _ v second_smooth, ← Finset.smul_sum] at he
    have ht (i:Axis): (𝜏 (r^4 • J i 1))=r^4 • (𝜏 (J i 1)) := funext (fun z=> three_linear A ..)
    simp_rw [ht,price_linear r,←Finset.smul_sum,(smul_eq_zero.mp (neg_eq_zero.mp he)).resolve_left (pow_ne_zero 3 hr.ne'), smul_zero]
end YM.FrontierTrace.Primary
