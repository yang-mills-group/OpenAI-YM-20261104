import YM.Comparison.Density.Mirrors.Ledger
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
import YM.Push.RELAY_DIFFERENCE.RawTop
/-!
# The analogous estimate for anchored kernels

When jets are controlled at fixed source roots (not just sums of
translations), no fourth difference is needed. Evaluate on group fields
of the actual step, through all indicated derivatives. Don't infer small
Fréchet norm from testing a projected basis. Compatible with complex
multimarker entries. Carry also exponent supports rooted at ANY of the
stated marker roots. Mask changes producing the aligned entry are separate.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Density.Mirrors.Anchor
open Function Lattice RG Wilson Filter WardBin.Lies AnalyticBridge.SectorAffine.Offset
open PhysicalNext.Repeat Transport MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} (B : BudgetPoint) (L : LinkTube G) (f : Config G n→ℂ)

-- Only used in evaluating a cylinder at the given regular address.
-- Not replacing the history's fields by a separately assembled good sector.
private def cut (X : Support n) (z : Site n→G.El) (U : Config G n) : Config G n := fun e =>
    if e.1∈X ∧ e.1+step e.2∈X then gauge z U e else 1
private def turning (X : Support n) (z : Site n→G.El) : Directions G n →L[ℝ] Directions G n :=
    ContinuousLinearMap.pi fun i=> if i.1∈X ∧ i.1+step i.2∈X then (G.adjoint (z i.1)).toContinuousLinearMap ∘L ContinuousLinearMap.proj i else 0

private lemma gauge_cut (X : Support n) (z : Site n→G.El) (U : Config G n) (v : Directions G n) :
    cut X z (increment U v)=increment (cut X z U) (turning X z v) := by
  funext i
  simp only [cut,turning,increment,ContinuousLinearMap.pi_apply]
  split; next h=>
    simp only [Lattice.gauge,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
    unfold increment; rw [show (G.adjoint (z i.1)).toContinuousLinearMap _ = G.adjoint (z i.1) (v i) from rfl, ProjectorNext.Equivariance.exp_adjoint]; group
  simp

private lemma cut_reads (X : Support n) (z : Site n→G.El) (U : Config G n) (hh : LocalOn X f) (h : GaugeInvariant f) : f (cut X z U)=f U :=
  (hh _ (gauge z U) fun _e a b=> if_pos (And.intro a b)).trans (h z U)

private lemma germ_cut (X : Support n) (z : Site n→G.El) (U : Config G n) (hh : LocalOn X f) (h : GaugeInvariant f) {m : ℕ}
    (hf : WardBin.Lies.Germ m f (cut X z U)) : WardBin.Lies.Germ m f U := by
  let V:= turning X z
  unfold WardBin.Lies.Germ
  rw [show (fun v=>f (increment U v))=((f ∘ increment (cut X z U))∘V) from funext fun v=>
    (cut_reads f X z _ hh h).symm.trans (congr_arg f (gauge_cut X z U v))]
  exact (show ContDiffAt ℝ m (f ∘ increment (cut X z U)) (V 0) by rw [map_zero]; exact hf).comp _ V.contDiff.contDiffAt

private lemma left_cut (X : Support n) (z : Site n→ G.El) (U : Config G n) (hh : LocalOn X f) (h : GaugeInvariant f) (l : List (Directions G n)) :
    leftDerivs f (l.map (turning X z)) (cut X z U)= leftDerivs f l U := by
  induction l generalizing U with
  | nil=> exact cut_reads f X z U hh h
  | cons v l ih=>
    have he t : t • (turning X z v) = (turning X z) (t • v):= (map_smul _ _ _).symm
    simp_rw [List.map_cons,leftDerivs, he,← gauge_cut,ih]

variable {o : Site n} {w d e : ℝ} {D s k m a : ℕ} {X : Support n}

def focus (D a : ℕ) (B : BudgetPoint) := (1+((D+a:ℕ):ℝ))^B.power


private lemma cut_to (U : Config G n) (hX : X⊆neighborhood k o) (h : Healthy B.threshold (neighborhood D o) U)
    (hd : k<D) (hR : Room B n L D w) : ∃ z : Site n→G.El,
      (∀ i, G.chord (cut X z U i)<L.radius) ∧ ‖logField (cut X z U)‖≤ w := by
  obtain ⟨z,hz⟩:= axial_to _ o D k _ hd hR.side h
  let V:= cut X z U
  have hv i : G.chord (V i)≤ axialCost B D := by
    unfold V cut; split
    next h=> exact hz _ ((neighborhood_iff ..).1 (hX h.1))
    rw [G.chord_one]; exact axial_nonneg ..
  have he i:= lt_of_le_of_lt (hv i) hR.core
  exact ⟨z,he,(pi_norm_le_iff_of_nonneg (B.threshold_pos.le.trans hR.budget)).2 fun i=>
    (L.log_size _ (he i)).trans ((mul_le_mul_of_nonneg_left (hv i) L.scale.le).trans hR.logs)⟩

lemma aligned (hX : X ⊆ neighborhood k o) (hk : k<D) (hR : Room B n L D w) (hm : B.order ≤ m) (hb : Measurable f) (h : LocalOn X f) (hg : GaugeInvariant f)
    (he : ∀ A : Directions G n, ‖A‖≤w → Through m (f∘increment 1) A d) : B.Regular (neighborhood D o) f := by
  have hp (V) (hu:Healthy B.threshold (neighborhood D o) V) : WardBin.Lies.Germ B.order f V := by
    obtain ⟨z,hz,hV⟩:= cut_to B L V hX hu hk hR
    exact germ_cut f X z _ h hg (germ_smooth f L _ hz B.order (through_le (he _ hV) hm).smooth)
  exact ⟨fun U V hc=> h _ _ (agrees_mono hc (Finset.coe_subset.mpr (hX.trans (neighborhood_mono hk.le)))),hb,hg,hp,
    fun V hu A l hl=> (hp V hu).has l A hl⟩

theorem pay (u : Site n) (ha : separation o u ≤ a) (hX : X⊆neighborhood k o) (hk : k < D)
    (hR : Room B n L D w) (hm : B.order ≤ m) (hs : s ≤ m) (hd : 0≤ d) (he : 0≤ e) (h : LocalOn X f) (hg : GaugeInvariant f)
    (hA : ∀ A : Directions G n, ‖A‖≤ w → Through m (f ∘ increment 1) A d) (hj : ∀ i<s, ‖iteratedFDeriv ℝ i (f∘ increment 1) 0‖≤e) :
    B.supBounds u (neighborhood D o) f (focus k a B^B.order*(groupPrice L B.order*(s*e+d*w^s))) := by
  let C:= groupPrice L B.order*(s*e+d*w^s)
  let q:=focus k a B
  have hq : 1≤q:= one_le_pow₀ (le_add_of_nonneg_right (Nat.cast_nonneg _))
  have hq' : 0<q:= zero_lt_one.trans_le hq
  have hw:=B.threshold_pos.trans_le hR.budget
  refine ⟨show 0≤ q^B.order*C from mul_nonneg (by positivity) (mul_nonneg (price_nonneg ..) (by positivity)),fun U hU l hl hD=>?_⟩
  obtain ⟨z,hV,hz⟩:= cut_to _ _ U hX hU hk hR
  let V := cut X z U
  let φ:=turning X z
  rw [← left_cut f X z U h hg]
  let y := l.map (fun A=> q⁻¹ • φ A)
  have hy : l.map (turning X z) = y.map (fun A=> q • A) := by
    unfold y; rw [List.map_map]; congr; ext i; simp [← mul_smul,hq'.ne',φ]
  rw [hy,Push.RelayDifference.left_dilate, List.length_map,norm_smul]
  have H (x) (hi : x∈ y) : ‖x‖ ≤ w:= by
    obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hi
    apply (pi_norm_le_iff_of_nonneg hw.le).2; intro i
    simp only [φ, turning, ContinuousLinearMap.pi_apply,Pi.smul_apply]
    split
    · rename_i he; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
      rw [norm_smul,Real.norm_of_nonneg (inv_pos.mpr hq'|>.le), show (G.adjoint (z i.1)).toContinuousLinearMap (j i)=G.adjoint (z i.1) (j i) from rfl,G.norm_adjoint]; apply (inv_mul_le_iff₀ hq').2
      refine (hD j hj i).trans (le_trans ?_ (mul_le_mul_of_nonneg_left hR.budget hq'.le)); rw [mul_comm q]; apply mul_le_mul_of_nonneg_left _ B.threshold_pos.le
      have hb : separation i.1 u ≤ k+a:= (separation_triangle i.1 o u).trans (Nat.add_le_add (by rw [separation_comm]; exact (neighborhood_iff ..).1 (hX he.1)) ha)
      unfold q focus; gcongr
    simpa using hw.le
  have hb:= transport f L w (cut X z U) hV hw hR.small hz m B.order s d e hs hm hd he hA hj y (by simpa [y] using hl) H
  change (_:ℝ) ≤ q^B.order*C
  rw [Real.norm_of_nonneg (pow_pos hq' _|>.le)]
  exact mul_le_mul (pow_le_pow_right₀ hq hl) hb (norm_nonneg _) (pow_nonneg hq'.le _)
end YM.Comparison.Density.Mirrors.Anchor
