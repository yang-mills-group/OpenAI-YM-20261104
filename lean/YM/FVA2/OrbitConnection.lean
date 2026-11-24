import YM.FVA2.ReindexLaplace
import YM.FVA2.FpSection
import YM.PertExtension.OrbCovariance

/-!
# FP-to-RG10 gauge bridge (independent of desired MS alignment)

Exact, not an asymptotic-in-volume statement. All tree geometry and
energies in this module are those of `PertExtension.Orb`, i.e. the printed
inversion quotient geometry. Do NOT wrap the *action* at a different period
when using these claims. No smoothness outside the slice germs is needed here.
For actual-integral interpretations (with finite tags) see e.g. `Orb.PreTest` /
`BlockGauge` hypotheses also.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wilson
open Lattice Gauge FormalOPE.RG10 FormalOPE.RG10.BlockGauge TreeBasis SectionBasis
open PertExtension PertExtension.Series PertExtension.Orb PertExtension.Chart GermLaplace
open Function Finset Filter Set Metric MeasureTheory Precision Inherit Push.Loops
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge}

abbrev Cone (G : Gauge) (n : Side) := TreeBasis.Links (OEdge n) G
abbrev Field (G : Gauge) (n : Side) := Free (staple n) G
abbrev GaugeSlice (G : Gauge)(n:Side) := SectionBasis (rim n) (staple n) G

abbrev budget (n : Side) : (staple n).Bulk ≃ Orb.Cotree n := Equiv.subtypeEquiv (Equiv.refl _) (fun i=> not_congr (same_staple i))

def accountBasis (G : Gauge)(n : Side) : Field G n ≃L[ℝ] Orb.Dir G n :=
 (LinearEquiv.piCongrLeft ℝ (fun _ => G.Color) (budget n)).toContinuousLinearEquiv
lemma accountMeasure (G:Gauge)(n:Side): MeasurePreserving (accountBasis G n)
     (tangent G (staple n).Bulk) (tangent G (Orb.Cotree n)) :=
 measurePreserving_piCongrLeft (fun _ : Orb.Cotree n => (volume : Measure G.Color)) (budget n)
lemma accountPoint (u:Field G n)(i:(staple n).Bulk): accountBasis G n u (budget n i)=u i:= Equiv.piCongrLeft_apply_apply (fun _=>G.Color) (budget n) u i

def assemble (G:Gauge)(n:Side) (u:Cone G n) := liftLinks (expLinks G (OEdge n) u)
lemma assembly (u:Field G n):
    assemble G n (enter G (staple n) u)=representative (accountBasis G n u) := by
  unfold representative assemble; apply congr_arg liftLinks; ext1 i; by_cases h:(staple n).Branch i
  · simp only [splitLink, entry_exp, Loom.Truss.board,Loom.Truss.stitch, dif_pos h,dif_pos ((same_staple i).mp h)]; rfl
  simp only [splitLink, entry_exp, Loom.Truss.board,Loom.Truss.stitch,dif_neg h, dif_neg ((same_staple i).not.mp h)];
  change G.lieExp _ = G.lieExp _; exact congr_arg _ (accountPoint u ⟨i,h⟩).symm

def pricing (G : Gauge)(n : Side) : Cone G n → ℝ := fun u => _root_.YM.Wilson.energy (assemble G n u) / 2

def treeS (G:Gauge)(n : Side) := pricing G n ∘ enter G (staple n)
theorem exactly (G:Gauge)(n:Side) : treeS G n= Orb.fiscal ∘ accountBasis G n:= funext fun u => congr_arg (fun a=>_root_.YM.Wilson.energy a / 2) (assembly u)

lemma descends (p : Vertex n → G.El) (U:LinkFrame G n):
     liftLinks ((rim n).spin p U)= Lattice.gauge (p ∘ track) (liftLinks U) := by
   rw [spin_agrees]
   exact funext fun i=> (Orb.path_law _ _ (track_even p) i).symm

lemma treeS_hot (G:Gauge)(n:Side) : ContDiffAt ℝ ω (treeS G n) 0:= by rw [exactly]; exact Orb.fiscal_smooth.contDiffAt.comp _ (accountBasis G n).contDiff.contDiffAt
lemma aptitude (G:Gauge)(n:Side): Series.Radial.Stationary (treeS G n) := by
   refine Inherit.stable (treeS_hot G n) ?_ (fun x=> div_nonneg (_root_.YM.Wilson.energy_nonneg (assemble G n (enter G (staple n) x))) (by norm_num))
   rw [exactly,Function.comp_apply,map_zero,Orb.fiscal_zero]
lemma quotient_gap (G:Gauge)(hn:_root_.Even n.val): Gap (treeS G n):= by
  rw [exactly]; apply Radial.quadratic_min _; intro v hx
  obtain ⟨c,hc,h⟩:= Orb.coercion (G:=G) hn
  let Q:= accountBasis G n; have hv: 0<‖Q v‖:= norm_pos_iff.mpr (by intro he; exact hx (Q.injective (by rw [map_zero]; exact he)))
  change 0 < Radial.jet (Orb.fiscal ∘ Q.toContinuousLinearMap) 2 v; rw [jet_pull (m:= Q.toContinuousLinearMap) _ (Orb.fiscal_smooth.of_le le_top).contDiffAt v 2]; exact lt_of_lt_of_le (mul_pos hc (pow_pos hv _)) (h _)

-- Invariance + exact pullback of the observable. Note uses *any* even gauges; root holds.
variable (Z: GaugeSlice G n)
abbrev Observable (G:Gauge)(n:Side):= _root_.YM.Wilson.Config G n → ℝ
abbrev Physical (O: Wilson.Observable G n): Prop:= ∀ (p:Vertex n→G.El), p (rim n).origin=1 → ∀ u:LinkFrame G n,O (Orb.liftLinks ((rim n).spin p u))=O (Orb.liftLinks u)
namespace Physical
lemma one (G:Gauge)(n:Side): Physical (1:Wilson.Observable G n) := fun _ _ _=> rfl
lemma energy (G:Gauge)(n:Side): Physical (_root_.YM.Wilson.energy (G:=G) (n:=n)) := by
      intro p _ u; rw [descends]; exact _root_.YM.Wilson.energy_gauge ..
end Physical
variable {O:Wilson.Observable G n}

def WilsonPull (Z : GaugeSlice G n) := pricing G n ∘ Z.L
def slice (A:Wilson.Observable G n) := (A ∘ assemble G n) ∘ Z.L
def treed (A:Wilson.Observable G n) := (A ∘ assemble G n) ∘ enter G (staple n)
lemma germ_eq (h: Physical O): slice Z O =ᶠ[𝓝 0] (treed O) ∘ Z.changeChart:= by
  have hA: Tendsto Z.L (𝓝 0) (𝓝 0):= by simpa using Z.L.continuous_of_finiteDimensional.tendsto 0
  filter_upwards [hA.eventually (fixed_eventual G (staple n))] with x hx
  change O (Orb.liftLinks (expLinks G _ (Z.L x)))=O (Orb.liftLinks (expLinks G _ _))
  exact (h _ ((staple n).frame_root _) _).symm.trans (congr_arg (fun u=> O (Orb.liftLinks u)) hx)
lemma price_eq : WilsonPull Z =ᶠ[𝓝 0] (treeS G n) ∘ Z.changeChart := (germ_eq Z (Physical.energy G n)).mono fun _ h=> congr_arg (·/2) h

lemma pull_hot : ContDiffAt ℝ ω (WilsonPull Z) 0:= ( (show ContDiffAt ℝ ω (treeS G n) (Z.changeChart 0) from (by rw [Z.change_zero]; exact treeS_hot ..)).comp _ (Z.change_hot)).congr_of_eventuallyEq (price_eq Z)

lemma pull_stable : Series.Radial.Stationary (WilsonPull Z) := changed_stat _ (Z.change_hot) (Z.change_zero) (aptitude G n) (treeS_hot G n) (price_eq Z)
lemma pull_quad : Series.Radial.jet (WilsonPull Z) 2=Series.Radial.jet (treeS G n) 2 := pulled_cost _ (Z.change_hot) (Z.change_zero) Z.solve_one (aptitude G n) (treeS_hot G n) (price_eq Z)
lemma pull_gap (he:_root_.Even n.val) : Gap (WilsonPull Z) := by unfold Gap;rw [pull_quad]; exact quotient_gap G he

lemma observe_tree (O:Wilson.Observable G n) : treed O = (restrictedO O ∘ expLinks G (Orb.Cotree n)) ∘ accountBasis G n := funext fun u=> congr_arg O (assembly u)

def Honest (O:Wilson.Observable G n) := ContDiffAt ℝ ω (treed O) 0
lemma one_honest : Honest (1:Wilson.Observable G n):= contDiffAt_const

def sliceK (U:ChartRatio G) (O : Wilson.Observable G n) : Field G n→ℝ:= fun x=> slice Z O x * (density (OEdge n) U (Z.L x)* Z.fpdet x)
lemma slice_hot (h:Physical O)(he: Honest O) : ContDiffAt ℝ ω (slice Z O) 0:= ((show ContDiffAt ℝ ω (treed O) (Z.changeChart 0) from (by rw [Z.change_zero]; exact he)).comp _ Z.change_hot).congr_of_eventuallyEq (germ_eq Z h)
lemma sliceK_hot (U:ChartRatio G)(hp:LocalRatio U)(h:Physical O)(he:Honest O): ContDiffAt ℝ ω (sliceK Z U O) 0:= by refine (slice_hot Z h he).mul (( ContDiffAt.comp (g:=density (OEdge n) U) (f:=Z.L.toContinuousLinearMap) _ ?_ Z.L.toContinuousLinearMap.contDiff.contDiffAt).mul Z.fp_analytic); rw [map_zero]; exact density_hot U hp

def sliceRows (U:ChartRatio G) (O:Wilson.Observable G n):= PowerSeries.mk (Radial.moment (tangent G (staple n).Bulk) (sliceK Z U O) (WilsonPull Z)) -- moment namespace


lemma to_tree (hn:_root_.Even n.val)(U:ChartRatio G)(hp:LocalRatio U)(h:Physical O)(he: Honest O) :
   Radial.moment (tangent G (staple n).Bulk) (treed O * density (staple n).Bulk U) (treeS G n)= Radial.moment (tangent G (staple n).Bulk) (sliceK Z U O) (WilsonPull Z):= by
  refine powerSeries_gauge _ _ Z.change_hot Z.change_zero Z.solve_one (aptitude G n) (quotient_gap G hn) (treeS_hot G n) (show ContDiffAt ℝ ω (treed O * density (staple n).Bulk U) 0 from ContDiffAt.mul he (density_hot U hp)) (sliceK_hot Z U hp h he) (price_eq Z) ?_
  filter_upwards [Z.fp_identification U hp, germ_eq Z h] with x hx h; unfold sliceK; rw [h,hx]; exact (mul_assoc ..).symm

lemma tree_to_orb (U:ChartRatio G)(hp: LocalRatio U) (he: Honest O) :
  rowsWith U (restrictedO O)= (U.scale ^ Fintype.card (staple n).Bulk) • Radial.moment (tangent G (staple n).Bulk) (treed O *density (staple n).Bulk U) (treeS G n):= by
  let μ:= tangent G (Orb.Cotree n); let ν:= tangent G (staple n).Bulk
  let K:= accountingWith U (restrictedO O); let H := accountBasis G n
  let F:= treeS G n; let b:= U.scale ^ Fintype.card (staple n).Bulk; let V:= treed O*density (staple n).Bulk U
  have hk : ContDiffAt ℝ ω K 0:= by
     have ha: treed O = (( restrictedO O) ∘ expLinks G (Orb.Cotree n)) ∘ H:= observe_tree _
     let f := restrictedO O∘ expLinks G (Orb.Cotree n); have he': ContDiffAt ℝ ω (treed O) 0 := he
     refine (Ratio.jacobian_smooth hp).mul (g:=f) ?_; rw [show f= treed O ∘ H.symm from funext fun i=>by rw [Function.comp_apply, show treed O _= f (H _) from congr_fun ha _, H.apply_symm_apply]]
     exact ContDiffAt.comp (f:=H.symm) 0 (by rw [map_zero]; exact he') H.symm.contDiff.contDiffAt
  change Radial.moment μ K fiscal= _
  rw [moment_reindex μ H ν (accountMeasure G n) (hk.of_le le_top) (fiscal_smooth.contDiffAt.of_le le_top), show Orb.fiscal ∘ H= _ from (exactly G n).symm]; change Radial.moment ν (K∘ H) F= b • Radial.moment ν V F; rw [← moment_scale _ b F (K:=V) (ContDiffAt.mul (show ContDiffAt ℝ ∞ (treed O) 0 from ContDiffAt.of_le he le_top) ((density_hot U hp).of_le le_top))];
  apply local_moments _ _ ν (Filter.EventuallyEq.refl _ _); filter_upwards [(Filter.eventually_all.mpr fun i=>(continuous_apply i).continuousAt (x:=(0:Field G n))|>.eventually (Metric.ball_mem_nhds (0:G.Color) hp.patch))] with x hx
  have hx':jacobian U (H x)=b*density (staple n).Bulk U x:= by
      unfold jacobian; rw [← Equiv.prod_comp (budget n) (fun i:Orb.Cotree n=>fee U (H x i)), show b = ∏ _i:(staple n).Bulk, U.scale from (by simp [b]), density,← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun i _=>?_ ; unfold fee H; rw [accountPoint]; exact max_eq_left (mul_pos hp.scale (hp.pos _ (hx i))).le
  change jacobian U (H x) * restrictedO O (expLinks G _ (H x))=b*(treed O x * _); rw [hx',show treed O x=restrictedO O (expLinks G _ (H x)) from congr_fun (observe_tree O) x]; ring

theorem countingConvention (hn:_root_.Even n.val)(U:ChartRatio G)(hp:LocalRatio U)(h:Physical O)(he: Honest O) :
  PowerSeries.mk (rowsWith U (restrictedO O)) = PowerSeries.C (U.scale ^ Fintype.card (staple n).Bulk) * sliceRows Z U O:= by
   rw [tree_to_orb U hp he, to_tree Z hn U hp h he]; apply PowerSeries.ext; intro n; rw [PowerSeries.coeff_C_mul, sliceRows,PowerSeries.coeff_mk,PowerSeries.coeff_mk]; rfl

lemma one_core (hn:_root_.Even n.val)(U:ChartRatio G)(hp:LocalRatio U):
    PowerSeries.constantCoeff (sliceRows Z U 1) ≠ 0 := by
  have ht: PowerSeries.constantCoeff (PowerSeries.mk (rowsWith (n:=n) U 1))≠0:=by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; exact (pivot hn hp).ne'
  rw [show (1:Orb.Observable G n)= restrictedO (1:Wilson.Observable G n) from rfl,countingConvention Z hn U hp (Physical.one G n) one_honest,map_mul] at ht; exact right_ne_zero_of_mul ht

/-- Our finite-regulator Landau/linear FP interpretation of the same physical coefficients
 (take `tray` as normalized ratio unless implementing a different chart-ratio provider).
 Includes one unmarked-vacuum-series division at the top regulator; the earlier RG open-step
 conditional denominator belongs to `OpenSlots.Broadcast`, not to this `sliceEval`. -/
def sliceEval (U:ChartRatio G)(O:Wilson.Observable G n):= sliceRows Z U O * (sliceRows Z U 1)⁻¹

private lemma det_divide {f g : ℕ→ℝ}{y x z:PowerSeries ℝ}
    (h0:PowerSeries.constantCoeff y≠0)(hp:g 0≠0) (hx:PowerSeries.mk f=z*x)(hy:PowerSeries.mk g=z*y):
    PowerSeries.mk (Tested.divide f g) = x*y⁻¹:= by
   have ht: PowerSeries.constantCoeff (PowerSeries.mk g)≠0:= by rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; exact hp
   rw [(show PowerSeries.mk (Tested.divide f g)=PowerSeries.mk f * (PowerSeries.mk g)⁻¹ from PowerSeries.ext fun n=> PowerSeries.coeff_mk n (Tested.divide f g))]; symm; apply (PowerSeries.eq_mul_inv_iff_mul_eq ht).2; rw [hx,hy]; rw [show x*y⁻¹*(z*y)= (z*x)*(y*y⁻¹) from (by ring),PowerSeries.mul_inv_cancel y h0,mul_one]
theorem tree_identity (hn:_root_.Even n.val)(U:ChartRatio G)(hp:LocalRatio U)(h:Physical O)(he: Honest O) :
    PowerSeries.mk (diagonalWith U (restrictedO O))=sliceEval Z U O := by
    unfold diagonalWith sliceEval; apply det_divide (z:= PowerSeries.C (U.scale ^ Fintype.card (staple n).Bulk)) (one_core Z hn U hp) (pivot hn hp).ne' (countingConvention Z hn U hp h he) ; rw [show (1:Orb.Observable G n)=restrictedO (1:Wilson.Observable G n) from rfl]; exact countingConvention Z hn U hp (Physical.one G n) one_honest
end YM.FVA2.Wilson
