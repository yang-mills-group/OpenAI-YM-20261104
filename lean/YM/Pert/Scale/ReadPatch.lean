import YM.Pert.Scale.Measure
/-! Position-tested raw data in the relative branch and their first scale derivative; no X-space positive-order precision claimed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace YM.Pert.Scale
open Function Filter Topology Set Spec RawLabels Extra.FD Maxwell Climb Position MeasureTheory Analysis Ward Next.UVStress
open scoped BigOperators ContDiff
variable {G : Gauge} {C : Family G} {I : Extraction.Order} {S : Table C.book} {n d : ℕ} {b : Final C I S} {X : Scaling S}
   {Q : Conditions C.labels d n} {φ : Ledger Q → Buffer C.labels d} (h : FirstExtension b X)
   (hq:CleanProfiles Q) (hl:Reports (chart Q) (white Q) 0 φ)
variable {m:ℕ} (R : Conditions C.labels d m)
def receiving (X : Scaling S) (φ : Ledger Q → Buffer C.labels d) k s := chart R (rolled R X k s, correction X φ k s)
def actualTest (X : Scaling S) (φ : Ledger Q → Buffer C.labels d) k s := R.chisels (fun i => Complex.re (∫ x : Points _, R.profiles i x * Ward.disc (fun j => (⟨d,positionScale X φ k s (R.columns i j)⟩:S.Tag)) ((X.r k*s) • x)))

private def zoomM {r : ℕ} (X : Scaling S) (k : ℕ) (v : ℝ) (x:Points r) :
     MultilinearMap ℂ (fun _ : Fin r => E C.labels d) ℂ :=
     (S.classMoment S (fun _=>d) ((X.r k*v) • x)).compLinearMap (fun _=> (X.U k d).toLinearMap)

include h
private lemma zoom_smooth {r : ℕ} (q : Fin r → E C.labels d) (k) {s:ℝ} (hs : 0<s) :
   ContinuousOn (fun x : Points r=>zoomM X k s x q) (conf _) := by
 have hh : Continuous (fun x:Points r=>(X.r k*s) • x) := ((X.r k * s) • ContinuousLinearMap.id ℝ (Points r)).continuous
 exact ((smoothDisc b.room.kernel.smooth (fun i=> (⟨d, X.U k d (q i)⟩:S.Tag))).continuousOn).comp hh.continuousOn (fun _=> slides (mul_pos (X.positive k) hs))
omit h in
private lemma cloud_zoom (i : Fin R.slots) (z : inklet R i) k s :
  cloud R X k s i z = ∫ x : Points _, R.profiles i x * zoomM X k s x (fromBasis R i z) := by
  unfold cloud fromBasis zoomM swivel
  simp only [mul_smul]; rfl

theorem receiver_grasp (hR : CleanProfiles R) {i k} {s : ℝ} (hs : 0<s) (q : Fin (R.arity i) → E C.labels d) :
   decode R (rolled R X k s) q = ∫ x : Points _,R.profiles i x * zoomM X k s x (fun i => gear C.labels d s (q i)) := by
   let M := fun x : Points (R.arity i) => (zoomM (d:=d) X k s x).compLinearMap (fun _=>gear C.labels d s)
   refine decode_profile R _ hR M (fun q => zoom_smooth h _ _ hs) (fun z=> ?_) q
   change decode R (cloud R X k s) (fun i=>motor C.labels _ (baring C.labels d (z i))) = _
   rw [decode_profile R (cloud R X k s) hR (zoomM (d:=d) (r:=R.arity i) X k s) (fun q=>zoom_smooth h q k hs) (fun _=>cloud_zoom R i _ k s)]
   apply integral_congr_ae
   apply Eventually.of_forall
   intro x; congr 1
   unfold M; simp only [MultilinearMap.compLinearMap_apply,Function.comp_apply,Prod.fst,Prod.snd,motor_bank,fromBasis]

lemma actual_receipt (hR : CleanProfiles R) {k s} (hs : Cleared X φ k s) : receiving R X φ k s = actualTest R X φ k s := by
   apply congrArg R.chisels
   funext i; apply congrArg Complex.re
   simp_rw [pos_eq X hs]
   exact receiver_grasp h R hR hs.1 _

include hq hl
lemma actual_near (hR : CleanProfiles R) {s : ℝ} (hs : 0<s) :
    ∀ᶠ k : ℕ in atTop, receiving R X φ k =ᶠ[𝓝 s] actualTest R X φ k := by
  obtain ⟨u,hu,w,hw,he⟩ := eventually_prod_iff.mp (clearance h hq hl hs)
  exact hu.mono (fun k hk=> hw.mono (fun _ ht=>actual_receipt h R hR (he hk ht).1))
theorem actual_fixed {s : ℝ} (hs : 0<s) :
    ∀ᶠ i : ℕ×ℝ in atTop ×ˢ 𝓝 s, actualTest Q X φ i.1 i.2 = chart Q (white Q,0) :=
  (clearance h hq hl hs).mono (fun i hi=> (actual_receipt h Q hq hi.1).symm.trans hi.2)

theorem response_limit (hR : CleanProfiles R) {s : ℝ} (hs : 0<s) :
   Tendsto (fun i : ℕ×ℝ => actualTest R X φ i.1 i.2) (atTop ×ˢ 𝓝 s) (𝓝 (chart R (white R,0))) :=
     (((chart_diff R).continuous.tendsto _).comp ((rolling R hR h hs).prodMk_nhds (corrects h hq hl hs))).congr' ((clearance h hq hl hs).mono fun i hi=>actual_receipt h R hR hi.1)

private lemma response_slope (hR : CleanProfiles R) s k :
   ∀ ha : DifferentiableAt ℝ (rolled R X k) s, ∀ hb : DifferentiableAt ℝ (correction X φ k) s,
   deriv (receiving R X φ k) s = fderiv ℝ (chart R) (rolled R X k s,correction X φ k s) (deriv (rolled R X k) s,deriv (correction X φ k) s) := by
     intro ha hb
     exact ((chart_diff R).differentiable (by decide) |>.differentiableAt.hasFDerivAt.comp_hasDerivAt s ((DifferentiableAt.hasDerivAt (f:=rolled R X k) (𝕜:=ℝ) ha).prodMk (DifferentiableAt.hasDerivAt (f:=correction X φ k) (𝕜:=ℝ) hb))).deriv

theorem response_turns (hR : CleanProfiles R) {s : ℝ} (hs : 0<s) :
   Tendsto (fun k => deriv (actualTest R X φ k) s) atTop (𝓝 0) := by
  let z k := (rolled R X k s, correction X φ k s)
  have hz : Tendsto z atTop (𝓝 (white R,0)) := (fixed_stitch (rolling R hR h hs)).prodMk_nhds (fixed_stitch (corrects h hq hl hs))
  let p k := (deriv (rolled R X k) s,deriv (correction X φ k) s)
  let P := ((0:Ledger R),(0:Buffer C.labels d))
  have hp : Tendsto p atTop (𝓝 P) := (rolled_deriv R hR h hs).1.prodMk_nhds (correction_deriv h hq hl hs).2
  let ht := passage (chart R) z p (white R,0) P hz hp (chart_diff R).contDiffAt
  dsimp only [P] at ht
  change Tendsto (fun k => fderiv ℝ (chart R) (z k) (p k)) atTop (𝓝 ((fderiv ℝ (chart R) (white R,0)) (0:Ledger R × Buffer C.labels d))) at ht
  rw [map_zero] at ht
  refine ht.congr' ?_
  filter_upwards [actual_near h hq hl R hR hs,(correction_deriv h hq hl hs).1] with k hk he
  exact (response_slope h hq hl R hR _ _ ((rolled_deriv R hR h hs).2 k) he).symm.trans hk.deriv_eq

end YM.Pert.Scale
