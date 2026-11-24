import YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalArms

/-! The connected original finite ensemble with the actual shared test and genuine deleted arms. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalRose
open Filter Function Set Finset MeasureTheory Spec Table Extraction Lattice Climb PhysMS RG17 RG
open PhysicalNext.Repeat.Legato Wilson Trace Metric Cells Push.GridApprox
open Maxwell XSpace XSpace.Normalize Trace.Pilot Next.UVStress
open WilsonPositionThermometerCapStation WilsonPositionCapTransport
open WilsonPositionProgramTrialPublicJointPivotOriginalArms (Ready source raw cutoff)
open WilsonPositionProgramTrialPublicJointPivotEvidence (atHome old)
open WilsonPositionThermometerConnected (value)
open WilsonSeparatedOriginalThermometerCells (positions placed weight)
open scoped Classical Topology BigOperators
variable {G:Gauge} {R:Run G} {o:Extraction.Order} {S:Table R.family.book}
variable (F:Final R.family o S) (J:ℝ→tower S) {l:Ultrafilter (ℕ×ℕ)} {D:ℕ}
variable {H:(Bel R.family.book).Hierarchy} {n:ℕ}

def site (A:Group R.family D) (d:Fin (D+1)) (p:Fin 3→Sec G d) (z:ℕ×ℕ)
    (y:Fin 3→Site (R.family.side z.1 z.2)) (s:Finset (Fin 3)) : ℂ :=
  R.family.ensemble (N:=z.1) (p:=z.2) (fun _:Fin 3=>d.val) y
    (fun i=>source A d (Rose.missing p s i) z)

def posted (A:Group R.family D) (d:Fin (D+1)) (p:Fin 3→Sec G d)
    (r:ℝ) (z:ℕ×ℕ) (x:Points 3) : ℂ :=
  value (site A d p z (positions (R:=R) r z x))

def signed (A:Group R.family D) (d:Fin (D+1)) (p:Fin 3→Sec G d) (φ:Test 3)
    (r:ℝ) (z:ℕ×ℕ) : ℂ := φ.applyTo (posted A d p r z)

theorem joint (A:Group R.family D) (d:Fin (D+1)) (p:Fin 3→Sec G d) (φ:Test 3)
    (r:ℝ) (z:ℕ×ℕ) :
    signed A d p φ r z=∑y,weight φ (positions (R:=R) r z) y*value (site A d p z y) :=
  WilsonSeparatedOriginalThermometerCells.tested φ _ (placed (R:=R) r z) (fun y=>value (site A d p z y))

theorem cuts (simple:G.Simple) (prior:(l:Filter _)≤o.fuse) {r:ℝ} (rp:0<r)
    (A:Group R.family D) (ready:Ready (o:=o) (l:=l) (H:=H) A (J r) r)
    (d:Fin (D+1)) (p:Fin 3→Sec G d) {K:Set (Points 3)} (hk:IsCompact K) (apart:K⊆conf 3)
    {e:ℝ} (ep:0<e) :
    ∀ᶠ z:ℕ×ℕ in (l:Filter _),∀x∈K,‖posted A d p r z x-
      value (fun s=>atHome F J d r x (Rose.missing p s))‖<e := by
  let target (x:Points 3) (s:Finset (Fin 3)) := atHome F J d r x (Rose.missing p s)
  have cont : ContinuousOn target K := by
    apply continuousOn_pi.mpr
    intro s
    exact (WilsonPositionPrescribedScreen.smooth F J (Rose.missing p s) rp).mono apart
  let V := target '' K
  have vc : IsCompact V := hk.image_of_continuousOn cont
  let W := cthickening (1:ℝ) V
  have wc : IsCompact W := vc.cthickening
  obtain ⟨t,tp,move⟩ := Metric.uniformContinuousOn_iff.mp
    (wc.uniformContinuousOn_of_continuous WilsonPositionThermometerConnected.continuous_value.continuousOn) e ep
  have pos : 0 < min 1 t := lt_min one_pos tp
  have close := eventually_all.mpr (fun s:Finset (Fin 3)=>cutoff F J simple prior rp A ready
    (fun _:Fin 3=>d) (Rose.missing p s) hk apart pos)
  filter_upwards [close] with z paid x hx
  let y := site A d p z (positions (R:=R) r z x)
  have near : dist y (target x) < min 1 t := (dist_pi_lt_iff pos).mpr (fun s=>by
    rw [dist_eq_norm]
    exact paid s x hx)
  have here : target x∈V := ⟨x,hx,rfl⟩
  have movein : y∈W := mem_cthickening_of_dist_le y (target x) 1 V here (near.le.trans (min_le_left _ _))
  change ‖value y-value (target x)‖<e
  simpa only [dist_eq_norm] using
    move y movein (target x) (self_subset_cthickening V here) (near.trans_le (min_le_right _ _))

theorem averaged {ι:Type*} (U:Filter ι) (φ:Test n) (X:ι→Points n→ℂ) (T:Points n→ℂ)
    (meas:∀i,Measurable (X i)) (smooth:ContinuousOn T (conf n))
    (close:∀e:ℝ,0<e→∀ᶠi in U,∀x∈tsupport φ,‖X i x-T x‖<e) :
    Tendsto (fun i=>φ.applyTo (X i)) U (𝓝 (φ.applyTo T)) := by
  apply Metric.tendsto_nhds.mpr
  intro e ep
  let M := ∫x:Points n,‖φ x‖
  have mp : 0≤M := integral_nonneg fun _=>norm_nonneg _
  let t := (e/2)/(M+1)
  have tp : 0<t := div_pos (half_pos ep) (by linarith)
  have pay : M*t<e := by
    calc M*t ≤ (M+1)*t := mul_le_mul_of_nonneg_right (by linarith) tp.le
         _ = e/2 := by dsimp only [t];field_simp [show M+1≠0 by linarith]
         _ < e := half_lt_self ep
  have gi : Integrable (fun x:Points n=>φ x) := φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have oi := φ.smearing smooth
  filter_upwards [close t tp] with i ready
  have am := (φ.continuous.measurable.mul (meas i)).aestronglyMeasurable (μ:=volume)
  have point (x:Points n) : ‖φ x*X i x-φ x*T x‖≤‖φ x‖*t := by
    by_cases hz:φ x=0
    · simp [hz]
    · rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left (ready x (subset_closure hz)).le (norm_nonneg _)
  have di := (gi.norm.mul_const t).mono' (am.sub oi.aestronglyMeasurable) (Eventually.of_forall point)
  have vi : Integrable (fun x:Points n=>φ x*X i x) :=
    (di.add oi).congr (Eventually.of_forall fun _=>sub_add_cancel _ _)
  rw [dist_eq_norm]
  change ‖(∫x,φ x*X i x)-(∫x,φ x*T x)‖<e
  rw [←integral_sub vi oi]
  apply lt_of_le_of_lt (norm_integral_le_of_norm_le (gi.norm.mul_const t) (Eventually.of_forall point))
  rw [integral_mul_const]
  exact pay

theorem original (simple:G.Simple) (prior:(l:Filter _)≤o.fuse) {r:ℝ} (rp:0<r)
    (A:Group R.family D) (ready:Ready (o:=o) (l:=l) (H:=H) A (J r) r)
    (d:Fin (D+1)) (p:Fin 3→Sec G d) (φ:Test 3) :
    Tendsto (signed A d p φ r) (l:Filter _) (𝓝 (old F J d φ rp p)) := by
  apply averaged (l:Filter _) φ (posted A d p r)
    (fun x=>value (fun s=>atHome F J d r x (Rose.missing p s)))
  · intro z
    exact (measurable_of_finite (fun y=>value (site A d p z y))).comp (placed (R:=R) r z)
  · apply WilsonPositionThermometerConnected.continuous_value.comp_continuousOn
    apply continuousOn_pi.mpr
    intro s
    exact WilsonPositionPrescribedScreen.smooth F J (Rose.missing p s) rp
  · intro e ep
    exact cuts F J simple prior rp A ready d p φ.hasCompactSupport φ.tsupport_subset ep

end YM.Integration.WilsonPositionProgramTrialPublicJointPivotOriginalRose
