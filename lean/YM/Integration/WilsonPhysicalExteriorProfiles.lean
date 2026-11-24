import YM.Integration.WilsonPhysicalExteriorFrame
import YM.PhysMS.Frame.Phases
import YM.OPE.Measuring.Grams

/-! Smooth compact exterior measurements on the original extraction.  A finite list of
joint tests separates the entire horizon in every phase, at every sufficiently small outer
radius. Its labels belong to the very same reference tower as the near-scale field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorProfiles
open Function Filter Set MeasureTheory Spec Climb OPE OPE.Orbits PhysMS Trace.Pilot
open Next.UVStress Ward Pert.Position Labels
open scoped Topology BigOperators Classical ContDiff

variable {G : Gauge} {C : Family G} {q : Extraction.Order} {S : Table C.book}

private def form (J : ℝ → tower S) (T : Table C.book) (m : MeterTest (Bel C.book))
    (d : ℕ) (r : ℝ) (x : Points (m.n+1)) : E C.labels d →ₗ[ℂ] ℂ :=
  (T.injectFront (fun i => ⟨(m.q i).1,S.representative _ (J r _ (m.q i).2)⟩)
    (r • x) d).comp ((S.representative d).comp (J r d).toLinearMap)

private theorem form_original (F : Final C q S) (J : ℝ → tower S) (p : Viewers F)
    (m : MeterTest (Bel C.book)) (d : ℕ) (v : E C.labels d) (r : ℝ) (x : Points (m.n+1)) :
    form J (spectator F p) m d r x v =
      measured F p (J r) (d:=fun i => (m.headTest d v i).1)
        (fun i => (m.headTest d v i).2) r x := by
  let w (i : Fin (m.n+1)) := m.headTest d v i
  change (spectator F p).read (r • x)
    (Fin.cons (⟨d,S.representative _ (J r d v)⟩ : C.book.Token)
     (fun i => ⟨(m.q i).1,S.representative _ (J r _ (m.q i).2)⟩)) =
    (spectator F p).read (r • x) (fun i => ⟨(w i).1,S.representative _ (J r _ (w i).2)⟩)
  apply congrArg ((spectator F p).read (r • x))
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

private theorem regular (F : Final C q S) (J : ℝ → tower S) (p : Viewers F)
    (m : MeterTest (Bel C.book)) (d : ℕ) (v : E C.labels d) (r : ℝ) (hr : 0<r) :
    ContinuousOn (fun x => form J (spectator F p) m d r x v) (conf _) := by
  simp_rw [form_original F J p m d v r]
  let z (i : Fin (m.n+1)) : S.Tag := ⟨(m.headTest d v i).1,J r _ (m.headTest d v i).2⟩
  intro x hx
  exact (((S.class_smooth (spectator F p) (spectate F p).smooth z).contDiffAt
    ((conf_open _).mem_nhds (Work.A05.smul_conf hr hx))).continuousAt.comp
    (continuousAt_id.const_smul r)).continuousWithinAt

/-- One genuine jointly smeared signed correlation; the exterior may have any finite arity. -/
def reading (F : Final C q S) (J : ℝ → tower S) (p : Viewers F)
    (m : MeterTest (Bel C.book)) (d : ℕ) (r : ℝ) : E C.labels d →ₗ[ℂ] ℂ :=
  if hr : 0<r then
    { toFun := fun v => m.t.applyTo fun x => form J (spectator F p) m d r x v
      map_add' := by
        intro a b
        simp only [map_add]
        exact test_add _ _ (regular F J p m d a r hr) (regular F J p m d b r hr) m.t
      map_smul' := by
        intro c v
        simp only [map_smul]
        exact test_smul _ c _ }
  else 0

theorem original (F : Final C q S) (J : ℝ → tower S) (p : Viewers F)
    (m : MeterTest (Bel C.book)) (d : ℕ) (r : ℝ) (hr : 0<r) (v : E C.labels d) :
    reading F J p m d r v = m.t.applyTo (measured F p (J r)
      (d:=fun i => (m.headTest d v i).1) (fun i => (m.headTest d v i).2) r) := by
  simp only [reading,dif_pos hr,LinearMap.coe_mk,AddHom.coe_mk,form_original]

private theorem weight {n : ℕ} (m : Test n) (k : Points n → ℂ) (B : ℝ)
    (h : ∀ x∈tsupport m, ‖k x‖ ≤ B) :
    ‖m.applyTo k‖ ≤ (∫ x, ‖m x‖)*B := by
  unfold Test.applyTo
  rw [←integral_mul_const]
  apply norm_integral_le_of_norm_le
    ((m.continuous.norm.integrable_of_hasCompactSupport m.hasCompactSupport.norm).mul_const _)
    (ae_of_all _ fun x => ?_)
  by_cases hm : m x = 0
  · simp [hm]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (h x (subset_closure (mem_support.mpr hm))) (norm_nonneg _)

variable (F : Final C q S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → tower S) (H : Leading F J) (hG : G.Simple) (X : Scaling S) (hR : Foundation F R)

include R H hG X hR in
private theorem all_tested (m : MeterTest (Bel C.book)) (d : ℕ) (v : E C.labels d) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ r in trail, ∀ p : Viewers F,
      ‖reading F J p m d r v - m.zeroScale (Maxwell.Free.hierarchy C.labels).smooth d v‖ < ε := by
  let w := m.headTest d v
  let vs : MaxwellSlots C (fun i => (w i).1) := fun i => (w i).2
  let M := ∫ x, ‖m.t x‖
  have hM : 0≤M := integral_nonneg fun _ => norm_nonneg _
  let δ := ε/(M+1)
  have hδ : 0<δ := div_pos hε (by positivity)
  have hbuy : M*δ<ε := by
    calc M*δ < (M+1)*δ := mul_lt_mul_of_pos_right (by linarith) hδ
         _ = ε := by dsimp [δ]; field_simp
  have h := Frame.all_leading F R J H hG X hR 0 vs (tsupport m.t)
    m.t.hasCompactSupport m.t.tsupport_subset δ hδ
  filter_upwards [h,self_mem_nhdsWithin] with r hr hr₀ p
  have hr' : 0<r := hr₀
  let a := measured F p (J r) vs r
  let b := WickGoal (C:=C) vs
  have hb : ContinuousOn b (conf _) := fun x hx => (WickGoal_tied vs hx).continuousAt.continuousWithinAt
  have ha : ContinuousOn a (conf _) := by
    have hc := regular F J p m d v r hr'
    simpa only [form_original] using hc
  rw [original F J p m d r hr',MeterTest.zeroScale_eq]
  change ‖m.t.applyTo a-m.t.applyTo b‖<ε
  rw [←test_sub a b ha hb]
  apply (weight m.t (a-b) δ ?_).trans_lt hbuy
  intro x hx
  have h₀ := hr x hx p
  change ‖iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x‖<δ at h₀
  have he : iteratedFDeriv ℝ 0 a x-iteratedFDeriv ℝ 0 b x =
      iteratedFDeriv ℝ 0 (a-b) x := by ext z; simp
  rw [he,norm_iteratedFDeriv_zero] at h₀
  exact h₀.le

include R H hG X hR in
/-- The measured compact probes detect the true near-scale coefficient on every character.
The finite list and the constants precede the outer radius, its far/near ratio, and all fields. -/
theorem far (d : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (MeterTest (Bel C.book))) (K : ℝ), 1≤K ∧
      ∀ᶠ r in trail, ∀ t∈Ioc (0:ℝ) 1, ∀ p : Viewers F, ∀ v : S.Field d,
        ‖(J (t*r) d).symm v‖ ≤ K*t^(-(d:ℝ)-ε)*
          ‖fun i : s => reading F J p i.val d r ((J r d).symm v)‖ := by
  obtain ⟨K,hK,hf⟩ := WilsonPhysicalExteriorFrame.between F d J H ε hε
  obtain ⟨s,hs⟩ := MeterTest.detects (Bel C.book) (Maxwell.Free.hierarchy C.labels) d
  let A (u : ℝ × Viewers F) := LinearMap.pi (fun i : s => reading F J u.2 i.val d u.1)
  let B := LinearMap.pi (fun i : s => i.val.zeroScale (Maxwell.Free.hierarchy C.labels).smooth d)
  let l := comap (Prod.fst : ℝ × Viewers F → ℝ) trail
  have hlim (v : E C.labels d) : Tendsto (fun u => A u v) l (𝓝 (B v)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply Metric.tendsto_nhds.mpr
    intro a ha
    have h := all_tested F R J H hG X hR i.val d v a ha
    filter_upwards [(show Tendsto (Prod.fst : ℝ × Viewers F → ℝ) l trail from tendsto_comap).eventually h] with u hu
    simpa only [A,B,LinearMap.pi_apply,dist_eq_norm] using hu u.2
  obtain ⟨B',hB',h₁⟩ := Measuring.priced hlim hs
  have hgood : ∀ᶠ r in trail, ∀ p : Viewers F, ∀ v : E C.labels d,
      ‖A (r,p) v‖ ≤ B'*‖v‖ ∧ ‖v‖ ≤ B'*‖A (r,p) v‖ :=
    (eventually_comap.mp h₁).mono (fun r hr p => hr (r,p) rfl)
  refine ⟨s,K*B',one_le_mul_of_one_le_of_one_le hK hB',?_⟩
  filter_upwards [hf,hgood] with r hr hrV t ht p v
  have h := (hrV p ((J r d).symm v)).2
  calc
    _ ≤ K*t^(-(d:ℝ)-ε)*‖(J r d).symm v‖ := hr t ht v
    _ ≤ K*t^(-(d:ℝ)-ε)*(B'*‖A (r,p) ((J r d).symm v)‖) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg (zero_le_one.trans hK) (Real.rpow_nonneg ht.1.le _))
    _ = _ := by change _ = K*B'*t^(-(d:ℝ)-ε)*‖A (r,p) ((J r d).symm v)‖; ring

end YM.Integration.WilsonPhysicalExteriorProfiles
