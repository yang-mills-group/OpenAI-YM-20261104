import YM.MS.ScaleForest.Sew

/-!
# Pole reader and distribution across integrated graph operands

No RE-evaluation on the four dimensional (z=0) slice. We prove all
distributive laws needed when replacing a child graph by the sum of its
forests, using the actual regulated integrals of Glue and UV (in particular
the `integratePages_add` and `closePages_add` used for internal loop nodes).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest

open Set Filter MeasureTheory Real
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color
open Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave
open scoped Topology ContDiff

variable {G : Gauge} {K : Rip G} {F H : Mob G} {b : Bool} {r u v : ℤ} {n h : ℕ}
  {f : Coat G} {X Y J L : Flats G} {z : ℂ}
/-! Explicit correctness spec for the pole reader. -/
theorem ct_extract (hr : Merg X) {i : ℕ} (hi : i < poleOrderBound X) :
    Pick i (paid (poleOrderBound X) (-counterterm X)) (Press X i (poleOrderBound X) 0) := by
  rw [counterterm,neg_neg]
  exact Mint_pick (sufficientBound hr) hi

theorem ct_insert (hr : Merg X) {i : ℕ} (hi : i < poleOrderBound X) :
    Pick i (paid (poleOrderBound X) (counterterm X)) (-Press X i (poleOrderBound X) 0) := by
  have ht := (ct_extract hr hi).static (-1)
  simp only [neg_one_smul] at ht
  rw [show -paid (poleOrderBound X) (-counterterm X) = paid (poleOrderBound X) (counterterm X) from ?_] at ht
  · exact ht
  ext z m w; simp [paid]

/-- These numbers are the negative Laurent coefficients of the prepared
amplitude, the same at all length and mass parameters. -/
theorem before_insert (hr : Merg X) (hv : Vibe h X J) (hp : Stay h J)
    {i : ℕ} (hi : i < poleOrderBound X) (y s : ℝ) :
    Pick i (paid (poleOrderBound X) (Parade X h y s)) (Press X i (poleOrderBound X) 0) := by
  have hR := sufficientBound hr
  obtain ⟨he,H⟩ := assign_home hR hv hp hi
  obtain ht := press_pick (m:=i) hR h s y
  rwa [← H,he s] at ht

/-- On the all-important (special) forest with the entire subgraph contracted. -/
theorem parade_collapsed_ct (hX : Sewable b r h 0 X) (hv : Vibe h X J) (hp : Stay h J) (s y : ℝ) :
    Parade (collapsed (counterterm X)) h y s = counterterm X :=
  pureP _ (pole_cancels hX hv hp).count s y

/-! Linearity needed to split into each quotient and pole part. -/
theorem same_pact (X : Flats G) : Pact X X := fun _ => EventuallyEq.rfl
theorem pact_comp (h : Pact X Y) (hp : Pact Y J) : Pact X J := fun i => (h i).trans (hp i)

theorem bridgePages_congr (hK : HalfKernel K) (hX : Pact X Y) (hJ : Pact J L) :
    Pact (bridgePages K X J) (bridgePages K Y L) := by
  rw [bridgePages_eq hK.rev,bridgePages_eq hK.rev]; exact pair_pact _ hX hJ

theorem bridgePages_left (hK : HalfKernel K) (X Y J : Flats G) :
    bridgePages K (X+Y) J = bridgePages K X J + bridgePages K Y J := by
  simp_rw [bridgePages_eq hK.rev, map_add, LinearMap.add_apply]

theorem bridgePages_right (hK : HalfKernel K) (X Y J : Flats G) :
    bridgePages K X (Y+J) = bridgePages K X Y + bridgePages K X J := by
  simp_rw [bridgePages_eq hK.rev, map_add]

theorem closePages_add (hK : HalfKernel K) (hX : Moony b X) (hY : Moony b Y) :
    Pact (closePages K (X+Y)) (closePages K X + closePages K Y) := by
  refine pact_comp (closePages_pact (hK.forms b) (Sun.HeapS.plus hX hY)) ?_
  rw [map_add]
  exact pact_sym (common (closePages_pact (hK.forms b) hX) (closePages_pact (hK.forms b) hY))

theorem closePages_congr (hK : HalfKernel K) (hX : Moony b X) (hY : Moony b Y) (he : Pact X Y) :
    Pact (closePages K X) (closePages K Y) :=
  pact_comp (closePages_pact (hK.forms b) hX) (pact_comp (same_jump he _ _)
    (pact_sym (closePages_pact (hK.forms b) hY)))

theorem scaleIntegral_aux_add (hw : kPrice F) (hG : kPrice H) (x : ℂ) (s a : ℝ) :
    finiteIntegral a s x (F+H) = finiteIntegral a s x F + finiteIntegral a s x H := by
  funext m w
  simp_rw [finiteIntegral,← cert,map_add,Pi.add_apply]
  exact intervalIntegral.integral_add (interval_plow hw a s x w) (interval_plow hG a s x w)

theorem regulated_add (hX : kPrice F) (hY : kPrice H) (z : ℂ) (h ell : ℕ) (a s : ℝ) :
    regulated a s z h ell (F+H) = regulated a s z h ell F + regulated a s z h ell H := by
  unfold regulated
  rw [scaleIntegral_aux_add hX hY]
  split_ifs with he
  · abel
  unfold belowCut
  simp_rw [t_plus hX hY, smul_add, Finset.sum_add_distrib]
  abel

theorem integratePages_add (hX : Sewable b r h 0 X) (hY : Sewable b r h 0 Y) :
    Pact (integratePages h (X+Y)) (integratePages h X + integratePages h Y) := by
  have hC : Sewable b r h 0 (X+Y) := by simpa only [add_zero] using hX.plus hY
  have ht {X : Flats G} (hX : Sewable b r h 0 X) (ell : ℕ) :=
    uv_limit (h:=h) (ell:=ell) ((clockMoon hX.clock ell).mer) (fun he => (he : ell = 0) ▸ hX.start)
  intro i
  filter_upwards [ht hC i, ht hX i, ht hY i,
    (clockMoon hX.clock i).mer.price, (clockMoon hY.clock i).mer.price] with z hz hV hU hw ht
  rw [Finsupp.add_apply, Pi.add_apply, integrate_each, integrate_each, integrate_each]
  obtain H1 := hz.2 0; obtain H2 := hV.2 0; obtain H3 := hU.2 0
  simp only [posing] at H1 H2 H3
  refine Shine.Wind.unique H1 ?_
  simp_rw [Finsupp.add_apply, Pi.add_apply, regulated_add hw ht]
  intro m w
  exact Tendsto.add (H2 m w) (H3 m w)

theorem integratePages_congr (h : ℕ) (he : Pact X Y) :
    Pact (integratePages h X) (integratePages h Y) := by
  intro i; rw [integrate_each,integrate_each]
  exact (he i).mono fun z hz => congr_arg (scaleIntegral z h i) hz

theorem ct_unique (hr : Stay h (X + collapsed f)) (hu : Count f h) (hv : Cool f)
    (hm : Sewable b r h 0 X) (hZ : Vibe h X Y) (hp : Stay h Y) :
    f = counterterm X := by
  have ht := (pole_cancels hm hZ hp).stay
  have hx := Live.sub (hr 0 0) (ht 0 0)
  rw [page_add,page_add, pureP _ hu, parade_collapsed_ct hm hZ hp] at hx
  rw [show (Parade X h 0 0 + f) - _ = f-counterterm X from by abel] at hx
  exact sub_eq_zero.mp (deep_zero ((cone G).sub_mem hv (ct_cool X)) (Live.tends hx).choose_spec)

end YM.MS.ScaleForest
