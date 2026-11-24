import YM.RG3.Pan.ModeEstimate

/-! # Complete dialect for an unmasked grouped payload on genuine
curvature: value paid, all actual left derivatives paid, at every allowed
mark or size at the common patch. Combine using REGULAR only, until actual
Masks bought separately incl their failure terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Pan.ModeEstimate
open YM.RG3.Pan Function FreeResolvent Lattice RG Wilson WilsonStartup Next.Rank.Spindle Filter SelectedOrderedKernels WardBin.Lies MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {n : Side} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : BudgetPoint} {o : Site n} {b r k : ℕ} {ε C : ℝ}
  {F : Config G n→E} {f : Palette G b→E}

local notation "hull" => Next.Rank.Spindle.patch
def Tariff (G : Gauge) (k b r : ℕ) (p : BudgetPoint) (ε C:ℝ): ℝ:= erent k r (candle G) (clock G k b*glitter p b) p.threshold ε C
lemma tariff_nn (G : Gauge) (k b r : ℕ) (p : BudgetPoint) {ε C:ℝ} (hε : 0≤ε) (hC : 0≤C): 0 ≤ Tariff G k b r p ε C:= erent_nn _ _ (candle_pos ..)
    (mul_nonneg (zero_le_one.trans (one_le_clock ..)) (zero_le_one.trans (one_le_glitter ..))) p.threshold_pos.le hε hC

/-- We export both ContDiffAt and the actual LEFT price. It's enough for any
representer f agreeing as an unmasked germ at these U. DANGER: equality at
just the healthy points not known to be enough (flag set truth at equality!).
`k` may match moving stage order, with stage costs to absorb. -/
theorem lights_up (he : 2*(b+1)<n.val) (U : Config G n) (hH : Healthy p.threshold (hull b o) U)
    (hx : F =ᶠ[𝓝 U] f ∘ palette b o) (h : Axial.Ordinary f r k p.threshold ε C):
    ContDiffAt ℝ k (F ∘ increment U) 0 ∧ ∀ x∈hull b o, ∀ l : List (Directions G n), l.length ≤ k → (∀ A∈l,p.dirBound x A) →
      ‖leftDerivs F l U‖ ≤ Tariff G k b r p ε C := by
  have hp : ‖palette b o U‖ ≤ p.threshold:=healthy_palette p.threshold_pos.le he hH
  have hv : Tendsto (increment U) (𝓝 0) (𝓝 U) := by
    nth_rw 2 [← Work.G07.at_zero_increment U]
    exact (show Continuous (increment U) by unfold increment;fun_prop).tendsto _
  have hz : increment U 0=U:=Work.G07.at_zero_increment _
  have ht := ((show ContDiffAt ℝ k f ((palette b o ∘ increment U) 0) by rw [comp_apply,hz]; exact h.germ _ hp).comp _
    (stellar k b o U)).congr_of_eventuallyEq (hx.comp_tendsto hv)
  refine ⟨ht,fun x hh l hl hL=>?_⟩
  let A:= l.get
  rw [← List.ofFn_get l,Germ.ordered A (ht.of_le (Nat.cast_le.mpr hl))]
  have hu : ∀ i,p.dirBound x (A i):= fun i=>hL _ (List.get_mem l i)
  let V := journey U l.length A
  have hw : V 0=U:= by unfold V; rw [journey_photon,comp_apply,map_zero,chug_zero]
  have hs (e : Edge (Site n)): Continuous (fun z : Panels l.length=>V z e):= by
    unfold V; simp_rw [journey,chug_apply]; exact ((chain_cont G l.length).comp (continuous_pi fun i=> (show Continuous (fun z : Panels l.length=> z i • A i e) by fun_prop))).mul continuous_const -- check simp
  have hg : Tendsto V (𝓝 0) (𝓝 U):= hw ▸ (continuous_pi hs).tendsto (0:Panels l.length)
  change ‖iteratedFDeriv ℝ _ (F ∘ V) 0 _‖ ≤ _
  rw [((hx.comp_tendsto hg).iteratedFDeriv ℝ l.length).eq_of_nhds]
  have hi := (palette_jets p x o U hh A hl hu).resonance (by rw [Function.comp_apply, show journey U l.length A 0=U from hw]; exact hp) h
    (mul_nonneg (zero_le_one.trans (one_le_clock ..)) (zero_le_one.trans (one_le_glitter ..)))
  refine (ContinuousMultilinearMap.le_opNorm_mul_prod_of_le _ (b:=fun _=>1) (fun i : Fin l.length=> ?cart)).trans ?_
  case cart=> change ‖cart i‖ ≤ (1:ℝ); unfold cart; rw [Pi.norm_single]; simp
  simpa only [one_pow,mul_one,Finset.prod_const_one,Tariff,Function.comp_assoc,V] using hi.B _ hl

variable [MeasurableSpace E] {X : Support n}
/-- RG regular price on the common hull. Path and mask discrepancies in a
published exponent are not removed by this theorem. -/
theorem elevated (he : 2*(b+1)<n.val) (hF : GaugeInvariant F) (hB : Measurable F) (hL : LocalOn ↑X F) (hX : X⊆hull b o)
    (hx : ∀ U,Healthy p.threshold (hull b o) U → F =ᶠ[𝓝 U] f ∘ palette b o) (h : Axial.Ordinary f r k p.threshold ε C)
    (hk : p.order ≤ k): p.Regular (hull b o) F ∧ ∀ x∈hull b o,p.supBounds x (hull b o) F (Tariff G k b r p ε C):= by
  have he' (U : Config G n)(hu:Healthy p.threshold (hull b o) U): ContDiffAt ℝ p.order (F ∘ increment U) 0:=
    ((lights_up he U hu (hx U hu) h).1).of_le (Nat.cast_le.mpr hk)
  refine ⟨⟨fun U V hi=>hL U V (agrees_mono hi (fun _ h=>hX h)),hB,hF,he',fun U hu A _ hl=> Next.Foundations.left_has A hl (he' U hu)⟩,fun x hi=>⟨tariff_nn _ _ _ _ _ h.small h.high,fun U hu l hl=> (lights_up he U hu (hx U hu) h).2 x hi l (hl.trans hk)⟩⟩
end YM.RG3.Pan.ModeEstimate
