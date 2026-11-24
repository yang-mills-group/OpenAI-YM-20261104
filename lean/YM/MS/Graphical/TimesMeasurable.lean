import YangMills.WilsonProof.NativeSupport.YM.MS.Graphical.PinScale

/-!
# Borel representatives for schedules (log-length distributions supplied as functions)

Only require Borel measurability in logarithmic time of each word evaluation,
rather than time continuity. For operations including `radialClose`, we verify
measurability through the Arc prescription. No measurable selection of z through time is required.
-/
noncomputable section
namespace YM.MS.Graphical
open Set Filter Function Finset MeasureTheory Real Metric
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color
open _root_.YM.MS.Shine Hem Mell Pearl Train Signal Book Convolve Garment.Wick Dock
open scoped Topology ContDiff Interval
variable {I E J : Type} {U : Set ℂ} {p t v a b c R : ℝ} {m n : ℕ} {G : Gauge} {x : Tone.QP} {k j : I→ ℝ} {Y Z : I→ℂ}
variable {F H : ℝ→Mob G}

abbrev BorelRow (F : ℝ→ Mob G) := ∀ m, ∀ w:Legs (Shore G m), Measurable fun t=> F t m w

lemma scatter_meas {f : ℝ → Shared I ℂ} (w : Legs I) (p : Sector I)
    (h : ∀ l r : Legs I, Split l r w → Measurable (fun i=> f i l r)) :
    Measurable (fun i=>scatter p w (f i)) := by
  induction w generalizing f with
  | nil=>exact h _ _ .nil
  | cons i w ih=>exact ih (fun l r he=> (h _ _ he.left).add ((h _ _ he.right).const_mul _))

lemma shuffle_meas (hf : BorelRow F) (hg : BorelRow H) : BorelRow fun t=> shuffleRows (F t) (H t) := by
  intro n w; unfold shuffleRows; simp_rw [scattered]; exact scatter_meas w _ fun l r _=> (hf _ _).mul (hg _ _)

lemma bring_meas (hf : BorelRow F) : BorelRow fun t=> bring x (F t) := fun n l=> (hf n l).const_mul _

lemma shell_meas (a b : Cfield G m) (p : SectorP m) : Measurable (fun t : ℝ=> halfD t m a b p) := by
  apply Continuous.measurable
  unfold halfD; apply Continuous.smul Real.continuous_exp; simp only [Landau.choir]; split
  · rcases a with ⟨⟨_|a,_|_⟩,v⟩ <;> rcases b with ⟨⟨_|a,_|_⟩,w⟩ <;>
      simp only [City.L0, City.brush] <;> fun_prop
  exact continuous_const

lemma bridge_meas (h : BorelRow F) (he : BorelRow H) :
    BorelRow fun t=> bridging t (F t) (H t):= by
  intro m w; refine scatter_meas w _ (fun i j _=>?_)
  apply Finset.measurable_fun_sum; intro a ha; apply Finset.measurable_fun_sum; intro b hb
  exact (((shell_meas a b _).const_mul _).mul ((h _ _).const_mul _)).mul (he _ _)

section
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]
lemma license {f : ℝ → E → ℂ} (h : ∀ t:ℝ, Continuous (f t)) (hf : ∀ p, Measurable fun t=> f t p) :
    Measurable (Function.uncurry f) := by
  letI : SecondCountableTopology E := inferInstance -- induce
  exact (measurable_uncurry_of_continuous_of_measurable h hf).comp measurable_swap
end

private lemma Borel_via_integral [MeasurableSpace E] {f : ℝ→E→ℂ} (μ : Measure E) [SFinite μ]
    (h : Measurable (Function.uncurry f)) : Measurable (fun t=>∫ q, f t q ∂μ) :=
  h.stronglyMeasurable.integral_prod_right.measurable

private lemma d_meas {f : ℝ→ Tree ℝ ℂ} (hv : ∀ t, ContDiff ℝ ∞ (f t))
    (h : ∀ p, Measurable fun t=> f t p) : ∀ p, Measurable fun t=> Arc.d (f t) p:= by
  rintro ⟨x,y⟩
  refine measurable_of_tendsto_metrizable' (f:=fun k : ℝ=> fun t=> k⁻¹ • (f t (x+k,y)-f t (x,y)))
      (𝓝[≠] 0) (fun i=> ((h (x+i,y)).sub (h (x,y))).const_smul (i⁻¹ : ℝ)) (tendsto_pi_nhds.mpr fun s=>?_)
  simpa only [slope_def_module] using (dr (hv s) y x).tendsto_slope_zero

private lemma chop_meas {f : ℝ→ Tree ℝ ℂ} (hv : ∀ t, ContDiff ℝ ∞ (f t))
    (h : ∀ p, Measurable fun t=> f t p) (p : ℝ × ℝ) : Measurable fun t=> chop (f t) p:= by
  unfold chop; simp_rw [ intervalIntegral.integral_of_le zero_le_one]
  refine Borel_via_integral _ (license (fun i=>?_ ) fun x=> d_meas (fun i=>fresh (hv i))
       (d_meas hv h) _)
  exact (fresh (fresh (hv i))).continuous.comp (f:=fun t:ℝ=>(t*p.1,p.2)) (by fun_prop)

private lemma prune_meas {f : ℝ → Tree ℝ ℂ} (hv : ∀ t, ContDiff ℝ ∞ (f t))
    (h : ∀ p, Measurable fun t=> f t p) (n : ℕ) :
    (∀ p, Measurable (fun t=> pruning n (f t) p)) ∧ (∀ t, ContDiff ℝ ∞ (pruning n (f t))) := by
  induction n with | zero=>exact ⟨h,hv⟩| succ n ih=> simp_rw [spent]; exact ⟨chop_meas ih.2 ih.1, fun t=> c_chop (ih.2 t)⟩

lemma radial_meas (hf : BorelRow F) (hv : ∀ i, kPrice (F i)) (z : ℂ) (y : ℝ) :
    BorelRow fun t=> radialClose (halfD t) z y (F t) := by
  intro m l; apply Measurable.const_mul; let f(t):= wing z (halfD t) (F t) (ray l);
  have h0 i : rPrice (halfD (G:=G) i) := by rw [halfD_eq]; exact (c_bo i (b:=false)).price
  have hb (i:ℝ):Ultra (f i):=exact_test (hv i) (h0 i) (ray l) z
  have he : ∀ p : WingDomain m ℝ, Measurable (fun t=> f t p) := by
    intro p; unfold f wing Wtr
    simp only [Pi.add_apply,Pi.smul_apply,at_trc,yeast]; refine Measurable.add ?_ ?_
    · exact Finset.measurable_fun_sum _ fun i _=> Finset.measurable_fun_sum _
         fun j _=> (shell_meas i j _).mul (hf _ _)
    simp only [smul_eq_mul]; apply Measurable.const_mul; refine Finset.measurable_fun_sum _ fun i _=> Finset.measurable_fun_sum _
        fun j _=> Finset.measurable_fun_sum _ fun x _=> Finset.measurable_fun_sum _ fun k _=>?_
    exact (shell_meas _ _ _).mul (hf _ _)
  let g (i:ℝ) := carpet (Px m) (f i)
  have hq (p : ℝ×ℝ): Measurable (fun t=>g t p):= by
    apply Borel_via_integral (Px m) (license (fun i=> (hb i).smooth ()|>.continuous.comp (f:=fun q:SectorP m=>((q,p.1),p.2)) (by fun_prop)) (fun x=> he ((x,p.1),p.2)))
  obtain ⟨hp,H⟩:= prune_meas (f:=g) (fun i=> Q.Gquiet (Px m) (hb i)|>.smooth ()) hq (m+1)
  -- multiplication by cloud positive side; change using a measurable version.
  let c := (cloud_sees (z:=z)).mk (cloud z)
  obtain hc: Measurable c := cloud_sees.stronglyMeasurable_mk.measurable
  obtain hx : (cloud z)=ᵐ[μhalf] c := cloud_sees.ae_eq_mk
  change Measurable (gage m • (fun i=> ∫ p, cloud z p * pruning (m+1) (g i) (p,(1:ℝ)) ∂μhalf))
  rw [show (fun (i:ℝ)=>∫ p,cloud z p * pruning (m+1) (g i) (p,1) ∂μhalf)=(fun (i:ℝ)=>∫ p,c p * pruning (m+1) (g i) (p,1) ∂μhalf) from
      funext fun i=> integral_congr_ae (hx.mono fun _ he=>congr_arg (·*_ ) he)]
  refine Measurable.const_smul (Borel_via_integral μhalf ?_) _
  exact (hc.comp measurable_snd).mul (license (fun i=> (H i).continuous.comp (f:=fun t:ℝ=>(t,(1:ℝ)))
      (by fun_prop)) fun x=> hp (x,1))
end YM.MS.Graphical
