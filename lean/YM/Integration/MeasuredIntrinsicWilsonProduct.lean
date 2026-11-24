import YM.Integration.FilteredProductLimit

/-! Raw born-cap Wilson moments with the genuine exterior detector and
the single intrinsic counterterm of their exact filtration resolution. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MeasuredIntrinsicWilsonProduct
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct FilteredProductLimit
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

omit [Fintype I] in
/-- The ordinary physical detector is separated on every admitted plot
once its grid has entered the fixed exterior clearance. -/
theorem plot_clear (U : Detector S D) (b m j : ℝ → ℕ) (growth : Tendsto m trail atTop) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
      ∀ i, Injective (beside (fun k => C.S.gridPoint (j t) (x k)) (OPE.positions S (U.listen i)).ofLp) := by
  obtain ⟨δ,hδ,clear⟩ := detector_uniform_clearance U
  have small : Tendsto (fun t => C.S.a (m t+1)) trail (𝓝 0) :=
    C.S.shrinks.comp ((tendsto_add_atTop_nat 1).comp growth)
  filter_upwards [small.eventually (gt_mem_nhds hδ)] with t width
  intro x shape i
  let p (k : I) := C.S.gridPoint (j t) (x k)
  let y := (OPE.positions S (U.listen i)).ofLp
  have inner : Injective p := by
    intro a b eq
    by_contra hn
    have h := shape.spaced a b hn
    change 2*C.S.a (j t)*((C.path.levels.budget (j t)).B:ℝ)^2 < ‖p a-p b‖ at h
    rw [eq,sub_self,norm_zero] at h
    have hbase := C.S.a_pos (j t)
    exact (not_lt_of_ge (mul_nonneg (mul_nonneg (by norm_num) hbase.le) (sq_nonneg _))) h
  have outside : Injective y := by
    intro k l eq
    by_contra hn
    have h := (clear i).spread k l hn
    change δ ≤ ‖y k-y l‖ at h
    rw [eq,sub_self,norm_zero] at h
    exact (not_le_of_gt hδ) h
  have distinct (k : I) (l : Fin (U.listen i).length) : p k ≠ y l := by
    intro eq
    have h := (clear i).openSpace l
    change δ ≤ ‖(0:E4)-y l‖ at h
    rw [zero_sub,norm_neg,← eq] at h
    have shr := shape.fit k
    change 8*‖p k‖ < C.S.a (m t+1) at shr
    change C.S.a (m t+1) < δ at width
    linarith [norm_nonneg (p k)]
  rintro (k|k) (l|l) eq
  · exact congrArg Sum.inl (inner eq)
  · exact (distinct k l eq).elim
  · exact (distinct l k eq.symm).elim
  · exact congrArg Sum.inr (outside eq)

private theorem cont_field (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) : Continuous (field F R J v t j x w) := by
  have eq : field F R J v t j x w = fun U => ∏ i, ∑ k : Fin (d i+1), C.O w.1 w.2
      (S.representative _ (R.cutTest k.val (d i) (J t (d i) (v i)))) (location C.S j w.1 w.2 (x i)) U := by
    funext U
    simp only [field,Finset.sum_apply,Finset.prod_apply]
  rw [eq]
  exact continuous_finsetProd _ fun i _ => continuous_finsetSum _ fun k _ => C.continuousO ..

/-- Changing the input leaves to their undivided physical representatives
does not change the counterterm attached to this same regulated model. -/
theorem replace_input (F : Spec.Final C f S)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin) (U : Detector S D)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (z : C.label D) :
    original U w (raw J v t j x w) z = original U w (field F R J v t j x w) z +
      difference F R U J v t j x w := by
  funext i
  let A := raw J v t j x w
  let B := field F R J v t j x w
  let P := C.O w.1 w.2 z 0
  let L := FilteredWilsonProduct.listen U i w
  have cL : Continuous L := by
    have eq : L = fun Y => ∏ k, C.O w.1 w.2 (detectorRaw S (tags S (U.listen i) k)).2
        (ceilSite C w.1 w.2 ((OPE.positions S (U.listen i)).ofLp k)) Y := by
      funext Y; exact Finset.prod_apply ..
    rw [eq]
    exact continuous_finsetProd _ fun k _ => C.continuousO ..
  have sub (X : Config G (C.side w.1 w.2) → ℂ) (hX : Continuous X) :
      moment (C.beta w.1 w.2) ((X-P)*L) =
      moment (C.beta w.1 w.2) (X*L) - moment (C.beta w.1 w.2) (P*L) := by
    rw [sub_mul]
    exact integral_sub (continuous_integrable _ (hX.mul cL))
      (continuous_integrable _ ((C.continuousO ..).mul cL))
  have ca : Continuous A := product_continuous .. 
  have cb : Continuous B := cont_field F R J v t j x w
  change moment (C.beta w.1 w.2) ((A-P)*L) = moment _ ((B-P)*L) +
    (moment _ (A*L)-moment _ (B*L))
  rw [sub A ca,sub B cb]
  ring

def Measured (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (b j : ℕ) (x : I → Cover) (w : ℕ × ℕ) (fee : ℝ) : Prop :=
  ∃ (ho : Opened C D b w.2) (live : b ≤ w.1),
    let Y := field F R J v t j x w
    let z := FilteredWilsonProduct.label F.room.cutoff ho live Y
    Booked C w.1 w.2 D Y b live ∧
      ‖wholeReadout U J t (original U w (raw J v t j x w) z)‖ ≤ fee

/-- The complete finite Wilson moment with ordinary born-cap inputs,
the funded intrinsic counterterm and the genuine inverse physical Gram
detector has a strict engineering margin at every admitted plot. -/
theorem engineering (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ b m j : ℝ → ℕ, ∃ h a c : ℝ, Height C.S trail LogV b h ∧ Height C.S trail LogV m a ∧
      Height C.S trail LogV j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (j t)^n * e t) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x → ∀ᶠ w in f.fuse,
        Measured F R U J v t (b t) (j t) x w (e t) := by
  obtain ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,e,he,_,paid⟩ :=
    FilteredWilsonProduct.engineering F facility anchor R U J H v
  let q := -(1:ℝ)/32
  let fee (t : ℝ) := e t + Real.exp (q*LogV t)
  have rate : RateLE trail LogV fee q := he.add ((RateIs.exp q PhysMS.to_log_zoom).pays PhysMS.to_log_zoom) PhysMS.to_log_zoom
  refine ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,fee,rate,?_,?_⟩
  · intro n
    have hp : RateLE trail LogV fee (-((0:ℕ):ℝ)-1/32) := by
      convert rate using 1
      norm_num [q]
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using
      all_loop_orders PhysMS.to_log_zoom 0 _ hp hj n
  · filter_upwards [paid,plot_clear (I:=I) U b m j hm.grows] with t bought disjoint
    intro x hx
    have ht := difference_tendsto F facility.toServices R U J v t (j t) x (disjoint x hx)
    have hl : Tendsto (fun w => wholeReadout U J t (difference F R U J v t (j t) x w)) f.fuse (𝓝 0) := by
      change Tendsto ((wholeReadout U J t) ∘ difference F R U J v t (j t) x) f.fuse (𝓝 0)
      simpa only [map_zero] using
        ((wholeReadout U J t).continuous.continuousAt.tendsto.comp ht)
    have hp := hl.norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using (Real.exp_pos (q*LogV t))))
    filter_upwards [bought x hx,hp] with w receipt tol
    obtain ⟨ho,live,book,_,_,fund⟩ := receipt
    let Y := field F R J v t (j t) x w
    let z := FilteredWilsonProduct.label F.room.cutoff ho live Y
    refine ⟨ho,live,book,?_⟩
    change ‖wholeReadout U J t (original U w (raw J v t (j t) x w) z)‖ ≤ _
    rw [replace_input F R U J v t (j t) x w z,map_add]
    exact (norm_add_le ..).trans (add_le_add fund tol.le)

end YM.Integration.MeasuredIntrinsicWilsonProduct
