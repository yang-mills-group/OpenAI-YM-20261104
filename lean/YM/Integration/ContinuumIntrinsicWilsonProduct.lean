import YM.Integration.IntrinsicProductCompactness

/-! Physical continuum Gram estimates for every sublimit of the same
original intrinsic report on the full multipoint Wilson field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ContinuumIntrinsicWilsonProduct
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct FilteredProductLimit IntrinsicProductCompactness
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

private def meter (T : Table C.book) (U : Detector S D) (i : Fin U.size) : C.label D →ₗ[ℂ] ℂ :=
  T.injectFront (detectorRaw S ∘ tags S (U.listen i)) (Points.cons 0 (OPE.positions S (U.listen i))) D

private theorem meter_field (hS : S.Symmetric) (U : Detector S D) (i : Fin U.size) (z : C.label D) :
    meter S U i z = witnessAt S D (U.listen i) (S.project D z) := by
  let A := detectorRaw S ∘ tags S (U.listen i)
  let v : Fin ((U.listen i).length+1) → C.book.Token := Fin.cons (⟨D,z⟩ : C.book.Token) A
  let q := Points.cons 0 (OPE.positions S (U.listen i))
  have eq : S.classTokens ∘ v = Fin.cons (α:=fun _ : Fin ((U.listen i).length+1) => S.Tag) (⟨D,S.project D z⟩: S.Tag) (OPE.tags S (U.listen i)) := by
    funext k
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · simp only [v,A,comp_apply,Fin.cons_succ,raw_class]
  change S.read q v = _
  rw [witness_kernel,← eq]
  exact (S.at_project S hS (fun _ => le_rfl) (generic_conf _ (U.awake i)) v).symm

private theorem zero_site (C : Family G) (w : ℕ × ℕ) : ceilSite C w.1 w.2 (0:E4) = 0 := by
  change Lattice.wrap _ (fun _ => ⌈(0:ℝ)/C.S.a w.1⌉) = 0
  simp only [zero_div,Int.ceil_zero]
  exact (Lattice.wrap _).map_zero

theorem physical_meter (U : Detector S D) (i : Fin U.size) (w : ℕ × ℕ) (z : C.label D) :
    meter (rounded C w.1 w.2) U i z =
      moment (C.beta w.1 w.2) (C.O w.1 w.2 z 0 * FilteredWilsonProduct.listen U i w) := by
  let E := U.listen i
  let v : Fin (E.length+1) → C.book.Token := Fin.cons (⟨D,z⟩: C.book.Token) (detectorRaw S ∘ tags S E)
  let q := Points.cons 0 (OPE.positions S E)
  change moment (C.beta w.1 w.2) (fun V => ∏ k, C.seen (v k) (ceilSite C w.1 w.2 (q k)) V) = _
  apply congrArg (moment (C.beta w.1 w.2))
  funext V
  rw [Fin.prod_univ_succ]
  simp only [v,q,Points.cons,points_apply,Fin.cons_zero,Fin.cons_succ,zero_site,comp_apply,
    Pi.mul_apply,FilteredWilsonProduct.listen,Finset.prod_apply]
  rfl

/-- A varying raw reference label with a limit on a physical subfilter
has the corresponding one-point continuum Gram samples. -/
theorem meter_tendsto (F : Spec.Final C f S) (services : Services C f S) (sym : S.Symmetric)
    (U : Detector S D) (i : Fin U.size) {l : Filter (ℕ × ℕ)} (filterSub : l≤f.fuse)
    {Z : (ℕ × ℕ) → C.label D} {z : C.label D} (limit : Tendsto Z l (𝓝 z)) :
    Tendsto (fun w => moment (C.beta w.1 w.2) (C.O w.1 w.2 (Z w) 0 * FilteredWilsonProduct.listen U i w))
      l (𝓝 (witnessAt S D (U.listen i) (S.project D z))) := by
  let A := detectorRaw S ∘ tags S (U.listen i)
  let x := Points.cons 0 (OPE.positions S (U.listen i))
  let M (w : ℕ × ℕ) := meter (rounded C w.1 w.2) U i
  let N := meter S U i
  have fixed (v : C.label D) : Tendsto (fun w => M w v) l (𝓝 (N v)) :=
    (rounded_tendsto_separated F services (Fin.cons (⟨D,v⟩ : C.book.Token) A) x (generic_conf _ (U.awake i))).mono_left filterSub
  let b := Module.finBasis ℂ (C.label D)
  have expand (L : C.label D →ₗ[ℂ] ℂ) (p : C.label D) :
      L p = ∑ k, b.repr p k * L (b k) := by
    conv_lhs => rw [← b.sum_repr p]
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
  rw [← meter_field sym U i z]
  change Tendsto _ l (𝓝 (N z))
  rw [expand N z]
  apply (tendsto_finsetSum Finset.univ (fun k _ =>
    (((b.coord k).continuous_of_finiteDimensional.continuousAt.tendsto.comp limit).mul (fixed (b k))))).congr'
  filter_upwards with w
  exact (expand (M w) (Z w)).symm.trans (physical_meter U i w (Z w))

/-- Along the same subfilter the entire signed original moment converges
to the native continuum complete-product detector residual. -/
theorem residual_tendsto (F : Spec.Final C f S) (services : Services C f S) (sym : S.Symmetric)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i))
    (t : ℝ) (j : ℕ) (x : I → Cover) {l : Filter (ℕ × ℕ)} (filterSub : l≤f.fuse)
    {Z : (ℕ × ℕ) → C.label D} {z : C.label D} (limit : Tendsto Z l (𝓝 z))
    (hx : ∀ i, Injective (beside (fun k => C.S.gridPoint j (x k)) (OPE.positions S (U.listen i)).ofLp)) :
    Tendsto (fun w => original U w (raw J v t j x w) (Z w)) l
      (𝓝 (PhysicalMSOPEReadout.candidateResidual J U v t (fun k => C.S.gridPoint j (x k)) (S.project D z))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  let p (k : I) := C.S.gridPoint j (x k)
  let y := (OPE.positions S (U.listen i)).ofLp
  let e := fun k => (tags S (U.listen i) k).2
  have listen_eq (w : ℕ × ℕ) : FilteredWilsonProduct.listen U i w = product y e w.1 w.2 := by
    funext V
    simp only [FilteredWilsonProduct.listen,Finset.prod_apply]
    rfl
  have whole := (whole_tendsto_separated F services p (PhysMS.Frame.born J t v) y e (hx i)).mono_left filterSub
  have counter := meter_tendsto F services sym U i filterSub limit
  apply (whole.sub counter).congr'
  filter_upwards with w
  let A := raw J v t j x w
  let P := C.O w.1 w.2 (Z w) 0
  let E := FilteredWilsonProduct.listen U i w
  have cE : Continuous E := by rw [show E = _ from listen_eq w]; exact product_continuous ..
  have mulEq : product (beside p y) (stages (PhysMS.Frame.born J t v) e) w.1 w.2 = A*E := by
    change _ = A*FilteredWilsonProduct.listen U i w
    rw [listen_eq]
    exact funext (product_split p (PhysMS.Frame.born J t v) y e w.1 w.2)
  change moment (C.beta w.1 w.2) _ - moment _ (P*E) = moment _ ((A-P)*E)
  rw [mulEq,sub_mul]
  exact (integral_sub (continuous_integrable _ ((product_continuous ..).mul cE))
    (continuous_integrable _ ((C.continuousO ..).mul cE))).symm

/-- Cluster points always refer to the gated intrinsic terminal report of
the actual complete product at this physical grid. -/
def Cluster (F : Spec.Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (v : (i : I) → (Climb.Bel C.book).Field (d i)) (t : ℝ)
    (b j : ℕ) (x : I → Cover) (z : C.label D) : Prop :=
  ∃ l : Filter (ℕ × ℕ), l.NeBot ∧ l ≤ f.fuse ∧
    Tendsto (fun w => value (D:=D) F.room.cutoff b w (field F R J v t j x w)) l (𝓝 z)

/-- Every actual canonical cluster point has the full normalized
continuum engineering estimate, for ordinary inputs at all loop orders. -/
theorem engineering (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ b m j : ℝ → ℕ, ∃ h a c : ℝ, Height C.S trail LogV b h ∧ Height C.S trail LogV m a ∧
      Height C.S trail LogV j c ∧ 0 < h ∧ h < a ∧ a < 1 ∧ 1 < c ∧
      ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (j t)^n * e t) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (b t) (m t) (j t) x →
        (∃ z : C.label D, Cluster F R J v t (b t) (j t) x z) ∧
          ∀ z : C.label D, Cluster F R J v t (b t) (j t) x z →
            ‖wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t
              (fun k => C.S.gridPoint (j t) (x k)) (S.project D z))‖ ≤ e t := by
  obtain ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,e,he,loop,measured⟩ :=
    MeasuredIntrinsicWilsonProduct.engineering F facility anchor R U J H v
  refine ⟨b,m,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,e,he,loop,?_⟩
  filter_upwards [measured,MeasuredIntrinsicWilsonProduct.plot_clear (I:=I) U b m j hm.grows,
    sublimit F facility anchor R J v hb hm hj hh ha (h₁.trans hc) D] with t paid cleared chosen
  intro x hx
  constructor
  · obtain ⟨l,z,live,sub,hz⟩ := chosen x hx
    exact ⟨z,l,live,sub,hz⟩
  intro z cluster
  obtain ⟨l,hl,sub,hz⟩ := cluster
  haveI := hl
  let out (w : ℕ × ℕ) := value (D:=D) F.room.cutoff (b t) w (field F R J v t (j t) x w)
  let A (w : ℕ × ℕ) := raw J v t (j t) x w
  let L := wholeReadout U J t
  have converge := residual_tendsto F facility.toServices R.continuum.laws.toSymmetric U J v t (j t) x sub hz (cleared x hx)
  have bound : ∀ᶠ w in l, ‖L (original U w (A w) (out w))‖ ≤ e t := by
    filter_upwards [(paid x hx).filter_mono sub] with w receipt
    obtain ⟨ho,live,_,cost⟩ := receipt
    simpa only [out,A,L,value_eq F.room.cutoff ho live] using cost
  exact le_of_tendsto (L.continuous.continuousAt.tendsto.comp converge).norm bound

end YM.Integration.ContinuumIntrinsicWilsonProduct
