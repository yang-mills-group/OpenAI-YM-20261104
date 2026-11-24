import YM.Integration.ContinuumIntrinsicWilsonProduct

/-! One physical mesh for all complete input vectors, regulator cluster
points, and independently prescribed exterior detectors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SharedIntrinsicWilsonGrid
open Function Filter MeasureTheory Lattice Wilson RG Cells OPE OPE.Orbits OPE.Cards OPE.Log
open StressFlux.Matching Frontier6.Road EngineeringWeightedReadout WilsonWholeLimit
open Trace.Pilot Trace.Physical.GermGraph RG16.Literal MultilinearCellCapture
open FilteredIntrinsicGramReadout FilteredWilsonProduct FilteredProductLimit IntrinsicProductCompactness
open ContinuumIntrinsicWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I : Type} [Fintype I] {d : I → ℕ} {D : ℕ}

/-- The mesh and engineering margin are fixed before either the exterior
train or the physical input coordinates are specified. -/
structure Plan (C : Family G) (D n m : ℕ) where
  b : ℝ → ℕ
  middle : ℝ → ℕ
  j : ℝ → ℕ
  h : ℝ
  a : ℝ
  c : ℝ
  coarse : Height C.S trail LogV b h
  mid : Height C.S trail LogV middle a
  fine : Height C.S trail LogV j c
  pos : 0 < h
  before : h < a
  low : a < 1
  high : 1 < c
  margin : Margin D n m h a c

def plan (C : Family G) (D n m : ℕ) : Plan C D n m := Classical.choice (show Nonempty (Plan C D n m) from by
  obtain ⟨h,a,c,hh,ha,h₁,hc,hmarg⟩ := engineering_margin D m n
  obtain ⟨b,hb⟩ := found PhysMS.to_log_zoom C.path.levels.fits.mesh hh.le
  obtain ⟨mid,hm⟩ := found PhysMS.to_log_zoom C.path.levels.fits.mesh (hh.trans ha).le
  obtain ⟨j,hj⟩ := found PhysMS.to_log_zoom C.path.levels.fits.mesh (zero_lt_one.trans hc).le
  exact ⟨b,mid,j,h,a,c,hb,hm,hj,hh,ha,h₁,hc,hmarg⟩)

private theorem submargin {n m k : ℕ} (P : Plan C D n m) (hk : k ≤ m) : Margin D n k P.h P.a P.c := by
  have hl : (k:ℝ)*(P.c-1) ≤ (m:ℝ)*(P.c-1) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (sub_nonneg.mpr P.high.le)
  have h := P.margin
  dsimp [Margin] at h ⊢
  linarith

private theorem decoded (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    {m : ℕ} (P : Plan C D (Fintype.card I) m) (hd : ∑ i, d i ≤ m)
    (v : ℝ → (i : I) → C.label (d i))
    (hv : ∀ i k, RateLE trail LogV (fun t => v t i k) (-(d i:ℝ))) :
    ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧ ∀ᶠ t in trail, ∀ x : I → Cover,
      Plot C (P.b t) (P.middle t) (P.j t) x → ∀ᶠ w in f.fuse,
        IntrinsicGramReadout.Decoded F.room.cutoff U J t (P.b t) (P.j t) x (v t) w (e t) := by
  obtain ⟨fee,expense,paid⟩ := on_grid F facility anchor D P.coarse P.mid P.fine P.pos P.before P.low P.high (submargin P hd) v hv
  obtain ⟨k,n,A,hA,price⟩ := IntrinsicGramReadout.bank (d:=d) F U 1 one_pos
  let K (i : Fin U.size) := ∏ a, (A i a * C.S.a (n i)^(-((OPE.tags S (U.listen i) a).1:ℝ)-1)+1)
  have pos (i : Fin U.size) : 0 ≤ K i := Finset.prod_nonneg (fun a _ =>
    add_nonneg (mul_nonneg (hA i a) (Real.rpow_nonneg (C.S.a_pos _).le _)) zero_le_one)
  refine ⟨fun t => columnPrice (wholeReadout U J t) K * fee t,?_,?_⟩
  · apply ((IntrinsicGramReadout.price_rate F U J H K pos).mul expense).mono
    linarith
  filter_upwards [paid,P.coarse.grows.eventually_ge_atTop k] with t funded level
  intro x hx
  filter_upwards [funded x hx,price,(Cards.largeMesh f).eventually_ge_atTop (P.j t)] with w cell bank hw
  exact bank (P.b t) (P.j t) level hw x (v t) _ cell J t

theorem graded (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i))
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (P.j t)^n * e t) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x → ∀ᶠ w in f.fuse,
        Finished F R J U v t (P.b t) (P.j t) x w (e t) := by
  choose fee rate booked using fun g : Grades d => decoded F facility anchor U J H P
    (Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (g i).isLt)
    (component F R J v g) (component_rate F R J H v g)
  let e (t : ℝ) := ∑ g, ‖fee g t‖
  have he : RateLE trail LogV e (-(1:ℝ)/32) := RateLE.sum PhysMS.to_log_zoom (fun g _ => (rate g).norm)
  refine ⟨e,he,?_,?_⟩
  · intro n
    have hp : RateLE trail LogV e (-((0:ℕ):ℝ)-1/32) := by simpa only [Nat.cast_zero,neg_zero,zero_sub,neg_div] using he
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using
      all_loop_orders PhysMS.to_log_zoom 0 _ hp P.fine n
  filter_upwards [eventually_all.mpr booked] with t sectors
  intro x hx
  filter_upwards [eventually_all.mpr (fun g => sectors g x hx),(Cards.largeMesh f).eventually_ge_atTop (C.ref 0),
    (Cards.largeMesh f).eventually_ge_atTop (P.j t)] with w rows hu hj
  exact assemble F R J U v t (P.b t) (P.j t) x w hu hj _ rows

theorem exists_cluster (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i)) (J : ℝ → PhysMS.tower S)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
      ∃ z : C.label D, Cluster F R J v t (P.b t) (P.j t) x z := by
  filter_upwards [sublimit F facility anchor R J v P.coarse P.mid P.fine P.pos P.before (P.low.trans P.high) D] with t chosen
  intro x hx
  obtain ⟨l,z,live,sub,hz⟩ := chosen x hx
  exact ⟨z,l,live,sub,hz⟩

/-- The same grid admits every detector and all born-cap vectors. At any
physical position the bound holds for every original intrinsic cluster point. -/
theorem serve (F : Spec.Final C f S) (facility : Facilities C f S) (anchor : I)
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i, d i))
    (U : Detector S D) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i : I) → (Climb.Bel C.book).Field (d i)) :
    ∃ e : ℝ → ℝ, RateLE trail LogV e (-(1:ℝ)/32) ∧
      (∀ n : ℕ, Tendsto (fun t => C.path.levels.clock.hatBeta (P.j t)^n * e t) trail (𝓝 0)) ∧
      ∀ᶠ t in trail, ∀ x : I → Cover, Plot C (P.b t) (P.middle t) (P.j t) x →
        ∀ z : C.label D, Cluster F R J v t (P.b t) (P.j t) x z →
          ‖wholeReadout U J t (PhysicalMSOPEReadout.candidateResidual J U v t
            (fun k => C.S.gridPoint (P.j t) (x k)) (S.project D z))‖ ≤ e t := by
  obtain ⟨e,he,loops,paid⟩ := graded F facility anchor R P U J H v
  refine ⟨e,he,loops,?_⟩
  filter_upwards [paid,MeasuredIntrinsicWilsonProduct.plot_clear (I:=I) U P.b P.middle P.j P.mid.grows] with t paid room
  intro x hx z selected
  obtain ⟨l,live,sub,hz⟩ := selected
  haveI := live
  let output (w : ℕ × ℕ) := value (D:=D) F.room.cutoff (P.b t) w (field F R J v t (P.j t) x w)
  let L := wholeReadout U J t
  let Y (w : ℕ × ℕ) := field F R J v t (P.j t) x w
  let candidate := PhysicalMSOPEReadout.candidateResidual J U v t (fun k => C.S.gridPoint (P.j t) (x k)) (S.project D z)
  have originalLimit := residual_tendsto F facility.toServices R.continuum.laws.toSymmetric U J v t (P.j t) x sub hz (room x hx)
  have correction := (difference_tendsto F facility.toServices R U J v t (P.j t) x (room x hx)).mono_left sub
  have scan : Tendsto (fun w => original U w (Y w) (output w)) l (𝓝 candidate) := by
    have both := originalLimit.sub correction
    rw [sub_zero] at both
    apply both.congr'
    filter_upwards with w
    rw [MeasuredIntrinsicWilsonProduct.replace_input F R U J v t (P.j t) x w (output w)]
    exact add_sub_cancel_right .. 
  have price : ∀ᶠ w in l, ‖L (original U w (Y w) (output w))‖ ≤ e t := by
    filter_upwards [(paid x hx).filter_mono sub] with w given
    obtain ⟨ho,active,_,_,_,cost⟩ := given
    simpa only [output,value_eq F.room.cutoff ho active] using cost
  exact le_of_tendsto (L.continuous.continuousAt.tendsto.comp scan).norm price

end YM.Integration.SharedIntrinsicWilsonGrid
