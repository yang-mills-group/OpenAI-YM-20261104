import YM.FVA2.ProfilePower
import YM.FVA2.ThePitch
import YM.PhysMS.Frame.Faces
import YM.RG11Proof.Neighborhood.Features

/-! The independent MS momentum prescription of the chosen FVA2 warehouse
defines the RG11 correlation report on the same physical label tower. Its
separated point and profile queries evaluate the original continuum kernels. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPEMSReport
open Function Set MeasureTheory FVA2 FVA2.ColorCode Pert.Position
open MS MS.Land MS.Menus MS.Theater MS.Book MS.Book.Program
open RG11.Fields RG11.Grove RG11.Neighborhood
open scoped Topology BigOperators ContDiff Classical

variable {G : Gauge} (V : Warehouse G) {Q : Booked (wings G)}
  (M : MS_Data G Q) (μ : ℝ)

/-- The horizon inclusion used by the MS panel is the RG11 inclusion on
the quotient by the free-field relations. -/
theorem same_rise {d e : ℕ} (h : d ≤ e) :
    RG11.Fields.up V.F h = PositionX.up V.F h := by
  apply LinearMap.ext
  intro v
  apply Extra.FD.writes_inj V.F e
  rw [RG11.Fields.up_write, Fountain.common_L V, Fountain.common_L V]
  exact (Maxwell.Free.address_rise V.F _ h v).symm

/-- Complex linearity in the full joint test, for the actual momentum-scheme bank. -/
def tests (k d n : ℕ) :
    Test n →ₗ[ℂ] MultilinearMap ℂ (fun _ : Fin n => E V.F d) ℂ where
  toFun := Spring.ms V M μ d k n
  map_add' a b := by
    ext1 v
    change Spring.ms V M μ d k n (a + b) v =
      Spring.ms V M μ d k n a v + Spring.ms V M μ d k n b v
    simp only [Spring.invoice, Test.applyTo, _root_.add_apply, add_mul]
    exact integral_add (Spring.payable V M μ a v k) (Spring.payable V M μ b v k)
  map_smul' c a := by
    ext1 v
    change Spring.ms V M μ d k n (c • a) v = c • Spring.ms V M μ d k n a v
    simp only [Spring.invoice, Test.applyTo, _root_.smul_apply, smul_eq_mul,
      mul_assoc, integral_const_mul]

def report : ShapeReport G V.F where
  table := tests V M μ
  maxwell d n f v := by
    change Spring.ms V M μ d 0 n f v = _
    rw [Spring.vintage_ms]
    rfl
  packs d e n k h f v := by
    change Spring.ms V M μ d k n f v = Spring.ms V M μ e k n f
      (RG11.Fields.up V.F h ∘ v)
    rw [same_rise, Spring.invoice, Spring.invoice]
    exact f.apply_eq (fun x _ => (Fountain.tower V M e μ v h k x).symm)

theorem report_test (k d n : ℕ) (f : Test n) (v : Fin n → E V.F d) :
    (report V M μ).table k d n f v =
      f.applyTo (fun x => Fountain.phys V M μ k x d v) :=
  Spring.invoice V M μ f v k

/-- The smooth-representative premise for the RG11 OPE extractor holds at
every coupling order, arity, and field horizon of this MS prescription. -/
theorem metered : Metered (report V M μ) := by
  intro d k n z
  let v := (tower V.F d).b ∘ z
  exact ⟨fun x => Fountain.phys V M μ k x d v,
    Spring.smoothShape V M μ v k, fun f => report_test V M μ k d n f v⟩

variable {n m i d : ℕ}

/-- The ordered labels of the two OPE clusters in their common horizon. -/
def jointLabels (u : sheaf V.F n i) (v : sheaf V.F m d) :
    Fin (n+m) → E V.F (max i d) :=
  (tower V.F (max i d)).b ∘ Fin.append (rise V.F (le_max_left i d) ∘ u)
    (rise V.F (le_max_right i d) ∘ v)

/-- Every RG11 point, derivative or test functional on the joint cluster
reads the declared smooth kernel of the retained independent MS prescription. -/
theorem link_coeff (q : leverage (n+m)) (u : sheaf V.F n i) (v : sheaf V.F m d)
    (k : ℕ) :
    PowerSeries.coeff k (link (report V M μ) i d q u v) =
      q (RG11.Stress.dress (fun x =>
        Fountain.phys V M μ k x (max i d) (jointLabels V u v))
        (Spring.smoothShape V M μ (jointLabels V u v) k)) :=
  link_integrates (report V M μ) i d k u v q _ _ (fun f =>
    report_test V M μ k (max i d) (n+m) f (jointLabels V u v))

theorem front_point (x : conf n) (y : Tail m) (s : ℝ)
    (hx : driven (Real.exp (-s)) x.val y ∈ conf (n+m))
    (u : sheaf V.F n i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (frontRow (report V M μ) i d (.inl x) y s u v) =
      Fountain.phys V M μ k (driven (Real.exp (-s)) x.val y) (max i d)
        (jointLabels V u v) := by
  unfold frontRow Design.taps
  rw [link_coeff, here_at _ hx]

theorem front_test (f : Test n) (y : Tail m) (s : ℝ)
    (hf : ∀ x ∈ tsupport f, driven (Real.exp (-s)) x y ∈ conf (n+m))
    (u : sheaf V.F n i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (frontRow (report V M μ) i d (.inr f) y s u v) =
      f.applyTo (fun x => Fountain.phys V M μ k (driven (Real.exp (-s)) x y)
        (max i d) (jointLabels V u v)) := by
  simp only [frontRow, Design.taps, dif_pos hf]
  rw [link_coeff, Design.scoop_at]

theorem close_conf (y : Tail m) : close y ∈ conf (1+m) := by
  apply coupled_conf
  · exact fun _ _ _ => Subsingleton.elim ..
  · exact Points.tail_in y.apart
  · intro _ j he
    apply Fin.succ_ne_zero j
    apply y.apart
    change Points.cons _ _ j.succ = Points.cons _ _ 0
    simpa [Points.cons] using he.symm

/-- The replacement row also uses the original MS kernel for every chosen
output label, exterior field tuple, and joint separated geometry. -/
theorem back_point (y : Tail m) (a : lab V.F i) (v : sheaf V.F m d) (k : ℕ) :
    PowerSeries.coeff k (backRow (report V M μ) i d y a v) =
      Fountain.phys V M μ k (close y) (max i d)
        (jointLabels V (fun _ : Fin 1 => a) v) := by
  change PowerSeries.coeff k (link (report V M μ) i d (here (close y))
    (fun _ : Fin 1 => a) v) = _
  rw [link_coeff, here_at _ (close_conf y)]

section Physical

open Filter Spec PhysMS
variable {C : Family G} {f : Extraction.Order} {S : Table C.book}
  (F : Final C f S) (J : ℝ → PhysMS.tower S) (H : Leading F J)
  (hC : C.Makes) (hV : ∀ h, Bid.pop (C.localSection h))

include H

/-- At order zero the actual all-length comparison frame and the independent
MS prescription on the very same warehouse give the same smooth kernel,
including every fixed position derivative uniformly on separated compacts. -/
theorem physical_leading_jet {n d : ℕ} (v : Fin n → E C.labels d)
    (j : ℕ) (K : Set (Points n)) (hK : IsCompact K) (hsep : K ⊆ conf n) :
    TendstoUniformlyOn (fun r => iteratedFDeriv ℝ j
      (measured F none (J r) (d := fun _ : Fin n => d) v r))
      (iteratedFDeriv ℝ j (fun x => Fountain.phys (Atoll.share C hC hV) M μ 0 x d v))
      Trace.Pilot.trail K := by
  have ht := H.lead n (fun _ => d) v j K hK hsep
  apply (Metric.tendstoUniformlyOn_iff).mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with r hr x hx
  have he : (fun z => Fountain.phys (Atoll.share C hC hV) M μ 0 z d v) =ᶠ[𝓝 x]
      WickGoal (C := C) (d := fun _ : Fin n => d) v := by
    filter_upwards [(conf_open n).mem_nhds (hsep hx)] with z hz
    exact DFunLike.congr_fun (Fountain.vintage (Atoll.share C hC hV) M μ z hz) v
  rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
  exact hr x hx

open OPE OPE.Orbits Trace.Pilot

/-- For any multi-insertion compact separated profile, the ordinary
physical Reader's scalar-output OPE in this frame has the independently
computed MS zeroth coefficient in the continuum all-length limit. -/
theorem physical_scalar_leading
    (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (hR : Foundation F R) (hG : G.Simple) (X : Climb.Scaling S)
    {n d : ℕ} (v : Fin n → E C.labels d) (K : Set (Points n))
    (hK : IsCompact K) (hsep : K ⊆ conf n) :
    TendstoUniformlyOn (fun r x => Short.scalar F R (r • x).ofLp
      (Orbits.tags (Frame.born (d := fun _ : Fin n => d) J r v)) 0)
      (fun x => Fountain.phys (Atoll.share C hC hV) M μ 0 x d v)
      trail K := by
  obtain ⟨a,ha,b,hb,hroom⟩ := compact_within K hK hsep
  have hp : Tendsto (fun r : ℝ => r ^ ((4 : ℝ)-1)) trail (𝓝 0) :=
    (length_rate.rpow (4-1)).tends (by norm_num) to_log_zoom
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hε' := half_pos hε
  have hhead := Frame.singleton_head (F := F) (R := R) (J := J) (H := H)
    (h := hR) (v := v) (M := a) (η := b) (ε := 1) (hM := ha) (hη := hb)
    (he := zero_lt_one) (hg := hG) (X := X)
  filter_upwards [hhead, hp.eventually (ge_mem_nhds hε'),
    Frame.all_leading F R J H hG X hR 0 v K hK hsep (ε/2) hε']
    with r hr hpow hlead x hx
  have he : Fountain.phys (Atoll.share C hC hV) M μ 0 x d v = WickGoal
      (C := C) (d := fun _ : Fin n => d) v x :=
    DFunLike.congr_fun (Fountain.vintage (Atoll.share C hC hV) M μ x (hsep hx)) v
  rw [he, dist_comm, dist_eq_norm]
  apply (norm_sub_le_norm_sub_add_norm_sub _ (measured F none (J r) v r x) _).trans_lt
  calc
    _ < ε/2 + ε/2 := by
      apply add_lt_add_of_le_of_lt
      · rw [norm_sub_rev]
        exact (hr x (hroom x hx) none).trans hpow
      specialize hlead x hx none
      rwa [show iteratedFDeriv ℝ 0 (measured F none (J r) v r) x -
          iteratedFDeriv ℝ 0 (WickGoal v) x =
          iteratedFDeriv ℝ 0 (measured F none (J r) v r - WickGoal v) x
          by ext z; simp, norm_iteratedFDeriv_zero] at hlead
    _ = ε := add_halves ε

end Physical

end YM.Integration.OPEMSReport
