import YM.Integration.OPETreeRemainder

/-! The original continuum frame realizes the entire multiweight tree
OPE against physical exteriors at comparable ultraviolet scales. A
single slowly shrinking relative radius can be used at every phase
and every sufficiently short outer length. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.OPETreePhysical
open Function Set Filter Asymptotics Trace.Pilot Spec PhysMS OPE OPE.Orbits
open FVA2 Pert.Position Maxwell Maxwell.Free MSbar.OPE RG11.Neighborhood OPETreeRemainder
open scoped Classical Topology BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (R : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hG : G.Simple) (X : Climb.Scaling S)
    (hR : Foundation F R) (hC : C.Makes) (hV : ∀ d, Bid.pop (C.localSection d))
    {Q : MS.Land.Booked (FVA2.ColorCode.wings G)} (M : MS.Land.MS_Data G Q) (μ : ℝ)
    {n m i d : ℕ}

theorem uniform_phases {Y : Type*} {l : Filter ℝ} (P : ℝ × Y → Prop) :
    (∀ᶠ a in comap Prod.fst l, P a) ↔ ∀ᶠ r in l, ∀ y, P (r,y) := by
  rw [eventually_comap]
  constructor
  · intro h; exact h.mono (fun r hr y => hr (r,y) rfl)
  · intro h
    filter_upwards [h] with r hr ⟨q,y⟩ he
    change q = r at he
    subst q
    exact hr y

def pair (p : Viewers F) (r : ℝ) (x : Points (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) : ℂ :=
  measured F p (J r) (d := fun _ : Fin (n+m) => max i d)
    (Fin.append (RG11.Fields.up C.labels (le_max_left i d) ∘ v)
      (RG11.Fields.up C.labels (le_max_right i d) ∘ w)) r x

include hJ hG X hR

theorem pair_limit (x : Points (n+m)) (hx : x ∈ conf (n+m))
    (v : Fin n → E C.labels i) (w : Fin m → E C.labels d) :
    Tendsto (fun a : ℝ × Viewers F => pair F J a.2 a.1 x v w) (comap Prod.fst trail)
      (𝓝 (paired (Atoll.share C hC hV) M μ 0 x v w)) := by
  let u := Fin.append (RG11.Fields.up C.labels (le_max_left i d) ∘ v)
    (RG11.Fields.up C.labels (le_max_right i d) ∘ w)
  have hn : paired (Atoll.share C hC hV) M μ 0 x v w = WickGoal (C := C)
      (d := fun _ : Fin (n+m) => max i d) u x :=
    DFunLike.congr_fun (Fountain.vintage (Atoll.share C hC hV) M μ x hx) u
  rw [hn]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  apply (uniform_phases _).mpr
  have hm := Frame.all_leading F R J hJ hG X hR 0
    (d := fun _ : Fin (n+m) => max i d) u {x} isCompact_singleton (singleton_subset_iff.mpr hx) ε hε
  filter_upwards [hm] with r hr p
  specialize hr x (mem_singleton x) p
  rw [show iteratedFDeriv ℝ 0 (measured F p (J r) u r) x -
    iteratedFDeriv ℝ 0 (WickGoal u) x =
      iteratedFDeriv ℝ 0 (measured F p (J r) u r - WickGoal u) x from by ext z; simp,
    norm_iteratedFDeriv_zero] at hr
  rw [dist_eq_norm]
  exact hr

variable (x : conf n) (y : Tail m) (v : Fin n → E C.labels i) (w : Fin m → E C.labels d)
    (weights : Fin n → ℕ) (H : ℕ)

def discrepancy (p : Viewers F) (r t : ℝ) : ℂ :=
  (t:ℂ)^(∑ a, weights a) * pair F J p r (driven t x.val y) v w -
    ∑ k ∈ Finset.range (H+1), (t:ℂ)^k *
      pair F J p r (close y) (fun _ : Fin 1 => output C.labels x v k) w

def treeDiscrepancy (t : ℝ) : ℂ :=
  (t:ℂ)^(∑ a, weights a) * paired (Atoll.share C hC hV) M μ 0 (driven t x.val y) v w -
    ∑ k ∈ Finset.range (H+1), (t:ℂ)^k *
      paired (Atoll.share C hC hV) M μ 0 (close y) (fun _ : Fin 1 => output C.labels x v k) w

theorem discrepancy_limit (t : ℝ) (ht : driven t x.val y ∈ conf (n+m)) :
    Tendsto (fun a : ℝ × Viewers F => discrepancy F J x y v w weights H a.2 a.1 t)
      (comap Prod.fst trail) (𝓝 (treeDiscrepancy hC hV M μ x y v w weights H t)) :=
  ((pair_limit F R J hJ hG X hR hC hV M μ _ ht v w).const_mul _).sub
    (tendsto_finsetSum _ fun k _ => (pair_limit F R J hJ hG X hR hC hV M μ _
      (OPEMSReport.close_conf y) (fun _ : Fin 1 => output C.labels x v k) w).const_mul _)

variable (hv : ∀ a, pureW scaleW (weights a) (polynomials C.labels i v a))
include hC hV M μ hv

/-- One power bound applies to the original table and all its phases.
The finite list of physical output fields is the same on every scale. -/
theorem two_scale :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ᶠ r in trail, ∀ p : Viewers F,
      ‖discrepancy F J x y v w weights H p r t‖ ≤ K*t^(H+1) := by
  have hs := ray_remainder (Atoll.share C hC hV) M μ x y v w weights hv H
  obtain ⟨B,hB,hb⟩ := hs.exists_nonneg
  refine ⟨B+1, by linarith, ?_⟩
  filter_upwards [hb.bound, self_mem_nhdsWithin,
    (contracts (x := x.val) y.c y.y (exterior_apart y)).filter_mono nhdsWithin_le_nhds]
    with t ht htpos hfar
  have htpos' : 0 < t := htpos
  have hpow := pow_pos htpos' (H+1)
  have ho : driven t x.val y ∈ conf (n+m) :=
    combination (safe x.property y.c htpos') (Points.tail_in y.apart) hfar
  have hp := Metric.tendsto_nhds.mp (discrepancy_limit F R J hJ hG X hR hC hV M μ x y
    v w weights H t ho) _ hpow
  filter_upwards [(uniform_phases _).mp hp] with r hr p
  have hd := hr p
  rw [dist_eq_norm] at hd
  rw [Real.norm_eq_abs, abs_of_pos hpow] at ht
  let D := discrepancy F J x y v w weights H p r t
  let T := treeDiscrepancy hC hV M μ x y v w weights H t
  change ‖D-T‖ < _ at hd
  change ‖T‖ ≤ _ at ht
  calc
    ‖D‖ ≤ ‖D-T‖ + ‖T‖ := norm_le_norm_sub_add D T
    _ ≤ t^(H+1)+B*t^(H+1) := add_le_add hd.le ht
    _ = _ := by ring

omit hC hV M μ hv hJ hG X hR in
/-- An all-length slow diagonal for eventually funded integer demands.
It retains the original small-length filter on its entire tail. -/
theorem slow_demand (P : ℕ → ℝ → Prop) (h : ∀ᶠ j : ℕ in atTop, ∀ᶠ r in trail, P j r) :
    ∃ a : ℝ → ℕ, Tendsto a trail atTop ∧ ∀ᶠ r in trail, P (a r) r := by
  obtain ⟨j,hj⟩ := eventually_atTop.mp h
  let cap := fun r : ℝ => ⌊r⁻¹⌋₊
  have hcap : Tendsto cap trail atTop := tendsto_nat_floor_atTop.comp tendsto_inv_nhdsGT_zero
  let P' := fun n r => P (j+n) r
  let a := fun r => Nat.findGreatest (fun n => P' n r) (cap r)
  have ha : Tendsto a trail atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [hj (j+k) (by omega), hcap.eventually_ge_atTop k] with r hp hmax
    exact Nat.le_findGreatest hmax hp
  refine ⟨fun r => j+a r, ?_, ?_⟩
  · exact tendsto_atTop.mpr fun k => (ha.eventually_ge_atTop k).mono (fun r hr => by omega)
  filter_upwards [hj j le_rfl] with r hr
  have hh : P' 0 r := by simpa only [P', Nat.add_zero] using hr
  exact Nat.findGreatest_spec (P := fun n => P' n r) (Nat.zero_le (cap r)) hh

/-- All phases obey the same power saving on a single shrinking
interior-to-exterior scale ratio, while the *full original continuum*
scale runs to zero. The ratio may depend on the fixed observation. -/
theorem simultaneous :
    ∃ K : ℝ, 0 < K ∧ ∃ ratio : ℝ → ℝ, Tendsto ratio trail (𝓝[>] 0) ∧
      ∀ᶠ r in trail, ∀ p : Viewers F,
        ‖discrepancy F J x y v w weights H p r (ratio r)‖ ≤ K*(ratio r)^(H+1) := by
  obtain ⟨K,hK,h⟩ := two_scale F R J hJ hG X hR hC hV M μ x y v w weights H hv
  let t := fun j : ℕ => 1 / ((j:ℝ)+1)
  have ht : Tendsto t atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun j => by
      change 0 < 1 / ((j:ℝ)+1); positivity)⟩
  obtain ⟨a,ha,had⟩ := slow_demand (fun j r => ∀ p : Viewers F,
    ‖discrepancy F J x y v w weights H p r (t j)‖ ≤ K*(t j)^(H+1)) (ht.eventually h)
  exact ⟨K,hK,t ∘ a,ht.comp ha,had⟩

end YM.Integration.OPETreePhysical
