import YM.WilsonMS.Columns.MarkChoice
/-!
# Highest rank through MS matching lattice-side arbor

Rank saturation survives the tree part of the flow, but the highest
engineering jet at that rank does NOT receive any contribution: both
vertices must have sufficient engineering weight. Kernel entries can
connect total field dimension less than four in the bookkeeping here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.StrictRank
open MS Function Filter Finset Set MeasureTheory Metric
open Plane Koszul Heat Flux Landau Lattice Tone Momentum Real Frame Wire Color Detect Native
  Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal Cylinder Lab Draft Wind Wind.Leading Menus Lifting
  LoopRank
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {q v : ℤ} {p : Team} {F A : Dec G} (x t : ℝ) {X H : Law G}
  {u V w : List (Lane4 G)} {h U i j k : ℕ}

abbrev riseH (F : Law G) (r : ℕ) (q : ℤ) (b : Bool) :=
  ∀ (l : List (Lane4 G)),
    l.length = r → Course b l → ∃ c : ℂ, Rest (fieldVal F (ray l)) (q - fieldDim wfield l) c

lemma R_build {X : ℝ → ℂ} (h : ContDiff ℝ ∞ X) (hv : ∀ i : ℕ, (i : ℤ) < v → reading i X = 0) :
    ∃ c, Rest X v c := by
  rcases lt_or_ge v 0 with he | he
  · exact ⟨0, h, fun _ => rfl, fun i hi => by omega⟩
  lift v to ℕ using he
  refine ⟨reading v X, h, (fun i => by omega), fun i hi => ?_⟩
  split
  congr
  omega
  apply hv
  omega

lemma BulkP (h : PC G p F) (hp : G.Simple) (i : ℕ) (hx : i ≥ 1) : riseH (F i x t) (i + 2) 4 true := by
  by_cases he : i = 1
  · subst i
    intro v hv ht
    rw [show fieldVal (F 1 x t) (ray v) = fieldVal (Top G) (ray v) from ?_]
    exact ⟨_, bulk_three hp _ ht⟩
    rw [← (first_top h x).2 t]
    funext z
    exact
      (enough (F := F 1 x t) (sail (ray v) z)
          (by
            rw [sail_len, ray_len, hv]
            norm_num)).symm
  intro v hv ht
  refine R_build (((h.owes i).stay x).joint.routine _ _) (fun m hm => ?_)
  have hL := Detect.length_pay v
  omega

lemma kernel_at (u v : BH G) (ht : 4 ≤ wfield u + wfield v) (p : QP) : Cpu G x u v p = 0 := by
  rcases u with ⟨⟨_ | a, _ | _⟩, g⟩ <;> rcases v with ⟨⟨_ | a, _ | _⟩, b⟩ <;>
      dsimp only [Cpu, LegsK, Landau.choir, L0] <;>
    (first
      | (solve
          | norm_num [wfield, dim] at ht)
      | (split <;> rfl))

private lemma axis_net (v : List (Lane4 G)) (s : ℝ) : net (sail (ray v) s) = s • net v := by
  induction v with
  | nil => exact (smul_zero s).symm
  | cons i v ih =>
    rw [show sail (ray (i :: v)) s = (i.1, s • i.2) :: sail (ray v) s from rfl, net_cons, ih,
      net_cons, smul_add]

private lemma lowerR (h : v < q) {f : ℝ → ℂ} {c : ℂ} (hp : Rest f q c) : Rest f v 0 := by
  refine ⟨hp.smooth, fun _ => rfl, fun i hi => ?_⟩
  rw [hp.home i (hi.trans h.le), if_neg ((lt_of_le_of_lt hi h).ne)]
  simp

private lemma chars (v : List (Lane4 G)) (s : ℝ) :
    degree (field parity) (sail (ray v) s) = degree (field parity) v := by
  induction v <;> simp_all [ray, sail]

lemma inkR (hp : pays i X) (hv : pays j H) (ht : riseH X i 4 true) (hh : riseH H j q false)
    (he : i + j = k + 2) (a b : BH G) (hU : Split u V w) (hr : w.length = k) :
    Rest (fun s : ℝ => radius parity (Cpu G t) a b X H (sail (ray u) s) (sail (ray V) s))
      (q - fieldDim wfield w) 0 := by
  by_cases hy : u.length + 1 = i
  swap
  · have ht := split_length hU
    by_cases hz : u.length + 1 > i
    · rw [show (fun s : ℝ => _) = (fun _ => (0 : ℂ)) from ?_]
      exact Rest.zero _
      funext s
      unfold radius
      dsimp only
      rw [hp _ (fun hw => ?_)]
      simp
      have hh := hw.smaller
      rw [List.length_cons, sail_len, ray_len] at hh
      omega
    have hZ : V.length + 1 > j := by omega
    rw [show (fun s : ℝ => _) = (fun _ => (0 : ℂ)) from ?_]
    exact Rest.zero _
    funext s
    unfold radius
    dsimp only
    rw [hv _ (fun hw => ?_)]
    simp
    have hh := hw.smaller
    rw [List.length_cons, sail_len, ray_len] at hh
    omega
  have hl : V.length + 1 = j := by
    obtain hv := split_length hU
    omega
  let E := (a, -net u) :: u
  let Y := (b, net u) :: V
  let U (s : ℝ) := Cpu G t a b (-(s • net u))
  have hw : ContDiff ℝ ∞ U :=
    (City.main_f G a b).comp (f := fun s : ℝ => (t, -(s • net u))) (by fun_prop)
  obtain ⟨c, hc⟩ :=
    ht E hy
      (by
        intro _
        unfold E
        rw [net_cons]
        exact neg_add_cancel _)
  obtain ⟨d, hd⟩ := hh Y hl (fun v => Bool.noConfusion v)
  let D := field (P := QP) (parity (A := Axis) (C := G.ColorIndex))
  let z : ℂ := cross (Landau.parity b) (degree D u)
  rw [show
      (fun s : ℝ => radius parity _ a b X H (sail (ray u) s) (sail (ray V) s)) = fun s : ℝ =>
        (((2 : ℂ) * U s) * (z * fieldVal X (ray E) s)) * fieldVal H (ray Y) s
      from ?_]
  swap
  · funext s
    unfold radius
    simp_rw [axis_net u s, chars, neg_neg]
    rw [show (a, -(s • net u)) :: sail (ray u) s = sail (ray E) s from ?_]
    rfl
    unfold E
    rw [← smul_neg]
    rfl
  by_cases hm : 4 ≤ wfield a + wfield b
  · rw [show U = (fun _ => 0) from funext fun s => kernel_at t a b hm _]
    simp only [mul_zero, zero_mul]
    exact Rest.zero _
  let Hr := (((Rest.level hw rfl).smul 2).mul (hc.smul z)).mul hd
  apply lowerR _ Hr
  have hl : fieldDim wfield u + fieldDim wfield V = fieldDim wfield w := by
    obtain he := split_perm hU
    simpa [fieldDim, Function.comp_def] using (he.map (fun x : Lane4 G => wfield x.1)).sum_eq
  rw [show fieldDim wfield E = wfield a + fieldDim wfield u from rfl,
    show fieldDim wfield Y = wfield b + fieldDim wfield V from rfl]
  omega

lemma post_m (hp : pays i X) (hv : pays j H) (ht : riseH X i 4 true) (hh : riseH H j q false)
    (he : i + j = k + 2) (hr : w.length = k) :
    Rest (fieldVal (tree parity (Cpu G t) X H) (ray w)) (q - fieldDim wfield w) 0 := by
  let D := field (P := QP) (parity (A := Axis) (C := G.ColorIndex))
  let T (s : ℝ) (l r : List (Lane4 G)) :=
    attaches parity (Cpu G t) X H (sail (ray l) s) (sail (ray r) s)
  have hz :
    Rest (fun s : ℝ => scatter D w (T s)) (q - fieldDim wfield w)
      (scatter D w (0 : Shared (Lane4 G) ℂ)) := by
    apply Rest.scattered
    intro l r hl
    unfold T
    simp_rw [convertR (Vrev G t)]
    have hh :=
      Rest.sum (Finset.univ : Finset (BH G))
        (fun b (_ : b ∈ Finset.univ) =>
          Rest.sum (Finset.univ : Finset (BH G))
            (fun a (_ : a ∈ Finset.univ) => inkR t hp hv ht hh he b a hl hr))
    simpa only [Finset.sum_const_zero] using! hh
  rw [show fieldVal (tree _ _ _ _) _ = _ from ?_]
  exact (show scatter D w (0 : Shared (Lane4 G) ℂ) = 0 from map_zero (allocate D w)) ▸ hz
  funext s
  unfold fieldVal tree T
  simp_rw [ray_go]
  exact scatter_move _ (fun i : Lane4 G => (i.1, s • i.2)) (fun _ => rfl) w
end YM.WilsonMS.StrictRank
