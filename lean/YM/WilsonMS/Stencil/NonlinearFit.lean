import YM.WilsonMS.Stencil.InkTensor
/-!
# The same field with **all** nonlinear momentum vertices

True even when evaluated off-shell. In addition to ensuring highest rank at
birth before any induction (including components with more potential fields
from the nonlinearity), useful for consumers verifying compatibility with
analytic $g0$ sections on smooth tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.AllJets
open Function Filter Set MeasureTheory
open Analysis Tensor TPath Source Paths TaylorRules PlaneGauge Panel Extract MS Plane Heat Flux
open Landau Arts Pilot Tone Tone.Frame Local.BV Mach Motif Halo Native Cylinder Lab Draft
open Native.Sew Koszul Orient Book Land XSpace Webs Packet Wire RGerm PacketInk Lifting
open Complex (I)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {H : Hol G} {n k m : ℕ} {p : Labels.Label G n} (K : Survey G H n)

def OnConn : Set (Shore G 0) :=
  range (@vectorD G)

lemma allowed (w : Shore G 0) : w ∈ OnConn ↔ ∃ i a, w.1 = at_g (chair 0 i) a := by
  constructor
  rintro ⟨v, rfl⟩
  exact ⟨_, _, rfl⟩
  rintro ⟨i, a, ha⟩
  exact ⟨(i, a, w.2), Prod.ext ha.symm rfl⟩

lemma ferry_conn {W : Type} [Fintype W] (K : W → Lattice.Edge Lattice.Cover) (V : Cyl (W × Conn G) ℂ) :
    Uses OnConn (Tone.run (Ferry (knot K) V)) := by
  have hp (F : Cyl (W × Conn G) ℂ) : Uses OnConn (Tone.run (Ferry (knot K) F)) := by
    unfold Tone.run
    rw [show shade paywave (Ferry (knot K) F) = _ from study ..]
    let T := fun (i : Shore G 0) j => paywave i (knot K j)
    change Uses _ (shade T F)
    intro l i hi hh
    induction l generalizing F with
    | nil => cases hi
    | cons j l ih =>
      rw [deriv_lum T j F (s := Finset.univ)
          (show Uses (↑(Finset.univ : Finset (W × Conn G)) : Set _) F.val from
            (by simp [Uses.entire]))]
      apply Finset.sum_eq_zero
      intro r _
      rcases List.mem_cons.mp hi with hz | h
      · subst i
        rw [show T j r = 0 from ?_, zero_mul]
        exact
          Classical.byContradiction fun hv =>
            hh ((allowed _).mpr ⟨_, _, in_light j (knot K r) hv⟩)
      rw [ih (enter r F) h, mul_zero]
  exact hp V
lemma symbol_U (p : Labels.Pol G) : Uses (OnConn) (Tone.run (Webs.symbol K p)) := by
  rw [Webs.symbol, map_add, map_smul]
  exact (ferry_conn _ _).add ((ferry_conn _ _).smul _)

private lemma seed_M (i : Axis) (a : G.ColorIndex) : Uses OnConn (Motif.A 0 G (chair 0 i) a) := by
  intro l p hp hv
  match l with
  | [] => simp at hp
  | [j] =>
    have hh : p = j := by simpa using hp
    change ite (j.1 = at_g _ _) (1 : ℂ) 0 = 0
    rw [if_neg (fun hx => (hh ▸ hv) ((allowed _).mpr ⟨_, _, hx⟩))]
  | _ :: _ :: _ => rfl

private lemma axis_M (i : Axis) (F : Mield G 0) (j : G.ColorIndex) (h : Uses OnConn (F j)) :
    Uses OnConn (axisP (chair 0 i) F j) := by
  intro l p hp hv
  rw [show axisP _ _ _ l = _ from moon (δ _) _ l, h l p hp hv, mul_zero]

private lemma jaw_M (U F : Mield G 0) (j : G.ColorIndex) (hx : ∀ i, Uses OnConn (U i))
    (h : ∀ i, Uses OnConn (F i)) : Uses OnConn (jaw G 0 U F j) := by
  rw [chew]
  exact Uses.sum fun i _ => Uses.sum fun j _ => ((hx i).pair (h j)).smul _

private lemma beam_U (i : ℕ) (x : E4) (a b : Axis) (j : G.ColorIndex) :
    Uses OnConn (JRad.rayF 1 x a b i j) := by
  induction i generalizing j with
  | zero =>
    rw [JRad.rayF, pow_zero, Module.End.one_apply, cur, one_smul]
    exact
      ((axis_M a _ _ (seed_M b j)).sub (axis_M b _ _ (seed_M a j))).add
        (jaw_M _ _ _ (seed_M a) (seed_M b))
  | succ i ih =>
    rw [JRad.rayF, pow_succ']
    let F := JRad.rayF 1 x a b i (n := 0) (G := G)
    change Uses _ (JRad.direction G 0 1 x F j)
    rw [JRad.direction, LinearMap.sum_apply, Finset.sum_apply]
    refine Uses.sum fun k _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, convoke, LinearMap.add_apply, LinearMap.smul_apply,
      one_smul]
    exact ((axis_M k _ _ (ih j)).add (jaw_M _ _ _ (seed_M k) ih)).smul _

private lemma antennaU (v : Labels.Key G) : Uses OnConn (JRad.member v 1 0) := by
  have hx (z : Probe G) : Uses OnConn (JRad.factor G v.1 (linear_part G v.1 z) 1 0) := by
    rw [linear_part, JRad.corresponding, JRad.node, Pi.smul_apply, Finset.sum_apply]
    exact (Uses.sum (fun i _ => (beam_U _ _ i _ _).smul ((z.1 i) : ℂ))).smul (JRad.volume v.1 : ℂ)
  unfold JRad.member
  rw [← ray_eq v, Finsupp.sum, map_sum, Finset.sum_apply, Finset.sum_apply]
  refine Uses.sum (fun i _ => ?_)
  rw [map_smul]
  exact (hx i).smul (((ray_basis v) i) : ℂ)

lemma ms_U (p : Labels.Pol G) : Uses OnConn (JRad.optic G p 1 0) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [JRad.constV]
    rintro (_ | l) i hi h
    cases hi
    rfl
  | add f g h hh =>
    simp only [map_add, Pi.add_apply]
    exact h.add hh
  | mul_X f a h =>
    rw [JRad.productV, JRad.names]
    exact h.pair (antennaU a)

private lemma by_power (F : ℝ → ℂ) (h : Smooth F) (c : ℂ)
    (hp : Agree n 0 (fun t : ℝ => t ^ m • F t) (fun t : ℝ => t ^ n • c)) : Rest F ((n : ℤ) - m) c := by
  have hv (j : ℕ) : ContDiffAt ℝ (↑j) F 0 := contDiffAt_infty.mp h.contDiffAt j
  have he := hp.along_line le_rfl
  rw [power_bill (hv _), power_top contDiffAt_const] at he
  refine ⟨h, fun hi => ?_, fun i hi => ?_⟩
  · rw [if_neg (by omega)] at he
    exact smul_eq_zero_iff_right (M := ℂ) (by positivity) |>.mp he.symm
  split
  · rename_i hh
    rw [if_pos (by omega)] at he
    have ha : m ≤ n := by omega
    have hx : ((n.factorial : ℝ)) = ((n - m).factorial : ℝ) * (n.choose m * (m.factorial : ℝ)) := by
      rw [← Nat.choose_mul_factorial_mul_factorial ha]
      push_cast
      ring
    have hm := smul_right_injective (M := ℂ) (show (n.factorial : ℝ) ≠ 0 by positivity)
    refine hm ?_
    change ((n.factorial : ℝ)) • (((i.factorial : ℝ)⁻¹) • iteratedDeriv i F 0) = _
    dsimp only
    rw [← he, ← Nat.cast_smul_eq_nsmul ℝ, hx, show i = n - m by omega, smul_smul, smul_smul]
    congr 1
    field_simp
  rename_i hh
  have ha := hp.along_line (k := i + m) (by omega)
  rw [power_bill (hv _), power_bill contDiffAt_const, if_pos (by omega), if_neg (by omega)] at ha
  have ht : (((i + m).choose m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  rw [← Nat.cast_smul_eq_nsmul ℝ] at ha
  rw [Plane.reading, show iteratedDeriv i F 0 = 0 from ?_, smul_zero]
  exact
    (Nat.add_sub_cancel i m ▸
      (smul_eq_zero.mp (smul_eq_zero.mp ha |>.resolve_left ht) |>.resolve_left (by positivity)))

section packet
variable {ι : Type} [Fintype ι] (B : ι → PairK G) (l : List ι)

lemma printed {C : Dot G Lattice.Cover} (V : ℝ × Inputs ι → ℂ) (h : Smooth V)
    (hv : ∀ t : ℝ, scPar cosine sine l V (t, 0)= (t : ℂ) ^ l.length * Tone.run C (l.map (wordI B t)))
    (ht : ∀ z, Agree n 0 (fun t => V (t,z)) (fun t : ℝ=> t ^ n • unread (trial B z) p.val)) :
    Rest (fun t : ℝ => Tone.run C (l.map (wordI B t))) ((n : ℤ) - l.length)
      (JRad.optic G p.val 1 0 (l.map (packet B))) := by
  let F := fun z : Inputs ι => unread (trial B z) p.val
  let W (z : ℝ × Inputs ι) := z.1 ^ n • F z.2
  have he := print_readout B p.val
  have hF : Smooth F := he.smooth
  have hw : Smooth W := (contDiff_fst.pow _).smul (hF.comp contDiff_snd)
  have hp := attends (u := cosine) (v := sine) (f := V) h hw n (fun i => ht i) l 0
  let L (t : ℝ) := Tone.run C (l.map (wordI B t))
  have hb (t : ℝ) : scPar cosine sine l V (t, 0) = t ^ List.length l • L t := by
    rw [Complex.real_smul, Complex.ofReal_pow]
    exact hv t
  let c := JRad.optic G p.val 1 0 (l.map (packet B))
  have hc (t : ℝ) : scPar cosine sine l W (t, 0) = t ^ n • c := by
    change scans _ _ ((t ^ n : ℝ) • F) l 0 = _
    rw [show ((t ^ n : ℝ) • F) = (((t ^ n : ℝ) : ℂ)) • F from rfl, scale_s hF, Pi.smul_apply,
      show scans cosine sine F l 0 = _ from he.reads l]
    rfl
  change
    Agree n 0 (fun t => scPar cosine sine l V (t, 0)) (fun t => scPar cosine sine l W (t, 0)) at hp
  rw [funext hb, funext hc] at hp
  exact by_power L (smooth_ink B C l) c hp

lemma portrait (ht : p ∈ Labels.Grade (n, k)) :
    Rest (fun t : ℝ => Tone.run (Webs.symbol K p.val) (l.map (wordI B t))) ((n : ℤ) - l.length)
      (JRad.optic G p.val 1 0 (l.map (packet B))) :=
  printed B l _ (smoke B K p.val) (fun t => crystal B K p.val l t)
    (fun z => Wilson_top (A := trial B z) p K ht (forever B z))
omit [Fintype ι] in
lemma momentum_scale {C : Dot G Lattice.Cover}
    (h : Rest (fun t : ℝ => Tone.run C (l.map (wordI B t))) ((n : ℤ) - l.length)
      (JRad.optic G p.val 1 0 (l.map (packet B)))) :
    Rest (fieldVal (Tone.run C) (ray (l.map (packet B))))
      ((n : ℤ) - fieldDim wfield (l.map (packet B))) (JRad.optic G p.val 1 0 (l.map (packet B))) := by
  have he : fieldDim wfield (l.map (packet B)) = l.length := by
    unfold fieldDim
    simp only [List.map_map]
    clear h
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [ih]
      change (1 : ℤ) + _ = _
      omega
  rw [he, show fieldVal (Tone.run C) (ray (l.map (packet B))) = _ from ?_]
  exact h
  ext1 t
  unfold fieldVal
  rw [ray_go, List.map_map]
  rfl
lemma motto (ht : p ∈ Labels.Grade (n, k)) :
    Rest (fieldVal (Tone.run (Webs.symbol K p.val)) (ray (l.map (packet B))))
      ((n : ℤ) - fieldDim wfield (l.map (packet B))) (JRad.optic G p.val 1 0 (l.map (packet B))) :=
  momentum_scale (p:=p) B l (portrait K B l ht)
end packet

lemma vertex_checks {C : Dot G Lattice.Cover} (ht : Uses OnConn (Tone.run C))
    (hv : ∀ {ι : Type} [Fintype ι] (B : ι → PairK G) (l : List ι),
      Rest (fieldVal (Tone.run C) (ray (l.map (packet B))))
        ((n : ℤ) - fieldDim wfield (l.map (packet B))) (JRad.optic G p.val 1 0 (l.map (packet B))))
    (l : List (Shore G 0)) : Rest (fieldVal (Tone.run C) (ray l)) ((n : ℤ) - fieldDim wfield l)
      (JRad.optic G p.val 1 0 l) := by
  by_cases h : ∀ i ∈ l, i ∈ OnConn
  · let L := l.toFinset
    let T := ↥L
    have hx (i : T) : ∃ y : PairK G, vectorD y = i.val := h i (List.mem_toFinset.mp i.property)
    let B (i : T) := (hx i).choose
    let D := fun i : { i : Shore G 0 // i ∈ l } => B (⟨i.val, List.mem_toFinset.mpr i.property⟩ : T)
    have hp : l.attach.map (packet D) = l := by
      rw [show packet D = fun i => i.val from funext fun i => (hx _).choose_spec]
      exact List.attach_map_subtype_val _
    have he := hv D l.attach
    rwa [hp] at he
  push Not at h
  obtain ⟨j, hj, hu⟩ := h
  rw [ms_U p.val l j hj hu, show fieldVal (Tone.run C) (ray l) = _ from ?_]
  exact Rest.zero _
  funext t
  unfold fieldVal
  rw [ray_go]
  let f (z : Shore G 0) := (z.1, t • z.2)
  exact
    ht (l.map f) (f j) (List.mem_map_of_mem hj)
      (fun hv => hu ((allowed _).mpr ((allowed (f j)).mp hv)))

/-- After beam testing (`portrait`), see also the nonlinear contributions. -/
lemma top_rest (ht : p ∈ Labels.Grade (n, k)) (l : List (Shore G 0)) :
    Rest (fieldVal (Tone.run (Webs.symbol K p.val)) (ray l)) ((n : ℤ) - fieldDim wfield l)
      (JRad.optic G p.val 1 0 l) := by
  refine vertex_checks (p:=p) (symbol_U K p.val) ?_ l
  intro X _ B l
  exact motto K B l ht

/-- Any field, *any dynamical rank*. Pure slot number k only governs
which label is emitted and the Laurent factor. -/
theorem classical_jet (ht : p ∈ Labels.Grade (n, k)) (r : ℕ) :
    Fits (Webs.symbol K p.val) (Book.mask (r : ℤ) (JRad.optic G p.val 1 0)) r n false := by
  intro w _
  by_cases hx : w.length = r
  · convert top_rest K ht w using 1
    · funext t
      exact Book.enough _ (by simp only [sail_len, ray_len, hx])
    · exact Book.enough _ (by rw [hx])
  rw [strange w (by omega), show fieldVal (Book.mask _ _) (ray w) = _ from ?_]
  exact Rest.zero _
  funext t
  exact
    Book.strange _
      (by
        simp only [sail_len, ray_len]
        omega)
end YM.WilsonMS.AllJets
