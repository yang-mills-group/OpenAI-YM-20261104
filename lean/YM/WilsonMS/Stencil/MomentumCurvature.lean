import YM.WilsonMS.Stencil.PacketField
/-!
# Evaluate momentum partials on continuum fields

This checks against the *supplied MS conventions* not another free tower.
Body rows can depend on x in this proof. Derivative shift from this exact
position factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Packet
open Function Filter Set MeasureTheory
open Analysis Tensor TPath Source Paths TaylorRules PlaneGauge Panel Extract MS Plane Heat Flux
open Landau Arts Pilot Tone Local.BV Mach Motif Halo Native Koszul
open Complex (I)
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {ι : Type} [Fintype ι] (B : ι → PairK G)

abbrev coordinates (ι : Type) :=
  E4 × Inputs ι

abbrev Θ (G : Gauge) (x : E4) (H : Rack G 0) (l : Legs (Shore G 0)) :=
  eip (net l) x * H l

structure AtVertex (F : coordinates ι → ℂ) (H : Rack G 0) : Prop where
  smooth : Smooth F
  read : ∀ l : List ι, ∀ x : E4, scPar cosine sine l F (x, 0) = Θ G x H (l.map (packet B))
variable {B} {F G' : coordinates ι → ℂ} {H K : Rack G 0}
namespace AtVertex

lemma add (h : AtVertex B F H) (hh : AtVertex B G' K) : AtVertex B (F + G') (H + K) := by
  refine ⟨h.smooth.add hh.smooth, fun l x => ?_⟩
  let q (z : Inputs ι) := (x, z)
  change scans cosine sine (F ∘ q + G' ∘ q) l 0 = _
  rw [sum2
      (h.smooth.comp (f := q)
        (by
          unfold q
          fun_prop))
      (hh.smooth.comp (f := q)
        (by
          unfold q
          fun_prop)),
    Pi.add_apply, show scans cosine sine (F ∘ q) l 0 = _ from h.read l x,
    show scans cosine sine (G' ∘ q) l 0 = _ from hh.read l x]
  simp only [Θ, Pi.add_apply, mul_add]

lemma smul (c : ℂ) (h : AtVertex B F H) : AtVertex B (c • F) (c • H) := by
  refine ⟨h.smooth.const_smul c, fun l x => ?_⟩
  let f := F ∘ (fun z : Inputs ι => (x, z))
  change scans cosine sine (c • f) l 0 = (eip _ x) * (c * _)
  rw [scale_s (h.smooth.comp (by fun_prop)), Pi.smul_apply,
    show scans cosine sine f l 0 = _ from h.read l x, smul_eq_mul]
  exact mul_left_comm ..

lemma sub (h : AtVertex B F H) (hh : AtVertex B G' K) : AtVertex B (F - G') (H - K) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_one_smul ℂ G', ← neg_one_smul ℂ K]
  exact h.add (hh.smul _)

lemma zero (B : ι → PairK G) : AtVertex B 0 0 :=
  ⟨contDiff_const, fun l x => by
    change scans cosine sine (0 : Inputs ι → ℂ) l 0 = (eip _ _) * 0
    rw [sc_zero, mul_zero]
    rfl⟩

lemma sum {X : Type} {F : X → coordinates ι → ℂ} {H : X → Rack G 0} (s : Finset X)
    (h : ∀ i ∈ s, AtVertex B (F i) (H i)) : AtVertex B (∑ i ∈ s, F i) (∑ i ∈ s, H i) := by
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact AtVertex.zero _
  | insert b s he ih =>
    rw [Finset.sum_insert he, Finset.sum_insert he]
    exact (h b (Finset.mem_insert_self ..)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Theta_k (x : E4) (H K : Rack G 0) (l) :
    bite 0 G (Θ G x H) (Θ G x K) l = Θ G x (bite 0 G H K) l := by
  let S := JRad.ZK G 0
  have he (i : Shore G 0) (F : Rack G 0) : Koszul.D i (Θ G x F) = eip i.2 x • Θ G x (Koszul.D i F) := by
    funext y
    simp only [at_D, Θ, net_cons, mul_p, Pi.smul_apply, smul_eq_mul]
    ring
  have hx (i) (F : Rack G 0) : sign S i (Θ G x F) = Θ G x (sign S i F) := by
    funext l
    simp only [at_sign, Θ]
    ring
  change product S (Θ G x H) (Θ G x K) l = Θ G x (product S H K) l
  induction l generalizing H K with
  | nil =>
    change times _ _ _ [] = Θ G x (times S H K) []
    simp only [times_nil, Θ]
    simp [net, eip]
  | cons i l ih =>
    change _ = eip _ x * (product S H K) (i :: l)
    rw [D_eval _ (product S _ _), D_product,
      show (product S H K) (i :: l) = _ from D_eval i (product S H K) l, D_product, Pi.add_apply,
      Pi.add_apply, he, he, hx, map_smul, LinearMap.smul_apply, map_smul, Pi.smul_apply,
      Pi.smul_apply, ih, ih, net_cons, mul_p]
    unfold Θ
    simp only [smul_eq_mul]
    ring

lemma product_read (h : AtVertex B F H) (hh : AtVertex B G' K) : AtVertex B (F * G') (bite 0 G H K) := by
  refine ⟨h.smooth.mul hh.smooth, fun l x => ?_⟩
  let q (z : Inputs ι) : coordinates ι := (x, z)
  change scans cosine sine (F ∘ q * G' ∘ q) l 0 = _
  rw [← Theta_k]
  exact
    sc_times _ (packet B) (fun _ => rfl) (Θ G x H) (Θ G x K)
      (h.smooth.comp (f := q)
        (by
          unfold q
          fun_prop))
      (hh.smooth.comp (f := q)
        (by
          unfold q
          fun_prop))
      (fun j => h.read j x) (fun j => hh.read j x) l

lemma derive (i : Axis) (h : AtVertex B F H) :
    AtVertex B (fun z : coordinates ι => Analysis.D (basis i) (fun x : E4 => F (x, z.2)) z.1)
      (rowP (chair 0 i) H) := by
  let dV := Analysis.D (basis i, (0 : Inputs ι)) F
  have hp : (fun z : coordinates ι => Analysis.D (basis i) (fun x : E4 => F (x, z.2)) z.1) = dV :=
    funext fun x => by
      have he : HasFDerivAt (fun z : E4 => (z, x.2)) (ContinuousLinearMap.inl ℝ E4 (Inputs ι)) x.1 :=
        (hasFDerivAt_id _).prodMk (hasFDerivAt_const ..)
      exact
        DFunLike.congr_fun ((h.smooth.differentiable (by simp) x).hasFDerivAt.comp x.1 he).fderiv _
  refine ⟨?_, fun l x => ?_⟩
  · rw [hp]
    exact contDiff_iff_contDiffAt.mpr fun x => dSmooth h.smooth.contDiffAt _ (by simp)
  let w := l.map (packet B)
  have hx :
    scans cosine sine (fun z : Inputs ι => Analysis.D (basis i) (fun x => F (x, z)) x) l 0 =
      Analysis.D (basis i) (fun x : E4 => scPar cosine sine l F (x, 0)) x := by
    have hv := iterated h.smooth 1 (fun _ => basis i) l x (0 : Inputs ι) (u := cosine) (v := sine)
    unfold Analysis.D
    simp only [iteratedFDeriv_one_apply] at hv
    exact hv.symm
  change scans cosine sine (fun z : Inputs ι => _) l 0 = Θ G x _ w
  rw [hx,
    show (fun x : E4 => scPar cosine sine l F (x, 0)) = (fun x => eip (net w) x * H w) from
      funext fun x => h.read l x]
  have hu := d_p (net w) x i
  have he : (fun x : E4 => eip (net w) x * H w) = (H w) • eip (net w) := funext fun x => mul_comm ..
  rw [he]
  unfold Analysis.D at *
  rw [fderiv_const_smul (smooth_p _ |>.differentiable (by simp) x), _root_.smul_apply, hu, Θ, rowP,
    moon]
  simp only [smul_eq_mul]
  ring

variable (B)

lemma seed (a : Axis) (c : G.ColorIndex) :
    AtVertex B (fun x => (((trial B x.2 a x.1) c : ℝ) : ℂ)) (Motif.A 0 G (chair 0 a) c) := by
  refine
    ⟨Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (𝕜 := ℝ) c).contDiff.comp (trial_s B a)),
      fun l x => ?_⟩
  let f : Inputs ι →L[ℝ] ℂ := Complex.ofRealCLM ∘L ((EuclideanSpace.proj (𝕜 := ℝ) c) ∘L payload B a x)
  let z := packet B
  change
    scans cosine sine (f := ⇑f) l 0 = Θ G x (Motif.note (at_g (chair 0 a) c) (fun _ => 1)) (l.map z)
  cases l with
  | nil =>
    change f 0 = _ * 0
    rw [map_zero, mul_zero]
  | cons i l =>
    rw [scans]
    let m : ℂ := f (cosine i) + I * f (sine i)
    have hp : m = if (packet B i).1 = at_g (chair 0 a) c then eip (price B i) x else 0 :=
      paid B i a c x
    rw [show Extract.delta i _ _ (⇑f : Inputs ι → ℂ) = (fun _ => m) from
        funext fun x => by
          simp only [Extract.delta, Analysis.D, Pi.add_apply, Pi.smul_apply, f.fderiv]
          rfl,
      Extract.const]
    cases l with
    | nil =>
      rw [Θ, List.map_cons, List.map_nil, node1]
      simp only [net_cons]
      rw [show net ([] : List (Shore G 0)) = 0 from rfl, add_zero]
      change m = (eip _ x) * if _ then _ else _
      rw [hp]
      split_ifs <;> simp [*]
      rfl
    | cons j l => simp [Θ, note, coin, mono]
end AtVertex
end YM.WilsonMS.Packet
