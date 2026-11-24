import YM.XSpace.Bare
import YM.MS.Wilson.Energy
import YM.MS.Wilson.Gauge
import YM.MS.Bare.Running
import YM.WilsonMS.Top.Darboux

/-!
# The finite, based ghost prescription on the inversion quotient

Choose root `T.root`. Based gauge is the **subgroup**, not the
sum-zero vector-space slice (which needn't be a Lie subalgebra). We remove
the constant gauge in this way even though it takes some extra work later
to compare with Landau's ghost / zero-mode convention. Only one term per
edge orbit in the action-inner-product conventions. The local identities
here are adaptations of `YM/MS/Wilson/Gauge.lean` to these rooted *orbit*
coordinates (especially relevant for the vertices at fixed points of the
inversion).
-/

set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Root
open XSpace Period Lattice Function Filter Set Finset
open MS MS.Bare MS.Bare.Focus MS.Bare.Maurer MS.Koszul MS.Cylinder MS.Cylinder.Taylor MS.Native
open Darboux
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace

variable {P : Period} (T : P.Tree) (G : Gauge)

abbrev LogSpace (P : Period) :=
  P.Link → G.Color

abbrev LinksI (P : Period) :=
  P.Link × G.ColorIndex

abbrev LieParameters :=
  T.Nonroot → G.Color

abbrev GhostI :=
  T.Nonroot × G.ColorIndex

abbrev Mode :=
  Letters (LinksI G P) (GhostI T G)

abbrev dg :=
  Darboux.parity (E := LinksI G P) (U := GhostI T G)

abbrev pairs :=
  Darboux.ports (LinksI G P) (GhostI T G)

def chartFocus : Focus (pairs T G) (LinksI G P) (GhostI T G) :=
  ⟨Equiv.refl _, fun _ => rfl, fun _ => rfl⟩

def direction : Mode T G → LogSpace G P
  | .inl (.inl i) => Native.priv i
  | _ => 0

def coordinates : Glow (chartFocus T G) (LogSpace G P)
    where
  e0 := direction T G
  seed := Native.projector
  restore v := Native.frame v
  ever
    i := by
    rcases i with (i | i) | (i | i) <;>
      (first
        | exact fun _ => ⟨_, rfl⟩
        | exact fun h => (h rfl).elim)

def based : LieParameters T G →ₗ[ℝ] (P.Vertex → G.Color)
    where
  toFun v x := if h : x ≠ T.root then v ⟨x, h⟩ else 0
  map_add' v w := by
    funext x
    by_cases hx : x = T.root <;> simp [hx]
  map_smul' t v := by
    funext x
    by_cases hx : x = T.root <;> simp [hx]

lemma based_braid (v w : LieParameters T G) :
    based T G (Native.braid v w) = Native.braid (based T G v) (based T G w) := by
  funext x
  by_cases he : x = T.root
  · simp [based, he, Native.braid]
  simp [based, Native.braid, he]

def endsMap (e : P.Link) : LieParameters T G →ₗ[ℝ] Maurer.Ends G :=
  ((LinearMap.proj (P.src e)).prod (LinearMap.proj (P.dst e))).comp (based T G)

def velocity (a : LogSpace G P) : LieParameters T G →ₗ[ℝ] LogSpace G P :=
  LinearMap.pi fun e : P.Link => (Maurer.voltage (a e)).comp (endsMap T G e)

def localVector (k : GhostI T G) (a : LogSpace G P) :=
  velocity T G a (Native.priv k)

lemma value_local (i : GhostI T G) (a : LogSpace G P) (e : P.Link) :
    localVector T G i a e = Maurer.volts (endsMap T G e (Native.priv i)) (a e) :=
  rfl

private lemma smooth (u : GhostI T G) : germ (localVector T G u) := by
  refine contDiffAt_pi.mpr (fun i => ?_)
  exact
    (show germ (Maurer.volts (endsMap T G i (Native.priv u))) from Maurer.home _).comp (f :=
      fun a : LogSpace G P => a i) 0 (contDiff_apply .. |>.contDiffAt)

private lemma vector_diff (u : GhostI T G) (a v : LogSpace G P) (x : P.Link)
    (h : DifferentiableAt ℝ (localVector T G u) a)
    (he : DifferentiableAt ℝ (Maurer.volts (endsMap T G x (Native.priv u))) (a x)) :
    fderiv ℝ (localVector T G u) a v x =
      fderiv ℝ (Maurer.volts (endsMap T G x (Native.priv u))) (a x) (v x) := by
  let X : LogSpace G P →L[ℝ] G.Color := ContinuousLinearMap.proj x
  let V := Maurer.volts (endsMap T G x (Native.priv u))
  have hv : X ∘ localVector T G u = V ∘ X := rfl
  have ht := fderiv_comp a X.differentiableAt h
  rw [hv, fderiv_comp a (show DifferentiableAt ℝ V (X a) from he) X.differentiableAt, X.fderiv,
    X.fderiv] at ht
  exact DFunLike.congr_fun ht.symm v

lemma site_bracket (i j : GhostI T G) :
    ∀ᶠ a in 𝓝 0,
      fderiv ℝ (localVector T G j) a (localVector T G i a) -
          fderiv ℝ (localVector T G i) a (localVector T G j a) =
        ∑ k : GhostI T G, Native.colorTerm G T.Nonroot i j k • localVector T G k a := by
  obtain ⟨r, hr, H⟩ := LocalH.geom_patch G
  filter_upwards [eventually_all.mpr
      (fun e : P.Link =>
        (show ∀ᶠ a : LogSpace G P in 𝓝 0, a e ∈ Metric.ball 0 r from
          (continuous_apply (A := fun _ : P.Link => G.Color) e |>.tendsto
                (0 : LogSpace G P)).eventually
            (Metric.ball_mem_nhds _ hr))),
    (smooth T G i).eventually (by simp), (smooth T G j).eventually (by simp)] with a ha hI hJ
  have he :
    ∑ k : GhostI T G, Native.colorTerm G T.Nonroot i j k • localVector T G k a =
      velocity T G a (Native.braid (Native.priv i) (Native.priv j)) := by
    rw [← Native.crowd, map_sum]
    simp only [map_smul]
    rfl
  rw [he]
  funext x
  rw [Pi.sub_apply,
    vector_diff T G j a _ x (hJ.differentiableAt (by simp))
      ((Maurer.analytic_volts _ (H r (le_refl r)) (ha x)).differentiableAt (by simp)),
    vector_diff T G i a _ x (hI.differentiableAt (by simp))
      ((Maurer.analytic_volts _ (H r (le_refl r)) (ha x)).differentiableAt (by simp)),
    value_local, value_local, Maurer.storm _ _ (H r (le_refl r)) (ha x)]
  unfold velocity Maurer.volts endsMap
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, based_braid]
  rfl

lemma site_lie : Vibes (Native.colorTerm G T.Nonroot) (localVector T G) :=
  ⟨Native.cartan _ _, smooth T G, site_bracket T G⟩

/-- The Haar log input *once per orbit*. -/
def orbitLog (a : LogSpace G P) :=
  ∑ e : P.Link, Maurer.lac (a e)

lemma orbit_germ : germ (orbitLog G (P := P)) :=
  ContDiffAt.sum fun i _ =>
    (Maurer.hlog G).comp (f := fun a : LogSpace G P => a i) (0 : LogSpace G P)
      (contDiff_apply .. |>.contDiffAt)

private lemma log_deriv {a v : LogSpace G P}
    (h : ∀ i : P.Link, DifferentiableAt ℝ (Maurer.lac (G := G)) (a i)) :
    fderiv ℝ (orbitLog G (P := P)) a v = ∑ i : P.Link, fderiv ℝ Maurer.lac (a i) (v i) := by
  let T i : LogSpace G P →L[ℝ] G.Color := ContinuousLinearMap.proj i
  have hh i := (h i).hasFDerivAt.comp (f := ⇑(T i)) a (T i).hasFDerivAt
  rw [show fderiv ℝ (orbitLog G) a = _ from (HasFDerivAt.fun_sum fun i _ => hh i).fderiv]
  simp
  rfl

private lemma trace_quotient (i : GhostI T G) :
    ∀ᶠ a : LogSpace G P in 𝓝 0,
      Focus.index_div (coordinates T G) (localVector T G i) a =
        ∑ e : P.Link, Maurer.divs (Maurer.volts (endsMap T G e (Native.priv i))) (a e) := by
  let V (x : P.Link) := Maurer.volts (endsMap T G x (Native.priv i))
  filter_upwards [(smooth T G i).eventually (by simp),
    eventually_all.mpr
      (fun x : P.Link =>
        (continuous_apply x |>.tendsto (0 : LogSpace G P)).eventually
          ((Maurer.home (endsMap T G x (Native.priv i))).eventually (by simp)))] with
    a ha he
  unfold Focus.index_div
  rw [Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Maurer.by_row]
  apply Finset.sum_congr rfl
  intro k _
  have hd : DifferentiableAt ℝ (localVector T G i) a := ha.differentiableAt (by simp)
  change
    fderiv ℝ (Native.projector (x, k) ∘ localVector T G i) _ (Native.priv (x, k)) =
      fderiv ℝ (V x) (a x) (baseC k) k
  rw [fderiv_comp a (projector (x, k)).differentiableAt hd, (projector (x, k)).fderiv,
    ContinuousLinearMap.comp_apply, projector_k]
  rw [vector_diff T G i a _ _ hd ((he x).differentiableAt (by simp))]
  simp [priv, V]

lemma density_identity : Focus.Bills (coordinates T G) (localVector T G) (orbitLog G) := by
  intro i
  filter_upwards [trace_quotient T G i,
    eventually_all.mpr
      (fun x : P.Link =>
        (continuous_apply x |>.tendsto (0 : LogSpace G P)).eventually
          ((Maurer.wind_div (endsMap T G x (Native.priv i))).and
            ((Maurer.hlog G).eventually (by simp))))] with
    a ha h
  change index_div _ _ a + fderiv ℝ (orbitLog G) a (localVector T G i a) = 0
  rw [ha, log_deriv G (fun i => (h i).2.differentiableAt (by simp)), ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => (h j).1

def raised (a : LogSpace G P) : P.Array G :=
  G.lieExp ∘ a

def rotation (i : GhostI T G) (t : ℝ) (a : LogSpace G P) (e : P.Link) : G.El :=
  Maurer.step (endsMap T G e (Native.priv i)) (a e) t

lemma rotation_gauge (i : GhostI T G) (t : ℝ) (a : LogSpace G P) :
    rotation T G i t a =
      P.act (fun x => (G.lieExp (t • based T G (Native.priv i) x))⁻¹) (raised G a) := by
  funext e
  unfold rotation Period.act Maurer.step
  rw [Next.SectorChange.exp_negative, inv_inv]
  rfl

def nearby (u : GhostI T G) (a : LogSpace G P) (t : ℝ) : LogSpace G P := fun e =>
  G.plog (G.mat (rotation T G u t a e))

lemma tangent_germ (u : GhostI T G) (a : LogSpace G P) {s : Set G.Color} {U : Set G.El}
    (h : LocalH.Geom G U s) (he : ∀ i, a i ∈ s) :
    nearby T G u a 0 = a ∧
      HasDerivAt (nearby T G u a) (localVector T G u a) 0 ∧
        (∀ᶠ t : ℝ in 𝓝 0, raised G (nearby T G u a t) = rotation T G u t a) := by
  unfold nearby rotation
  refine ⟨funext (fun e => ?_), hasDerivAt_pi.mpr (fun i => Maurer.amp _ h (he i)), ?_⟩
  · rw [Maurer.step_start]
    exact snap_on h (he e)
  filter_upwards [eventually_all.mpr
      (fun i : P.Link => Maurer.walk_on (endsMap T G i (Native.priv u)) h (he i))] with
    t ht
  funext i
  exact h.2.2.2.1 (ht i)

lemma inert_of_invariant (f : P.Array G → ℝ)
    (hx : ∀ k : P.Vertex → G.El, k T.root = 1 → ∀ U, f (P.act k U) = f U) (h : germ (f ∘ raised G)) :
    Inert (localVector T G) (f ∘ raised G) := by
  intro i
  obtain ⟨r, hr, H⟩ := LocalH.geom_patch G
  filter_upwards [h.eventually (by simp),
    eventually_all.mpr
      (fun e : P.Link =>
        (continuous_apply e |>.tendsto (0 : LogSpace G P)).eventually
          (Metric.ball_mem_nhds (0 : G.Color) hr))] with
    a ha hh
  obtain ⟨he, hy, hg⟩ := tangent_germ T G i a (H r (le_refl r)) hh
  have ht :
    HasDerivAt ((f ∘ raised G) ∘ nearby T G i a) (fderiv ℝ (f ∘ raised G) a (localVector T G i a))
      0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 (ha.differentiableAt (by simp) |>.hasFDerivAt) hy he.symm
  refine
    ((ht.congr_of_eventuallyEq (f₁ := fun _ => f (raised G a)) (hg.mono fun t ht => ?_)).unique
      (hasDerivAt_const ..))
  dsimp only [Function.comp_apply]
  rw [ht, rotation_gauge, hx _ ?_]
  simp [based]

end YM.WilsonMS.Root
