import YM.WilsonMS.Regulator.HoldCycles
/-!
# Log-polynomial time budget on fully pinned glades
Keep the polynomial property uniform over ALL momenta, not just separated
limits at each point. Good on each compact position scope. We expose this in
the Logarithm bookkeeping system. Argument does not need exchanging badly divergent limit
and Taylor extraction; evaluate in slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.TraceMC
open Function Set Filter MeasureTheory Real Finset Metric
open MS MS.Plane MS.Latch MS.Latch.Job MS.Koszul MS.Landau MS.Landau.Detect MS.Land
open MS.Rake MS.Orbit MS.Vane MS.Heat MS.Tone MS.City MS.Book MS.Dock MS.Emit MS.Outlook
open MS.Local.Physical MS.Osc MS.Osc.Snap MS.Tide MS.Dial MS.Logarithm Wire Belt Geo Flux
open scoped Topology Classical
variable {G : Gauge} {I : Type} {A : Deck G} {M : Booked A} {n m k : ℕ}
section poly

variable {F : Type} [MeasurableSpace F] (g : ℝ → I → F → ℂ) (μ : I → Measure F)

lemma ready_int (hp : Ready g) (he : ∀ i x, Integrable (g i x) (μ x)) :
    Ready (fun i : ℝ => fun p : I => ∫ x, g i p x ∂μ p) := by
  obtain ⟨n, h⟩ := hp
  let Y i (p : I) := ∫ x, g i p x ∂μ p
  have ht (p : ℝ) : Y p = Logarithm.evaluate n Y p := by
    funext i
    unfold Y Logarithm.evaluate
    conv_lhs =>
      rw [Logarithm.interpret h p]
      unfold Logarithm.evaluate
      simp only [Finset.sum_apply, Pi.smul_apply]
    simp_rw [Finset.sum_apply]
    rw [integral_finsetSum _
        (fun j _ => show Integrable (fun x => (plate n j).eval p • g j i x) (μ i) from
          (he j i).smul ((plate n j).eval p))]
    simp_rw [integral_smul]
    rfl
  rw [show (fun i : ℝ => fun p : I => ∫ x, g i p x ∂μ p) = _ from funext ht]
  exact eval_ready ..
end poly

abbrev Rates (I : Type) :=
  ℝ × I

abbrev Tℓ (G : Gauge) :=
  List (Lane4 G)
variable {F H : Glade G (Rates I)} {τ φ : Tℓ G → Prop}

def along (F : Glade G (Rates I)) : ℝ → (I → ℝ → Law G) := fun μ p => F (μ, p)

def allLn (τ : Tℓ G → Prop) (F : Glade G (Rates I)) :=
  Ready (fun μ : ℝ => fun p : I × ℝ × { l : Tℓ G // τ l } => F (μ, p.1) p.2.1 p.2.2.val)

lemma all_add (h : allLn τ F) (hv : allLn τ H) : allLn τ (F + H) :=
  Ready.add h hv

lemma above (h : Ready (along F)) : allLn τ F := by
  let L : (I → ℝ → Law G) →ₗ[ℝ] (I × ℝ × { x // τ x } → ℂ) :=
    LinearMap.pi fun p => LinearMap.proj p.2.2.val ∘ₗ LinearMap.proj p.2.1 ∘ₗ LinearMap.proj p.1
  exact h.linear L

lemma complete (hp : allLn τ F) (h : ∀ l, τ l) : Ready (along F) := by
  let A := (I × ℝ × { l : Tℓ G // τ l })
  let L : (A → ℂ) →ₗ[ℝ] (I → ℝ → Law G) :=
    LinearMap.pi fun i => LinearMap.pi fun x => LinearMap.pi fun l => LinearMap.proj (i, x, ⟨l, h l⟩)
  exact Ready.linear hp L

lemma integral (hp : allLn τ F) (ht : Latch.Job.train false F) : allLn τ (river F) :=
  ready_int (fun μ : ℝ => fun p : I × ℝ × { l : Tℓ G // τ l } => fun t => F (μ, p.1) t p.2.2.val)
    (fun p => volume.restrict (Set.Iic p.2.1))
    (Ready.linear hp
      (LinearMap.pi fun (p : I × ℝ × { l : Tℓ G // τ l }) =>
        LinearMap.pi fun (i : ℝ) => LinearMap.proj (p.1, i, p.2.2)))
    (fun μ p => ht (μ, p.1) _ _ (fun i => Bool.noConfusion i))
set_option quotPrecheck false
local notation "μ0" => (fun _ : Rates I => planeF)
local notation "Z0" => Geo.constantP G (Rates I) (PlanetD G)

lemma cost_Θ (H : ∀ x : Rates I, ∀ t, SatC planeF (PlanetD G t) (F x t) false) (hp : allLn τ F)
    (he : ∀ i j : Lane4 G, ∀ x : Tℓ G, φ x → τ (i :: j :: x)) : allLn φ (sailP μ0 Z0 F) := by
  let T := I × ℝ × { l : Tℓ G // τ l }
  let V := I × ℝ × { l : Tℓ G // φ l }
  let g (i : ℝ) (v : T) := F (i, v.1) v.2.1 v.2.2.val
  let f (i : ℝ) (p : V) (q : QP) := trc (PlanetD G p.2.1) q (F (i, p.1) p.2.1) p.2.2.val
  apply
    ready_int (g := f) (μ := fun _ => planeF) _
      (fun i p => H (i, p.1) p.2.1 p.2.2.val (fun i => Bool.noConfusion i))
  let R (p : V) (q : QP) (i j : BH G) : T :=
    (p.1, p.2.1, ⟨(i, q) :: (j, -q) :: p.2.2.val, he _ _ _ p.2.2.property⟩)
  let A (u : V) (q : QP) (i j : BH G) : (T → ℂ) →ₗ[ℝ] ℂ :=
    ((LinearMap.mulLeft ℂ (PlanetD G u.2.1 i j q)).restrictScalars ℝ).comp
      (LinearMap.proj (R u q i j))
  let L : (T → ℂ) →ₗ[ℝ] (V → QP → ℂ) :=
    LinearMap.pi fun u => LinearMap.pi fun q => ∑ i, ∑ j, A u q i j
  have hh : f = (fun i => L (g i)) := by
    funext i p q
    change f i p q = (∑ i, ∑ j, A p q i j) _
    unfold f
    simp only [at_trc, LinearMap.sum_apply]
    rfl
  rw [hh]
  exact Ready.linear hp L

lemma tree_g (h : Ready (along F)) (he : Ready (along H)) : Ready (along (expJ Z0 F H)) := by
  let M := (I → ℝ → Law G)
  let L : M →ₗ[ℝ] M →ₗ[ℝ] M :=
    { toFun
        x :=
        LinearMap.pi fun p =>
          LinearMap.pi fun t =>
            ((Heat.boulevard Landau.parity (PlanetD G t) (x p t)).restrictScalars ℝ) ∘ₗ
              LinearMap.proj t ∘ₗ LinearMap.proj p
      map_add' x
        y :=
        LinearMap.ext fun z =>
          funext fun i =>
            funext fun t =>
              (_root_.map_add ((Heat.boulevard Landau.parity (PlanetD G t)).flip (z i t)) (x i t)
                (y i t))
      map_smul' a
        x :=
        LinearMap.ext fun z =>
          funext fun i =>
            funext fun t =>
              (_root_.map_smul
                (((Heat.boulevard Landau.parity (PlanetD G t)).flip (z i t)).restrictScalars ℝ) a
                (x i t)) }
  exact Ready.pair L h he

lemma polyp_in {Y : I → QP} (hp : Ready (along F)) (hx : Ready (along H))
    (ht : ∀ (v : Rates I) (t : ℝ), SatP planeF (PlanetD G t) (F v t) (H v t) (Y v.2)) :
    Ready (along (regionC μ0 (Y ∘ Prod.snd) Z0 F H)) := by
  let U := (I × ℝ × BH G × BH G × Tℓ G × Tℓ G)
  let A (v : ℝ) (u : U) (q : QP) :=
    Tone.bill (Y u.1) q *
      meshZ (PlanetD G u.2.1) u.2.2.1 u.2.2.2.1 (F (v, u.1) u.2.1) (H (v, u.1) u.2.1) u.2.2.2.2.1
        u.2.2.2.2.2 q
  let g (v : ℝ) (u : U) := ∫ q, A v u q ∂planeF
  have he : Ready g := by
    let P := (U → QP → ℂ)
    apply
      ready_int A (fun _ => planeF) _
        (fun v u => ht (v, u.1) u.2.1 u.2.2.1 u.2.2.2.1 u.2.2.2.2.1 u.2.2.2.2.2)
    let M := (I → ℝ → Law G)
    let K (p : U) (q : QP) : ℂ :=
      Tone.bill (Y p.1) q *
        (2 * PlanetD G p.2.1 p.2.2.1 p.2.2.2.1 q *
          cross (Landau.parity p.2.2.2.1) (Koszul.degree (field Landau.parity) p.2.2.2.2.1))
    let X : M →ₗ[ℝ] P :=
      LinearMap.pi fun u =>
        LinearMap.pi fun q =>
          ((LinearMap.mulLeft ℂ (K u q)).restrictScalars ℝ) ∘ₗ
            LinearMap.proj ((u.2.2.1, q) :: u.2.2.2.2.1) ∘ₗ LinearMap.proj u.2.1 ∘ₗ LinearMap.proj u.1
    let B : M →ₗ[ℝ] P :=
      LinearMap.pi fun p =>
        LinearMap.pi fun i =>
          LinearMap.proj ((p.2.2.2.1, -i) :: p.2.2.2.2.2) ∘ₗ
            LinearMap.proj p.2.1 ∘ₗ LinearMap.proj p.1
    rw [show A = (fun v => X (along F v) * B (along H v)) from ?_]
    exact Ready.pair (Algebra.lmul ℝ P).toLinearMap (hp.linear X) (hx.linear B)
    funext v p q
    change A v p q = (K p q * _) * _
    unfold A meshZ K
    ring_nf
    rfl
  let D := (U → ℂ)
  let Aℓ (i : I) (t : ℝ) (l r : Tℓ G) : D →ₗ[ℝ] ℂ :=
    ((LinearMap.mulLeft ℂ (Tone.bill (Y i) (net l))).restrictScalars ℝ).comp
      (∑ a : BH G, ∑ b : BH G, LinearMap.proj (i, t, a, b, l, r))
  let X (i : I) (t : ℝ) : D →ₗ[ℝ] Shared (Lane4 G) ℂ :=
    LinearMap.pi fun l => LinearMap.pi fun r => Aℓ i t l r
  let K : D →ₗ[ℝ] (I → ℝ → Law G) :=
    LinearMap.pi fun i =>
      LinearMap.pi fun t =>
        LinearMap.pi fun w => ((allocate (field Landau.parity) w (R := ℂ)).restrictScalars ℝ) ∘ₗ X i t
  have hm : along (regionC μ0 (Y ∘ Prod.snd) Z0 F H) = fun i => K (g i) := by
    funext i p t l
    change scatter _ l _ = scatter _ l _
    apply congr_arg (scatter _ l)
    funext l r
    change
      _ =
        (Tone.bill (Y p) _) *
          ((∑ a : BH G,
              ∑ b : BH G, LinearMap.proj (R := ℝ) (φ := fun _ => ℂ) (⟨p, t, a, b, l, r⟩ : U))
            _)
    simp_rw [LinearMap.sum_apply]
    rfl
  rw [hm]
  exact he.linear _
end YM.WilsonMS.TraceMC
