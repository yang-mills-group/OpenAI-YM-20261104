import YM.Integration.WilsonPhysicalRegisteredLocalAction
import YM.Integration.WilsonPhysicalLocalPlaquetteForest

/-! The actual free links of the Wilson forest at a fixed exterior. An internal
bond is conjugated by the same coarse colour at its two endpoints. This gives
a literal local Haar change of variables with the original Jacobian. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPhysicalRegisteredForestAction
open Lattice RG Wilson Tree MeasureTheory Set Metric PertExtension MSbar.Heath Precision OPE.Therm
open WilsonPhysicalAnchoredGauge WilsonPhysicalForestAnchor WilsonPhysicalLocalPlaquetteForest
open scoped Classical Topology
variable {G : Gauge} {c f : Side} {S : StepData c f}

private theorem draped (T : Forest S.ratio) (u : T.Slice G) : canoe T (T.drape u) = T.drape u := by
  have names : T.foldAt (T.drape u)=T.foldAt (1:Config G f) :=
    T.names _ _ (fun _ hi => T.on_tree _ ⟨_,hi⟩)
  have trivial (w : Walk) (o : Site f) : travel (1:Config G f) o w=1 := by
    induction w generalizing o with
    | nil => rfl
    | cons d w ih => rw [travel,ih]; unfold Step.read; split <;> simp
  have trans : T.foldAt (T.drape u)=1 := by
    rw [names]; funext i; unfold Forest.foldAt; rw [trivial,inv_one]; rfl
  unfold canoe; rw [trans]; funext e; simp [Lattice.gauge]

/-- A genuine unmodified forest integration variable, including its original
old environment, when the bond's endpoints have the same coarse parent. -/
theorem free (T : Forest S.ratio) (o : Site f) (D : ℕ)
    (period : 2*radius D S.ratio.count.val<f.val) (u : T.Slice G) {τ : ℝ} (pos : 0≤τ)
    (cold : T.drape u∈House.chilly (WilsonAxialWindow.cells o (radius D S.ratio.count.val)) τ)
    (e : T.Free) (tail : separation o e.val.1≤D) (head : separation o (e.val.1+step e.val.2)≤D)
    (internal : S.ratio.parent e.val.1=S.ratio.parent (e.val.1+step e.val.2)) :
    G.chord (u e) ≤ area D S.ratio.count.val*τ := by
  have paid := field (S:=S) T o D period (T.drape u) pos cold (1:G.El) e.val tail head
  have rot (U : Config G f) : rotate (1:G.El) U=U := by funext i; simp [rotate,Lattice.gauge]
  rw [rot,after_forest,draped] at paid
  simpa only [Lattice.gauge,foot,internal,G.chord_conj,T.off_tree u e] using paid

def cut (T : Forest S.ratio) (E : Finset T.Free) : T.Slice G ≃ᵐ (↥E → G.El) × (({i : T.Free | i∉E}:Set T.Free) → G.El) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : T.Free => G.El) (·∈E)

def filled (T : Forest S.ratio) (E : Finset T.Free)
    (v : ({i : T.Free | i∉E}:Set T.Free) → G.El) (x : ↥E→G.El) : Config G f :=
  T.drape ((cut T E).symm (x,v))

/-- The local free-link Haar integral is exactly the Lie-algebra integral on
the physical cold event. All complementary free links are the prescribed v.
The signed measurable a may depend on all links. -/
theorem integral (J : Voice G) (clear : Clear G J) (P : ChartRatio G) (hp : LocalRatio P)
    (T : Forest S.ratio) (E : Finset T.Free) (o : Site f) (D : ℕ)
    (period : 2*radius D S.ratio.count.val<f.val) {τ r : ℝ} (pt : 0≤τ) (pr : 0<r) (sr : r<Chart.small G P)
    (small : area D S.ratio.count.val*τ≤J.δ) (bound : J.C*(area D S.ratio.count.val*τ)<r)
    (locality : ∀e∈E, separation o e.val.1≤D ∧ separation o (e.val.1+step e.val.2)≤D ∧
      S.ratio.parent e.val.1=S.ratio.parent (e.val.1+step e.val.2))
    (v : ({i : T.Free | i∉E}:Set T.Free) → G.El) (a : Config G f→ℝ) (meas : Measurable a) :
    let good := House.chilly (G:=G) (WilsonAxialWindow.cells o (radius D S.ratio.count.val)) τ
    let Φ := fun x : ↥E→G.El => good.indicator a (filled T E v x)
    (∫ x, Φ x ∂Chart.physical G (↥E)) =
      ∫x in ball 0 r, Chart.jacobian P x*Φ (Chart.expLinks G (↥E) x) ∂Chart.tangent G (↥E) := by
  dsimp only
  let good := House.chilly (G:=G) (WilsonAxialWindow.cells o (radius D S.ratio.count.val)) τ
  let Φ := fun x : ↥E→G.El => good.indicator a (filled T E v x)
  have mfill : Measurable (filled T E v) := T.continuous_drape.measurable.comp
    ((cut T E).symm.measurable.comp (measurable_id.prodMk measurable_const))
  have mΦ : Measurable Φ := (meas.indicator (House.bath _)).comp mfill
  have chart (x : ↥E→G.El) (cold : filled T E v x∈good) : x∈Chart.chamber G (↥E) r := by
    intro e _
    obtain ⟨tail,head,internal⟩ := locality e.val e.property
    let u := (cut T E).symm (x,v)
    have h := free T o D period u pt cold e.val tail head internal
    have read := congrFun (congrArg Prod.fst ((cut T E).apply_symm_apply (x,v))) e
    change u e.val=x e at read
    rw [read] at h
    have decoder := clear.near (x e) (h.trans small)
    refine ⟨J.decode (x e),?_,decoder.2.1⟩
    rw [mem_ball_zero_iff]
    exact decoder.2.2.trans_lt ((mul_le_mul_of_nonneg_left h (zero_le_one.trans clear.cost)).trans_lt bound)
  have restrict : (Chart.chamber G (↥E) r).indicator Φ=Φ := by
    funext x
    by_cases hx : x∈Chart.chamber G (↥E) r
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx]
      exact (Set.indicator_of_notMem (fun hc=>hx (chart x hc)) a).symm
  change (∫x, Φ x ∂Chart.physical G (↥E)) = _
  calc
    _ = ∫x in Chart.chamber G (↥E) r, Φ x ∂Chart.physical G (↥E) := by
      rw [← integral_indicator (Chart.Ratio.chamber_open hp sr.le).measurableSet,restrict]
    _ = _ := Chart.Ratio.chamber_integral hp Φ mΦ sr pr

end YM.Integration.WilsonPhysicalRegisteredForestAction
