import YM.LocalTaylorR2.Clutch

/-!
# Real representation after decorated integration

Fixed forest gauges. Do NOT claim unmasking or competing rank identities
after a change of representation. Pattern/Gio proof ported for local tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Port
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {W s μ C : ℝ} {R : Rep G f} {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}
variable {H : Cash W s μ L Q o C T R}
open PhysicalNext PhysicalNext.Repeat Greenbelt Channel Next.Foundations
variable {U:Support c} {p:Molecule S} {K : Test T}

/-- The conditional at a molecule. In the call use before mask and only for
geometrically permitted molecules. In particular, this does not imply
price at a non-Healthy configuration. -/
def onFrame (X:Coat T F) (p:Molecule S) (U:Support c) (K:Test T) := likely fun z:S.Choices=>
    average ((preps X (roster p)).taggedL z) (podium S G U X.B) K
def rinsed (X:Coat T F) (p:Molecule S) (U:Support c) (K:Test T) := ∫ z, onFrame (X.rinse z) p U K ∂(Measure.pi fun _:Site c=>G.probHaar)
def episode (H:Cash W s μ L Q o C T R) (χ:Chi) (p:Molecule S) (K:Test T) (V:Config G c):=
    likely fun i:Greenbelt.Reserve S => rinsed (prism T s χ o.K V (Greenbelt.allot i)) p (H.unionP p) K

variable (X:Coat T F) (hx : X.x=s) (hk : X.width=o.K) (hK : Kept H U K)
lemma frieze (p:Molecule S) : GaugeInvariant (fun V=> rinsed (vary X V) p U K) := by
  intro z V
  let f:= MeasurableEquiv.piCongrRight (fun i=> MeasurableEquiv.mulRight (z i))
  let D:=(Measure.pi fun _:Site c=>G.probHaar)
  have hp : MeasurePreserving f D D := measurePreserving_pi _ _ (fun i : Site c=> measurePreserving_mul_right G.probHaar (z i))
  let Y:= vary X V; dsimp only [rinsed]; rw [← hp.integral_comp' (fun z=> onFrame (Y.rinse z) p U K)]
  apply integral_congr_ae; filter_upwards with u; have ht : gauge u (gauge z V) = gauge (f u) V := by
    funext i; unfold Lattice.gauge; change _= (u _*z _)* V _* (u _*z _)⁻¹; group
  unfold vary rinse; simp_rw [ht]; rfl
include hx hk hK
lemma plantedRule (p:Molecule S) (V:Config G c) (hp : Healthy (Pressure.temp s) U X.V) (he:(roster p).flags=∅) (Y:S.Choices):
    average (vary ((planted X p).taggedL Y) V) (podium S G U (radiusB s)) K=average ((preps (vary X V) (roster p)).taggedL Y) (podium S G U (radiusB s)) K := by
  rw [← show X.B=radiusB s from congr_arg _ hx]
  let A:=vary ((planted X p).taggedL Y) V; let A':=(preps (vary X V) (roster p)).taggedL Y
  refine agreesVillage A hx hk hK U (Subset.refl _) (show Village A A' U from ?_)
  refine ⟨rfl,rfl,rfl,?_, fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
  intro i hi; have he':i∉ RG.flags (Pressure.temp X.x) X.V:= by rw [hx]; exact Finset.disjoint_left.mp hp hi
  unfold A A' vary taggedL planted preps place; simp [he,he']

lemma onFrameSites (p:Molecule S): Measurable (fun V=> onFrame (vary X V) p U K) ∧ LocalOn U (fun V=>onFrame (vary X V) p U K):= by
  constructor
  · let f z V:= average ((preps (vary X V) (roster p)).taggedL z) (podium S G U X.B) K
    have hf z:Measurable (f z):=by
      let L:=((preps X (roster p)).taggedL z)
      have hq V : (preps (vary X V) (roster p)).taggedL z=vary L V:=rfl
      unfold f; simp_rw [hq]; exact averageMeas L hx hk hK (podium S G U X.B)
    exact measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> hf i)
  intro V Z hu; apply congr_arg likely; funext i
  refine agreesVillage ((preps (vary X V) (roster p)).taggedL i) hx hk hK U (Subset.refl _) (show Village _ ((preps (vary X Z) (roster p)).taggedL i) U from ?_)
  exact ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,fun _ _=>rfl,hu⟩
lemma rinsedSites (p:Molecule S): Measurable (fun V=> rinsed (vary X V) p U K) ∧ LocalOn U (fun V=> rinsed (vary X V) p U K):= by
  obtain ⟨hm,hL⟩:= onFrameSites X hx hk hK p; constructor
  · have hp : Measurable fun (a:Config G c × (Site c → G.El))=> gauge a.2 a.1 := by
      refine measurable_pi_lambda _ fun i=> ?_; dsimp only [Lattice.gauge]; fun_prop
    exact ((hm.comp hp).stronglyMeasurable.integral_prod_right' (ν:=Measure.pi fun _ : Site c=> G.probHaar)).measurable
  intro V Z hu; apply integral_congr_ae; filter_upwards with z
  exact hL (gauge z V) (gauge z Z) (fun i hi hj=> by unfold Lattice.gauge; rw [hu i hi hj])

variable {A b r C' v B d:ℝ} {l j : ℕ} {χ : Chi} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {Ξ : Utopia H j v d r C' χ}
variable (h : Oboe H j v B l A b Ξ) (he : (roster p).flags=∅) (hp:X.χ=χ) (hy : Healthy (Pressure.temp s) U X.V) (hM : Mode V x j v) (hz : V x=X.V)
include h he hp hy hM hz
lemma formula :
    (fun y=> rinsed (vary X (V y)) p U K) =ᶠ[𝓝 x] fun y=> likely fun i:S.Choices=>
      average (vary ((planted X p).taggedL i) (V y)) (podium S G U (radiusB s)) K := by
  let Y t y:= vary ((planted X p).taggedL t) (V y); have ht:= H.laws.data
  have hf t: ∀ᶠ y in 𝓝 x,Hue (Y t y):= eventual_hue (h.flow F ((planted X p).taggedL t) hx hp hk (planted_valid X p) E V x hz hM)
    (ht.localP F ((planted X p).taggedL t) hx hk (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh
  let Z:= likely fun i:S.Choices=> average (Y i y) (podium S G U (radiusB s)) K
  change (∫ z, onFrame _ _ _ _ ∂_) = Z
  have hF z : onFrame ((vary X (V y)).rinse z) p U K=Z := by
    apply congr_arg likely; funext q
    let I:=podium S G U (radiusB s); change average ((preps (vary X (gauge z (V y))) (roster p)).taggedL q) (podium S G U X.B) K=average (Y q y) I K
    rw [show X.B=radiusB s from congr_arg _ hx,← plantedRule X hx hk hK p _ hy he]
    change average ((Y q y).rinse z) I _=average _ I _; unfold I; rw [← chargedU]
    exact rinseInvariant (Y q y) hx hk hK _ _ (hh q)
  -- exact, strong support unchanged
  change (∫ z, onFrame ((vary X (V y)).rinse z) p U K ∂_)=Z; simp_rw [hF]; simp

lemma priced {k':ℝ} (hm:IntegrandCost H U K j A v k' χ): Brush j k' 1 (fun y=> rinsed (vary X (V y)) p U K) x := by
  refine (?_ : Brush _ _ _ _ _).shimmy (formula X hx hk hK h he hp hy hM hz)
  exact avgBrush _ _ _ (fun i=> lands (X:=(planted X p).taggedL i) hx (planted_valid X p) hk hK h hm hp hy hM hz)

omit hx hk hK hp h he hy hM hz
variable (H)
lemma episodeSites (hK:Kept H (H.unionP p) K) (χ:Chi) : Measurable (episode H χ p K) ∧ LocalOn (H.unionP p) (episode H χ p K) ∧ GaugeInvariant (episode H χ p K):= by
  let X i:= prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:= rinsed (vary (X i) V) p (H.unionP p) K
  have hz i : Measurable (f i) ∧ LocalOn (H.unionP p) (f i) := rinsedSites (X i) rfl rfl hK p
  exact ⟨measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> (hz i).1),fun U V h=> congr_arg likely (funext fun i=> (hz i).2 _ _ h),
    fun z V=> congr_arg likely (funext fun i=> frieze (U:=H.unionP p) (K:=K) (X i) p z V)⟩
include he h
lemma episodeCost (hK:Kept H (H.unionP p) K) {k':ℝ} (hm:IntegrandCost H (H.unionP p) K j A v k' χ) (U:Config G c) (hy:Healthy (Pressure.temp s) (H.unionP p) U):
    Ore U (episode H χ p K) v k' j := by
  intro E _ _ _ V x hz hV
  let X i:= prism T s χ o.K U (Greenbelt.allot (S:=S) i)
  let f i y:= rinsed (vary (X i) (V y)) p (H.unionP p) K
  letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  exact avgBrush (j:=j) f _ _ (fun i=>priced (X i) rfl rfl hK h he rfl hy hV hz hm)
end YM.LocalTaylorR2.Port
