import YM.LocalTaylorR2.Exponent.Shelf

/-! Adaptation of `Port` helpers for the above new Burst. -/
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

variable (X:Coat T F) (hx : X.x=s) (hk : X.width=o.K) (hK : Burst H U K)
include hx hk hK
lemma plantedRuleBurst (p:Molecule S) (V:Config G c) (hp : Healthy (Pressure.temp s) U X.V) (he:(roster p).flags=∅) (Y:S.Choices):
    average (vary ((planted X p).taggedL Y) V) (podium S G U (radiusB s)) K=average ((preps (vary X V) (roster p)).taggedL Y) (podium S G U (radiusB s)) K := by
  rw [← show X.B=radiusB s from congr_arg _ hx]
  let A:=vary ((planted X p).taggedL Y) V; let A':=(preps (vary X V) (roster p)).taggedL Y
  refine agreesVillageBurst A hx hk hK U (Subset.refl _) (show Village A A' U from ?_)
  refine ⟨rfl,rfl,rfl,?_, fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _ _=>rfl⟩
  intro i hi; have he':i∉ RG.flags (Pressure.temp X.x) X.V:= by rw [hx]; exact Finset.disjoint_left.mp hp hi
  unfold A A' vary taggedL planted preps place; simp [he,he']

lemma onFrameSitesBurst (p:Molecule S): Measurable (fun V=> onFrame (vary X V) p U K) ∧ LocalOn U (fun V=>onFrame (vary X V) p U K):= by
  constructor
  · let f z V:= average ((preps (vary X V) (roster p)).taggedL z) (podium S G U X.B) K
    have hf z:Measurable (f z):=by
      let L:=((preps X (roster p)).taggedL z)
      have hq V : (preps (vary X V) (roster p)).taggedL z=vary L V:=rfl
      unfold f; simp_rw [hq]; exact averageMeasBurst L hx hk hK (podium S G U X.B)
    exact measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> hf i)
  intro V Z hu; apply congr_arg likely; funext i
  refine agreesVillageBurst ((preps (vary X V) (roster p)).taggedL i) hx hk hK U (Subset.refl _) (show Village _ ((preps (vary X Z) (roster p)).taggedL i) U from ?_)
  exact ⟨rfl,rfl,rfl,fun _ _=> Iff.rfl,fun _ _=> rfl,fun _ _=>rfl,fun _ _=>rfl,hu⟩
lemma rinsedSitesBurst (p:Molecule S): Measurable (fun V=> rinsed (vary X V) p U K) ∧ LocalOn U (fun V=> rinsed (vary X V) p U K):= by
  obtain ⟨hm,hL⟩:= onFrameSitesBurst X hx hk hK p; constructor
  · have hp : Measurable fun (a:Config G c × (Site c → G.El))=> gauge a.2 a.1 := by
      refine measurable_pi_lambda _ fun i=> ?_; dsimp only [Lattice.gauge]; fun_prop
    exact ((hm.comp hp).stronglyMeasurable.integral_prod_right' (ν:=Measure.pi fun _ : Site c=> G.probHaar)).measurable
  intro V Z hu; apply integral_congr_ae; filter_upwards with z
  exact hL (gauge z V) (gauge z Z) (fun i hi hj=> by unfold Lattice.gauge; rw [hu i hi hj])

variable {A b r C' v B d:ℝ} {l j : ℕ} {χ : Chi} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {Ξ : Utopia H j v d r C' χ}
variable (h : Oboe H j v B l A b Ξ) (he : (roster p).flags=∅) (hp:X.χ=χ) (hy : Healthy (Pressure.temp s) U X.V) (hM : Mode V x j v) (hz : V x=X.V)
include h he hp hy hM hz
lemma formulaBurst :
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
    rw [show X.B=radiusB s from congr_arg _ hx,← plantedRuleBurst X hx hk hK p _ hy he]
    change average ((Y q y).rinse z) I _=average _ I _; unfold I; rw [← chargedU]
    exact rinseInvariantBurst (Y q y) hx hk hK _ _ (hh q)
  -- exact, strong support unchanged
  change (∫ z, onFrame ((vary X (V y)).rinse z) p U K ∂_)=Z; simp_rw [hF]; simp

lemma pricedBurst {k':ℝ} (hm:IntegrandCost H U K j A v k' χ): Brush j k' 1 (fun y=> rinsed (vary X (V y)) p U K) x := by
  refine (?_ : Brush _ _ _ _ _).shimmy (formulaBurst X hx hk hK h he hp hy hM hz)
  exact avgBrush _ _ _ (fun i=> landsBurst (X:=(planted X p).taggedL i) hx (planted_valid X p) hk hK h hm hp hy hM hz)

omit hx hk hK hp h he hy hM hz
variable (H)
lemma episodeSitesBurst (hK:Burst H (H.unionP p) K) (χ:Chi) : Measurable (episode H χ p K) ∧ LocalOn (H.unionP p) (episode H χ p K) ∧ GaugeInvariant (episode H χ p K):= by
  let X i:= prism T s χ o.K 1 (Greenbelt.allot (S:=S) i); let f i V:= rinsed (vary (X i) V) p (H.unionP p) K
  have hz i : Measurable (f i) ∧ LocalOn (H.unionP p) (f i) := rinsedSitesBurst (X i) rfl rfl hK p
  exact ⟨measurable_const.mul (Finset.measurable_fun_sum _ fun i _=> (hz i).1),fun U V h=> congr_arg likely (funext fun i=> (hz i).2 _ _ h),
    fun z V=> congr_arg likely (funext fun i=> frieze (U:=H.unionP p) (K:=K) (X i) p z V)⟩
include he h
lemma episodeCostBurst (hK:Burst H (H.unionP p) K) {k':ℝ} (hm:IntegrandCost H (H.unionP p) K j A v k' χ) (U:Config G c) (hy:Healthy (Pressure.temp s) (H.unionP p) U):
    Ore U (episode H χ p K) v k' j := by
  intro E _ _ _ V x hz hV
  let X i:= prism T s χ o.K U (Greenbelt.allot (S:=S) i)
  let f i y:= rinsed (vary (X i) (V y)) p (H.unionP p) K
  letI : Nonempty (Tree.Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
  exact avgBrush (j:=j) f _ _ (fun i=>pricedBurst (X i) rfl rfl hK h he rfl hy hV hz hm)
end YM.LocalTaylorR2.Port


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
variable {A b r C' v B d:ℝ} {l j : ℕ} {χ : Chi} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {Ξ : Utopia H j v d r C' χ}
variable (X:Coat T F) (hx:X.x=s) (hk:X.width=o.K)
variable {ι : Type*} [Fintype ι] {g:ι→Test T}
variable (hK : Burst H U K) (hg : ∀ i,Burst H U (g i)) (H0 : ∀ F X u, K F X u=∑ i, g i F X u)
variable (h : Oboe H j v B l A b Ξ) (he : (roster p).flags=∅) (hp:X.χ=χ) (hy : Healthy (Pressure.temp s) U X.V) (hM : Mode V x j v) (hz : V x=X.V)
private lemma like_sumBurst {α : Type} [Fintype α] (f : α→ι→ℝ) : likely (fun x=>∑ i, f x i) =∑ i, likely (fun x=> f x i) := by
  unfold likely; rw [← mul_sum, sum_comm]
include hx hk hK hg H0 h he hp hy hM hz
lemma resolvesBurst :
    (fun y=> rinsed (vary X (V y)) p U K) =ᶠ[𝓝 x]
      fun y=> ∑ i,rinsed (vary X (V y)) p U (g i) := by
  have hY t : (fun y=> average (vary ((planted X p).taggedL t) (V y)) (podium S G U (radiusB s)) K) =ᶠ[𝓝 x]
      fun y=> ∑ i,average (vary ((planted X p).taggedL t) (V y)) (podium S G U (radiusB s)) (g i):=by
    let Z:= (planted X p).taggedL t; let L:= (F.order G).prod Z.dice; let I:=edgesM S U (radiusB s)
    have hχ : Z.χ=χ:= hp
    have hX: Z.manifest:= planted_valid X p
    have hC:= h.flow F Z hx hχ hk hX E V x hz hM
    filter_upwards [slopesBurst (X:=Z) hx hX hk hK hC h.conduit h.mode,eventually_all.mpr (fun i=> slopesBurst (X:=Z) hx hX hk (hg i) hC h.conduit h.mode),eventually_all.mpr (fun i=> (periodExchangeBurst (X:=Z) hx hX hk (hg i) hC h.conduit h.mode).2)] with y he hX he'
    change average _ _ _=∫ w, duoTilt R.beta I Z (V y) A K w ∂L at he
    change ∀ i, average (F:=F) (vary Z (V y)) _ (g i)=∫ w, duoTilt R.beta I Z (V y) A (g i) w ∂ L at hX
    change average (F:=F) (vary Z (V y)) _ _=∑ i,average (vary Z (V y)) _ _; rw [he]; simp_rw [hX]; rw [← integral_finsetSum _ (fun i _=> he' i)]
    apply integral_congr_ae; filter_upwards with w
    unfold duoTilt tilted; rw [H0,Finset.mul_sum]
  filter_upwards [formulaBurst X hx hk hK h he hp hy hM hz,
    eventually_all.mpr (fun i=> formulaBurst X hx hk (hg i) h he hp hy hM hz), eventually_all.mpr hY] with y hK hV he
  rw [hK]; simp_rw [hV,he,like_sumBurst]

omit hx hk hK hg hp hy hz
lemma episodeSumBurst (hK : Burst H (H.unionP p) K) (hg : ∀ i,Burst H (H.unionP p) (g i))
    (hy:Healthy (Pressure.temp s) (H.unionP p) (V x)) :
    episode H χ p K ∘ V =ᶠ[𝓝 x]
      fun y=> ∑ i,episode H χ p (g i) (V y) := by
  let X i:= prism T s χ o.K (V x) (Greenbelt.allot (S:=S) i)
  let M y (g:Test T) i:=rinsed (vary (X i) (V y)) p (H.unionP p) g
  filter_upwards [eventually_all.mpr (fun t=> resolvesBurst (V:=V) (U:=H.unionP p) (K:=K) (X t) rfl rfl hK hg H0 h he rfl hy hM rfl)] with y hy
  change ∀ i,M y K i=∑ t,M y (g t) i at hy
  change likely (fun i=>M y K i)=∑ t, likely (M y (g t))
  simp_rw [hy]; rw [like_sumBurst]
end YM.LocalTaylorR2.Port


