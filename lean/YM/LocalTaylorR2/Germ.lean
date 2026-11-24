import YM.LocalTaylorR2.Pool
/-!
# Exact sums in common mask, integrated (*even in the open germ*)

Compare unmasked *label values* but budgets only on the Healthy
predicate. Global exact decompositions at the E6/LeafReady level
must still stipulate equality off the predicate (paid guard extension
in the tail letter).
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
variable {A b r C' v B d:ℝ} {l j : ℕ} {χ : Chi} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : E → Config G c} {x : E} {Ξ : Utopia H j v d r C' χ}
variable (X:Coat T F) (hx:X.x=s) (hk:X.width=o.K)
variable {ι : Type*} [Fintype ι] {g:ι→Test T}
variable (hK : Kept H U K) (hg : ∀ i,Kept H U (g i)) (H0 : ∀ F X u, K F X u=∑ i, g i F X u)
variable (h : Oboe H j v B l A b Ξ) (he : (roster p).flags=∅) (hp:X.χ=χ) (hy : Healthy (Pressure.temp s) U X.V) (hM : Mode V x j v) (hz : V x=X.V)
private lemma like_sum {α : Type} [Fintype α] (f : α→ι→ℝ) : likely (fun x=>∑ i, f x i) =∑ i, likely (fun x=> f x i) := by
  unfold likely; rw [← mul_sum, sum_comm]
include hx hk hK hg H0 h he hp hy hM hz
lemma resolves :
    (fun y=> rinsed (vary X (V y)) p U K) =ᶠ[𝓝 x]
      fun y=> ∑ i,rinsed (vary X (V y)) p U (g i) := by
  have hY t : (fun y=> average (vary ((planted X p).taggedL t) (V y)) (podium S G U (radiusB s)) K) =ᶠ[𝓝 x]
      fun y=> ∑ i,average (vary ((planted X p).taggedL t) (V y)) (podium S G U (radiusB s)) (g i):=by
    let Z:= (planted X p).taggedL t; let L:= (F.order G).prod Z.dice; let I:=edgesM S U (radiusB s)
    have hχ : Z.χ=χ:= hp
    have hX: Z.manifest:= planted_valid X p
    have hC:= h.flow F Z hx hχ hk hX E V x hz hM
    filter_upwards [slopes (X:=Z) hx hX hk hK hC h.conduit h.mode,eventually_all.mpr (fun i=> slopes (X:=Z) hx hX hk (hg i) hC h.conduit h.mode),eventually_all.mpr (fun i=> (periodExchange (X:=Z) hx hX hk (hg i) hC h.conduit h.mode I).2)] with y he hX he'
    change average _ _ _=∫ w, duoTilt R.beta I Z (V y) A K w ∂L at he
    change ∀ i, average (F:=F) (vary Z (V y)) _ (g i)=∫ w, duoTilt R.beta I Z (V y) A (g i) w ∂ L at hX
    change average (F:=F) (vary Z (V y)) _ _=∑ i,average (vary Z (V y)) _ _; rw [he]; simp_rw [hX]; rw [← integral_finsetSum _ (fun i _=> he' i)]
    apply integral_congr_ae; filter_upwards with w
    unfold duoTilt tilted; rw [H0,Finset.mul_sum]
  filter_upwards [formula X hx hk hK h he hp hy hM hz,
    eventually_all.mpr (fun i=> formula X hx hk (hg i) h he hp hy hM hz), eventually_all.mpr hY] with y hK hV he
  rw [hK]; simp_rw [hV,he,like_sum]

omit hx hk hK hg hp hy hz
lemma episodeSum (hK : Kept H (H.unionP p) K) (hg : ∀ i,Kept H (H.unionP p) (g i))
    (hy:Healthy (Pressure.temp s) (H.unionP p) (V x)) :
    episode H χ p K ∘ V =ᶠ[𝓝 x]
      fun y=> ∑ i,episode H χ p (g i) (V y) := by
  let X i:= prism T s χ o.K (V x) (Greenbelt.allot (S:=S) i)
  let M y (g:Test T) i:=rinsed (vary (X i) (V y)) p (H.unionP p) g
  filter_upwards [eventually_all.mpr (fun t=> resolves (V:=V) (U:=H.unionP p) (K:=K) (X t) rfl rfl hK hg H0 h he rfl hy hM rfl)] with y hy
  change ∀ i,M y K i=∑ t,M y (g t) i at hy
  change likely (fun i=>M y K i)=∑ t, likely (M y (g t))
  simp_rw [hy]; rw [like_sum]
end YM.LocalTaylorR2.Port
