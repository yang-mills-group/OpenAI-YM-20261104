import YM.Integration.WilsonRetainedOccupiedSubword
import YM.Comparison.RG02.Cumulants.Partition

/-! Sum the native signed partition logarithm after paying its actual
subwords on one original conditional Gaussian. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory
open Push Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure RGLocalTaylor
open Coat Matter Pond Blaze.March PhysicalNext.Repeat Greenbelt PhysicalNext.Repeat.Legato Work.F03 Bid
open PhysicalNext.Repeat.Malachite AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Next.SectorChange WilsonCoherentMayerProjection Next.Rank Comparison.RG02.Cumulants Comparison.RG02.Assembly
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoherentMayerHearing Dict06.Series
open Census Window
open scoped BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W s μ C : ℝ} {o : Target.Order G W} {R : Rep G f}


open Marker Multi Extra.Trajectories

private theorem product_change {J : Type*} [DecidableEq J] (A : Finset J)
    (v w : J → ℂ) (δ : J → ℝ) (paid : ∀ i∈A, ‖v i-w i‖ ≤ δ i) :
    ‖(∏ i∈A,v i)-(∏ i∈A,w i)‖ ≤ (∏ i∈A,(‖w i‖+δ i))-(∏ i∈A,‖w i‖) := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert i A hi ih =>
    have step := ih (fun j hj => paid j (Finset.mem_insert_of_mem hj))
    have change := paid i (Finset.mem_insert_self ..)
    have bound : ‖v i‖ ≤ ‖w i‖+δ i := calc
      _ = ‖v i-w i+w i‖ := by rw [sub_add_cancel]
      _ ≤ ‖v i-w i‖+‖w i‖ := norm_add_le ..
      _ ≤ _ := by linarith
    simp only [Finset.prod_insert hi]
    calc
      _ = ‖v i*((∏ j∈A,v j)-(∏ j∈A,w j))+(v i-w i)*(∏ j∈A,w j)‖ := by congr 1; ring
      _ ≤ ‖v i‖*‖(∏ j∈A,v j)-(∏ j∈A,w j)‖ + ‖v i-w i‖*(∏ j∈A,‖w j‖) := by
        simpa only [norm_mul, Complex.norm_prod] using
          norm_add_le (v i*((∏ j∈A,v j)-(∏ j∈A,w j))) ((v i-w i)*(∏ j∈A,w j))
      _ ≤ (‖w i‖+δ i)*((∏ j∈A,(‖w j‖+δ j))-(∏ j∈A,‖w j‖))+δ i*(∏ j∈A,‖w j‖) :=
        add_le_add (mul_le_mul bound step (norm_nonneg _) ((norm_nonneg _).trans bound))
          (mul_le_mul_of_nonneg_right change (by positivity))
      _ = _ := by ring

variable {V : Type*} [DecidableEq V] {E : Marker.Census V}

def partitionTariff (v : Marker.Poly E) (δ : E.Mode → ℝ) (t : E.Mode) : ℝ :=
  ∑ q∈shards E t, ‖mobiusTop q.val.card‖*
    ((∏ j∈q.val, (‖v.part j.val‖+δ j.val))-(∏ j∈q.val,‖v.part j.val‖))

theorem partition_change [Fintype V] (v w : Marker.Poly E) (δ : E.Mode → ℝ)
    (ov : v.part E.quiet=1) (ow : w.part E.quiet=1)
    (paid : ∀ j : E.Mode, ‖v.part j-w.part j‖≤δ j) (t : E.Mode) :
    ‖(connected v).part t-(connected w).part t‖ ≤ partitionTariff w δ t := by
  rw [log_partition v ov t, log_partition w ow t, ← Finset.sum_sub_distrib]
  refine (norm_sum_le ..).trans (Finset.sum_le_sum ?_)
  intro q _
  rw [←mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (product_change q.val (fun j=>v.part j.val)
    (fun j=>w.part j.val) (fun j=>δ j.val) (fun j _ => paid j.val)) (norm_nonneg _)

def physicalRegister (E : Marker.Census V) (X : Coat T F) (y : F.Slice G)
    (B : V → Normal.poly (Eye X)) (live : Finset V) (a : V → PrismA G) (x : V → Site f)
    (g p : ℝ) : Marker.Poly E :=
  Marker.Poly.inject fun t => ∫ z : Air f G,
    Cloud.paint (fun k=>z (tube X k)) (∏ j∈t.val, B j)*
      ∏ j∈t.val∩live, oldReading X y g p (a j) (x j) z ∂X.dice

def prescribedRegister (E : Marker.Census V) (X : Coat T F) (tag : S.Choices) (s : ℝ)
    (B : V → Normal.poly (Eye X)) (live : Finset V) (a : V → PrismA G) (x : V → Site f)
    (K : ℕ) (g p : ℝ) : Marker.Poly E :=
  Marker.Poly.inject fun t => Cloud.wick (WilsonOriginalSignedSamplerMoment.ideal T F tag s)
    (WilsonOriginalSignedSamplerMoment.symmetry T F tag s) 0
    ((∏ j∈t.val,B j)*(∏ j∈t.val∩live,rootedSite X (a j) (x j) K g p))

theorem occupied_log [Fintype V] (E : Marker.Census V)
    (H : Cash W s μ L Q o C T R) (temp : 0≤Pressure.temp s)
    (χ : Chi) (v : Finset (LocalLTE.Fan.Veil c f)) (i : Greenbelt.Reserve S) (tag : S.Choices)
    (y : (Greenbelt.allot i).Slice G) (Z : SeriesA G) (K : ℕ) (live : Finset V)
    (σ D : V → ℝ) (hs : ∀ j∈live, 0<σ j) (filed : ∀ j∈live, Draw Z (σ j) (D j))
    (a : V → PrismA G) (member : ∀ j∈live, a j ∈ Z) (x : V → Site f)
    (g p : ℝ) (hg : 0<g) (small : g≤1) (lo : 1/2≤p) (hi : p≤3/2) :
    let X := chamber T s o.K χ 1 v i tag
    ∀ B : V → Normal.poly (Eye X),
      let actual := physicalRegister E X y B live a x g p
      let model := prescribedRegister E X tag s B live a x K g p
      let δ := fun t : E.Mode => subwordTariff T L P o s X (t.val∩live) a σ D g K (∏ j∈t.val,B j)
      ∀ t : E.Mode, ‖(connected actual).part t-(connected model).part t‖ ≤ partitionTariff model δ t := by
  intro X B actual model δ t
  apply partition_change actual model δ
  · change (∫ z : Air f G, Cloud.paint (fun k=>z (tube X k)) (∏ j∈(∅:Finset V), B j)*
        ∏ j∈(∅:Finset V)∩live,oldReading X y g p (a j) (x j) z ∂X.dice)=1
    simp
  · change Cloud.wick _ _ 0 ((∏ j∈(∅:Finset V), B j)*
        (∏ j∈(∅:Finset V)∩live,rootedSite X (a j) (x j) K g p))=1
    simp [Cloud.wick_one]
  · intro u
    exact (occupied_subword H temp χ v i tag y Z K (u.val∩live) σ D
      (fun j hj=>hs j (Finset.mem_inter.mp hj).2) (fun j hj=>filed j (Finset.mem_inter.mp hj).2)
      a (fun j hj=>member j (Finset.mem_inter.mp hj).2) x g p hg small lo hi (∏ j∈u.val,B j)).2

end YM.Integration.OriginalMarkedRunAction

