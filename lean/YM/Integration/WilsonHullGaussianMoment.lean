import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Grain
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Projection
import YM.Comparison.RG02.Cumulants.Cloud
import YM.RGLocalTaylor.Engine.Meaning
import YM.Next.RANK.Guard

/-! The joint signed marked measure of the original empty-inventory Wilson hull and its comparison with the full active Gaussian covariance. -/
set_option autoImplicit false

noncomputable section
namespace YM.Integration.WilsonHullGaussianMoment
open Filter Function Finset Lattice Wilson RG Pressure Pressure.Stores Pressure.Tube Tree
open MeasureTheory Matrix Marker Multi Precision Exterior Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 ConnectedActivityE6.Coat Progress.StationaryScenes
open ConnectedActivityE6.Window ConnectedActivityE6.Control ConnectedActivityE6.Census
open ConnectedActivityE6.Blaze ConnectedActivityE6.SliceRows ConnectedActivityE6.Mask
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws AnalyticBridge.SectorAffine
open PhysicalNext.Repeat PhysicalNext.Repeat.Malachite
open PhysicalNext.WeightedGaussianMarginal45C.Issue Next.Rank
open Comparison.RG02.Cumulants
open scoped BigOperators Classical Matrix.Norms.Frobenius Topology

section Polynomial
variable {I : Type} [Fintype I] [DecidableEq I] {Q D : Matrix I I ℝ}
variable (hQ : Q.IsSymm) (hD : D.IsSymm)

omit [Fintype I] [DecidableEq I] in
theorem polynomial (p : Normal.poly I) (d : ℕ) {b ε : ℝ} (hb : 1≤b) (hε : 0≤ε)
    (hd : p.totalDegree ≤ d) (hP : ∀i∈p.vars,∀j∈p.vars, |Q i j|≤b)
    (hP' : ∀i∈p.vars,∀j∈p.vars, |D i j|≤b)
    (hgap : ∀i∈p.vars,∀j∈p.vars, |Q i j-D i j|≤ε) :
    ‖Cloud.wick Q hQ 0 p-Cloud.wick D hD 0 p‖≤ Rise.coin p*(ε*Common.priced b d) := by
  apply Tapes.differently p.vars p le_rfl hb hd (fun i _=> by simpa using (zero_le_one.trans hb))
  · intro i hi j hj
    change ‖(Q i j:ℂ)‖≤b
    simpa using hP i hi j hj
  · intro i hi j hj
    change ‖(D i j:ℂ)‖≤b
    simpa using hP' i hi j hj
  · exact hε
  · intro i hi j hj
    change ‖(Q i j:ℂ)-(D i j:ℂ)‖≤ε
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hgap i hi j hj
end Polynomial

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
def measured (X : Coat T F) := (stoneC X 0).submatrix (tube X) (tube X)

theorem optics_symm (X : Coat T F) : (optics X 0).IsSymm := by
  rw [optics,AnalyticBridge.SectorAffine.picked_sym]
  unfold Matrix.IsSymm
  rw [Matrix.transpose_smul,Matrix.transpose_add,Matrix.transpose_transpose,add_comm]

theorem marginal (X : Coat T F) (hX : (stoneC X 0).PosDef) :
    MeasurePreserving (fun z : Air f G => fun i => z (tube X i)) (gem X 0).dice (Gaussian.cloud (measured X)) := by
  let e := (MeasurableEquiv.toLp 2 (Gaussian.Vec (Tubular f G))).symm
  have he : MeasurePreserving e (gem X 0).dice (Gaussian.cloud (stoneC X 0)) := ⟨e.measurable,rfl⟩
  exact (AnalyticBridge.Sharp.Projection.cloud_projection hX (tube X)).comp he

theorem moment (X : Coat T F) (hX : (stoneC X 0).PosDef) (p : Normal.poly (Eye X)) :
    ∫ z : Air f G,Cloud.paint (fun i=>z (tube X i)) p ∂(gem X 0).dice =
      Cloud.wick (measured X) (Matrix.isHermitian_iff_isSymm.mp (hX.submatrix (tube X).injective).isHermitian) 0 p := by
  let hs := Matrix.isHermitian_iff_isSymm.mp (hX.submatrix (tube X).injective).isHermitian
  have H := Cloud.paid (measured X) hs (hX.posSemidef.submatrix (tube X)) 0 p
  simp only [Cloud.shift_zero,zero_add] at H
  have h := marginal X hX
  rw [←H.2,←h.map_eq,integral_map h.measurable.aemeasurable]
  simpa only [h.map_eq] using H.1.aestronglyMeasurable

theorem paid (X : Coat T F) {u e C : ℝ} {n : ℕ} (H : Photic X u e C n)
    (hu : 0≤u) (he : 0≤e) (hX : (stoneC X 0).PosDef) (p : Normal.poly (Eye X)) (d : ℕ)
    (hd : p.totalDegree≤d) :
    ‖(∫ z : Air f G,Cloud.paint (fun i=>z (tube X i)) p ∂(gem X 0).dice) -
       Cloud.wick (optics X 0) (optics_symm X) 0 p‖ ≤ Rise.coin p*(e*Common.priced (1+|C|) d) := by
  rw [moment X hX]
  have hb : 1≤1+|C| := by linarith [abs_nonneg C]
  have hU : ‖(0:Directions G c)‖ ≤ u := by simpa using hu
  refine polynomial _ _ p d hb he hd (fun i _ j _=>?_) (fun i _ j _=>?_) (fun i _ j _=>?_ )
  · have h := (H.horizon 0 i j hU).bound
    exact (show |measured X i j|≤C from by simpa [measured,Real.norm_eq_abs] using h).trans (by linarith [le_abs_self C])
  · exact (show |optics X 0 i j|≤C from by simpa [Real.norm_eq_abs] using (H.peak 0 i j hU).bound).trans
      (by linarith [le_abs_self C])
  · exact only_price H.shade.1 le_rfl i j

theorem read_inject {V : Type} [DecidableEq V] {R : Census V} (a : R.Mode→ℂ) (i : R.Mode) :
    (Poly.inject a).part i=a i := rfl

theorem marked {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    (X : Coat T F) {u e C : ℝ} {n : ℕ} (H : Photic X u e C n) (hu : 0≤u) (he : 0≤e)
    (hX : (stoneC X 0).PosDef) (p : Hot R → Normal.poly (Eye X)) (s : R.Mode) (d : ℕ)
    (hd : (Cloud.integrand p s).totalDegree≤d) :
    ‖(∫ z : Air f G,(Poly.pass (lit R fun j=>Cloud.paint (fun i=>z (tube X i)) (p j))).part s ∂(gem X 0).dice) -
      (Cloud.prescription (optics X 0) (optics_symm X) 0 p).part s‖ ≤
        Rise.coin (Cloud.integrand p s)*(e*Common.priced (1+|C|) d) := by
  simpa only [Cloud.before_log,Cloud.prescription,read_inject] using
    paid X H hu he hX (Cloud.integrand p s) d hd

/-- A single tail precedes the period, the forest and its live coordinates,
the tests and their complete joint polynomial. The only coefficient price
is the variation of the actual finite marked polynomial. -/
theorem scheduled (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G)
    (n : ℕ) (hn : 2≤n) {u : ℝ→ℝ} (hu : Rate G L (-(1/2)) u) (hu' : ∀ᶠ x in atTop,0≤u x)
    (j : ℝ) (d : ℕ) :
    ∃ fee : ℝ→ℝ, Rate G L j fee ∧ ∀ᶠ x in atTop,∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch=D → Works P L x S T → ∀(F : Forest S.ratio) (X : Coat T F), X.x=x → (stoneC X 0).PosDef →
      ∀(p : Normal.poly (Eye X)), p.totalDegree≤d →
        ‖(∫ z : Air f G,Cloud.paint (fun i=>z (tube X i)) p ∂(gem X 0).dice) -
          Cloud.wick (optics X 0) (optics_symm X) 0 p‖ ≤ Rise.coin p * fee x := by
  obtain ⟨e,C,hr,hC,h⟩ := treasure G P L D hD n hn hu hu' j
  have hA : Rate G L 0 (fun x=>|C x|) := hC.compare (by filter_upwards with x; simp)
  have hB := ((Rate.const (G:=G) (L:=L) 1).add hA).mul_left 2
  have hF := hr.mul ((hB.mul_right (d+1:ℝ)).pow d)
  refine ⟨fun x=> e x * Common.priced (1+|C x|) d, ?_, ?_⟩
  · simpa only [zero_mul,add_zero,Common.priced] using hF
  · filter_upwards [h,hu'] with x hb hx c f S T hs ht F X hX hp p hd
    obtain ⟨he,_hC₀,hP⟩ := hb c f S T hs ht F X hX
    exact paid X hP hx he hp p d hd

/-- The inverse of the entire physical bare Gram matrix on all free
coordinates. Empty inventory only removes the coordinate-tree gauge. -/
def active (X : Coat T F) := (X.blank.plate.submatrix (tube X) (tube X))⁻¹

theorem active_eq (X : Coat T F) {P : Teller G} (h : P.Funds S T) :
    active X = (profileGram T X.x 1 (bareStores S) F X.k 0)⁻¹ := by
  rw [active,same_probe X h]

theorem active_symm (X : Coat T F) :
    (active X).IsSymm := by
  have h : X.blank.plate.IsSymm := by
    unfold Coat.plate
    apply Matrix.IsSymm.add
    · unfold Matrix.IsSymm
      rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    · change (Matrix.diagonal _).IsSymm
      exact Matrix.isSymm_diagonal _
  exact (h.submatrix _).inv

theorem zero_cov (X : Coat T F) : stoneC X 0 = X.blank.relating := by
  unfold stoneC gem dry
  rw [Work.G07.at_zero_increment]
  rfl

/-- The frame cut from the full inverse costs only the purchased covariance
tail on each genuine live pair. The uncut inverse has the original uniform
volume-independent covariance invoice on those same coordinates. -/
theorem active_paid (X : Coat T F) {P : Teller G} (h : P.Funds S T) {η r Q : ℝ} {m : ℕ}
    (A : Allow X.blank.plate (along S) m η r Q) (hp : X.blank.relating.PosDef)
    (p : Normal.poly (Eye X)) (d : ℕ) (hd : p.totalDegree≤d) :
    ‖(∫ z : Air f G, Cloud.paint (fun i=>z (tube X i)) p ∂(gem X 0).dice) -
       Cloud.wick (active X) (active_symm X) 0 p‖ ≤
      Rise.coin p * (distPay η r Q m X.B * Common.priced (1+payE η r Q m) d) := by
  have hme : (stoneC X 0).PosDef := by rw [zero_cov];exact hp
  have hc : 1≤1+payE η r Q m := by linarith [A.disc]
  have hd' : 0≤distPay η r Q m X.B := mul_nonneg A.disc (A.heap _)
  rw [moment X hme]
  refine polynomial _ _ p d hc hd' hd (fun i _ j _=>?_) (fun i _ j _=>?_) (fun i _ j _=>?_)
  · have q := only_price (A.mate X.blank.shutter).1 A.weather.1.le (tube X i) (tube X j)
    rw [measured,zero_cov]
    exact q.trans (by linarith)
  · rw [active,←ringD X h A]
    exact (only_price A.flatup.1 A.weather.1.le (tube X i) (tube X j)).trans (by linarith)
  · rw [measured,zero_cov,active,←ringD X h A]
    exact only_price (A.drift X.blank.shutter).1 A.weather.1.le (tube X i) (tube X j)

theorem active_scheduled (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G)
    (j : ℝ) (d : ℕ) :
    ∃ fee : ℝ→ℝ, Rate G L j fee ∧ ∀ᶠ x in atTop,∀ (c f : Side) (S : StepData c f) (T : Tube G S),
       S.patch=D → Works P L x S T → ∀(F : Forest S.ratio) (X : Coat T F), X.x=x →
       ∀(p : Normal.poly (Eye X)), p.totalDegree≤d →
          ‖(∫ z : Air f G,Cloud.paint (fun i=>z (tube X i)) p ∂(gem X 0).dice) -
            Cloud.wick (active X) (active_symm X) 0 p‖ ≤ Rise.coin p * fee x := by
  obtain ⟨η,r,Q,Y,hP,H⟩ := shoots P L D hD
  let m := tubularPrice G L
  let E := payE η r Q m
  refine ⟨fun x=>distPay η r Q m (radiusB x)*Common.priced (1+E) d,
    ((hP.physical G L j m).mul_left E).mul_right _,?_⟩
  filter_upwards [H,ConnectedActivityE6.room G P L] with x hb hr c f S T hs ht F X hx p hd
  subst x
  let hA := hb c f S T F X.blank rfl hs ht.length_eq (hr c f S T ht) (X.bowed (by unfold Pressure.temp;positivity))
  exact active_paid X ht.funds hA.scale hA.fullC p d hd

end YM.Integration.WilsonHullGaussianMoment
end

noncomputable section
namespace YM.Integration.WilsonHullGaussianMoment
open Filter Function Finset Lattice Wilson RG Pressure Pressure.Stores Pressure.Tube Tree
open MeasureTheory Matrix Marker Multi Precision Exterior Next.Fluctuations Next.SectorChange
open ConnectedActivityE6 ConnectedActivityE6.Coat Progress.StationaryScenes
open ConnectedActivityE6.Window ConnectedActivityE6.Control ConnectedActivityE6.Census
open PhysicalNext.Repeat PhysicalNext.Repeat.Malachite Next.Rank RGLocalTaylor
open AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open Comparison.RG02.Cumulants
open scoped BigOperators Classical Matrix.Norms.Frobenius Topology
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

theorem entire_input (X : Coat T F) (y : F.Slice G) (u : Directions G f) :
    (X.blank.wrapY y).input u = X.blank.input u := by
  unfold Coat.input
  congr 1
  funext e
  have h : X.blank.Hot e.val := (X.no_flat _).2 e.2
  change (if X.blank.Hot e.val then _ else y e)=(if X.blank.Hot e.val then _ else X.blank.Y e)
  rw [if_pos h,if_pos h]
  rfl

theorem entire_saved (X : Coat T F) (y : F.Slice G) : (X.blank.wrapY y).saved=0 := by
  funext e
  change (if e∈F.trunks ∨ X.blank.Hot e then 0 else _)=_
  rw [if_pos (or_iff_not_imp_left.mpr (fun he=>(X.no_flat _).2 he))]
  rfl

theorem entire_signal (X : Coat T F) (y : F.Slice G) (u : Directions G f) :
    (X.blank.wrapY y).signal u=X.blank.lens u := by
  rw [Coat.signal,entire_saved,zero_add]
  rfl

/-- The forest Haar integral contributes its exact mass one for every
bounded measurable test of the true reconstructed field and active noise. -/
theorem entire_haar (X : Coat T F) (u : Air f G → Directions G f) (g : Config G f → Air f G → ℂ)
    (h : Integrable (fun z => g (X.blank.input (u z)) z) (gem X 0).dice) :
    (∫ z : F.Slice G × Air f G, g ((X.blank.wrapY z.1).input (u z.2)) z.2 ∂Insert.moment (gem X 0)) =
      ∫ z : Air f G,g (X.blank.input (u z)) z ∂(gem X 0).dice := by
  simp_rw [entire_input]
  let hπ : MeasurePreserving Prod.snd (Insert.moment (gem X 0)) (gem X 0).dice := measurePreserving_snd
  rw [←hπ.map_eq,integral_map hπ.measurable.aemeasurable]
  simpa only [hπ.map_eq] using h.aestronglyMeasurable

section joint
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}

def actual (X : Coat T F) (b : F.Slice G → Hot R → Normal.poly (Eye X)) (s : R.Mode)
    (z : F.Slice G × Air f G) : ℂ :=
  (Poly.pass (lit R (fun j=>Cloud.paint (fun i=>z.2 (tube X i)) (b z.1 j)))).part s

def reference (X : Coat T F) (b : F.Slice G → Hot R → Normal.poly (Eye X)) (s : R.Mode) (y : F.Slice G) : ℂ :=
  (Cloud.prescription (active X) (active_symm X) 0 (b y)).part s

/-- The full mixed signed Haar charge is reduced only after evaluating
every marked source at the same physical Gaussian and the same Haar field. -/
theorem whole (X : Coat T F) {P : Teller G} (h : P.Funds S T) {η r Q : ℝ} {m : ℕ}
    (A : Allow X.blank.plate (along S) m η r Q) (hp : X.blank.relating.PosDef)
    (b : F.Slice G → Hot R → Normal.poly (Eye X)) (s : R.Mode) (d : ℕ) (bill : ℝ)
    (hbill : ∀y, Rise.coin (Cloud.integrand (b y) s)≤bill)
    (hd : ∀y, (Cloud.integrand (b y) s).totalDegree≤d)
    (htrue : Integrable (actual X b s) (Insert.moment (gem X 0)))
    (href : Integrable (reference X b s) (F.order G)) :
    ‖(∫ z,actual X b s z ∂Insert.moment (gem X 0)) -
      (∫ y,reference X b s y ∂F.order G)‖ ≤
        bill*(distPay η r Q m X.B*Common.priced (1+payE η r Q m) d) := by
  let k := distPay η r Q m X.B*Common.priced (1+payE η r Q m) d
  have hk : 0≤k := by
    have hc := A.disc
    have he := A.heap X.B
    dsimp [k,distPay,Common.priced]
    positivity
  have hrow (y : F.Slice G) :
      ‖(∫ z : Air f G, actual X b s (y,z) ∂(gem X 0).dice) - reference X b s y‖ ≤ bill*k := by
    have hy := (active_paid X h A hp (Cloud.integrand (b y) s) d (hd y)).trans
      (mul_le_mul_of_nonneg_right (hbill y) hk)
    simpa only [actual,reference,Cloud.before_log,Cloud.prescription,read_inject] using hy
  change ‖(∫ z,actual X b s z ∂(F.order G).prod (gem X 0).dice) - _‖ ≤ bill*k
  rw [integral_prod _ htrue,←integral_sub htrue.integral_prod_left href]
  exact (norm_integral_le_integral_norm _).trans ((integral_mono (htrue.integral_prod_left.sub href).norm
    (integrable_const _) hrow).trans_eq (by simp))

end joint
end YM.Integration.WilsonHullGaussianMoment
end

