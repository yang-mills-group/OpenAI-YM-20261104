import YM.Comparison.RG02.Bulk.Admits
/-!
# Coefficient prescription on `Bulk.Kernel`: rescaled step before reset/repacking

Bulk ingredients:
* `S, P` etc **the real Wilson datum**, a single t in `StepData.Choices` (not
  independent uses; actually all t same in germ; no trace represented input here).
* Coarse `x` in actual *fine units* g: on eval V:=represent (g • x). (All SCALARS:
   any `v` volume etc held outside germ. Need exact reconstruction identity & *separate*
   estimates to use with normalized push. Here ζ=1 branch of Jacobian etc.)
* Finitary additional log inputs in `W : Colors`, already valued in g; at rescaled fields
     use supplement as indicated. Full-field Gaussian/wick. No outside marker sharing
     assumptions. No infinite-volume mesh rate or puzzle-solving claimed.

Output `Fk` function is canonical joint order-graded Poly moment (series of unnormalized
 numerator **factored by one identifiable leading scalar**, not unit-normalized source industry).
 `Order.denominator` applies to vacuum denominator; `Order.logVac` and `.logMarked`
 compute the log after that normalization. Use that same `denominator`, not separate tag-by-tag
 normalizations. The scalar factors (outside moments) are supplied as in Kernel.Heat etc later;
 they *do not Taylor expand* with these grades. Phase-independent local RG kernel coefficients;
 phase-dependent observables must apply Capture etc to their own term in the corresponding Family.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bulk
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open Next.SectorChange
open PertExtension.Series Multi Marker Order Assembly Cumulants
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} {V : Type} [DecidableEq V] {R : Census V}
  (K : Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
  (W : Colors R G f)

local notation "E" => Joint S F (G:=G)
local notation "I" => Precision.Key F G

def pillar (z : E) := (z.1)^2

def officer (_ : Kernel S p P O) (z : E) := (loop P (Work.F03.live F z.2)) - Real.log (∏ i, O.J (z.2.2 i))

def stone (_ : Kernel S p P O) (z : E) := Surface S p P F t z.2

def fee (z : E) := pillar (F:=F) z * officer F K z + supplement S F W z

def geometric (z : E) := stone F t K z + fee K F W z

lemma officer_known : GradeAt 1 (officer F K) := by
   obtain ⟨a,A,Λ,hP⟩:=K.bounds
   let J (z : E) := ∏ i, O.J (z.2.2 i)
   have h0 : J 0=1 := by simp only [J,Prod.snd_zero,Pi.zero_apply,K.ratio.anchored,prod_const_one]
   have hc : ContDiffAt ℝ ω J 0 := by
      unfold J; apply contDiffAt_prod; intro i _
      have ho := K.ratio.germ 0 (Metric.mem_ball_self K.ratio.patch)
      exact ho.comp (f:=fun z : E=> z.2.2 i) 0 ((contDiffAt_apply ℝ G.Color i _).comp (f:=fun z:E=> z.2.2) (0:E) (contDiffAt_snd.snd))
   apply GradeAt.anchored
   · let u:=fun i:E=> loop P (Work.F03.live F i.2)
     have hp : ContDiffAt ℝ ω u 0 := (joint_receipt S F (z:=fun _=> loop P) (GradeAt.unchecked (show ContDiffAt ℝ ω (fun x : ℝ × fieldDir G f 1=> loop P (represent x.2)) 0 from (loop_smooth (m:=f) p P hP).comp (f:=Prod.snd) (0:ℝ × fieldDir G f 1) contDiffAt_snd))).smooth
     exact hp.sub (hc.log (by rw [h0]; simp))
   unfold officer; rw [Prod.snd_zero,Work.F03.live_zero,loop_origin p P hP]; change 0- Real.log (J 0)=0; rw [h0,Real.log_one,sub_zero]
lemma fee_starts (hw : Well W) : GradeAt 3 (fee K F W) := by
   let L : E→ℝ:= Prod.fst
   have he : GradeAt 2 (fun z=> L z ^ 2) := GradeAt.shifts _ contDiffAt_fst rfl 2
   exact (he.mul (officer_known K F)).add (joint_receipt S F hw.suppose_vac)

private def pullstone : E →L[ℝ] SliceDir S F G := ContinuousLinearMap.snd ℝ ℝ _
lemma stone_smooth : ContDiffAt ℝ ω (stone F t K) 0 := ((K.critical F).2.2 t).1.comp (0:E) contDiffAt_snd
lemma stone_jet (y : E) (i : ℕ) : Assembly.jet (stone F t K) i y = Assembly.jet (Surface S p P F t) i y.2 :=
  jet_continuous_right (pullstone (F:=F)) (((K.critical F).2.2 t).1.of_le le_top) y
lemma geometric_prefix (h : Well W) (y : E) (n : ℕ) (hn : n<3) : Assembly.jet (geometric K F t W) n y=Assembly.jet (Surface S p P F t) n y.2 := by
  rw [← stone_jet K F t]
  unfold Assembly.jet
  rw [show geometric K F t W=stone F t K+fee K F W from rfl,iteratedFDeriv_add_apply ((stone_smooth K F t).of_le le_top) ((fee_starts K F W h).smooth.of_le le_top),(fee_starts K F W h).vanish n hn, add_zero]

lemma geometric_ready (hw : Well W) : Admissible W.power (markFn S F W) (geometric K F t W) := by
   refine ⟨?_,fun i=> let h : GradeAt (W.power i) (markFn S F W i):=joint_receipt S F (hw.suppose_mark i); ⟨h.smooth.of_le le_top, fun _ he x=> h.jet_z x he⟩⟩
   obtain ⟨a,A,Λ,hP⟩:=K.bounds
   constructor
   · exact ((stone_smooth K F t).add (fee_starts K F W hw).smooth).of_le le_top
   · simpa only [Assembly.jet_zero,origin S p P F t hP K.branches]
        using geometric_prefix K F t W hw 0 0 (by decide)
   intro u; change Assembly.jet _ 1 u=0
   rw [geometric_prefix K F t W hw u 1 (by decide), Assembly.jet, iteratedFDeriv_one_apply, surface_first S p P F t hP K.branches (K.b F) (K.critical F)]; simp

lemma geometric_choice (t' : S.Choices) : geometric K F t W =ᶠ[𝓝 0] geometric K F t' W := by
  refine Filter.EventuallyEq.add ?_ Filter.EventuallyEq.rfl
  exact (continuous_snd.tendsto (0:E)).eventually (Work.F04.tested_germ K.branches F p P t t')
-- deterministic external orders explicitly.
variable (x : fieldDir G c 1)

def stage : E := (1,classical S F (K.b F) x)
def hinge (F : Forest S.ratio) : (Precision.Key F G → ℝ) →ₗ[ℝ] Joint S F (G:=G) :=
    (LinearMap.inr ℝ _ _).comp ((LinearMap.inr ℝ _ _).comp gaugeCount.toLinearEquiv.toLinearMap)

def translated (z : I→ℝ) : E := translate (stage K F x) (hinge F) z
lemma footing (z : I→ℝ) : translated K F x z = ((1:ℝ),x, fderiv ℝ (K.b F) 0 x + tape z) := by
   unfold translated stage Assembly.translate hinge; ext1
   · exact add_zero _
   apply Prod.ext
   · exact add_zero _
   rfl
lemma completed (z : I→ℝ) (hW : Well W) : Assembly.jet (geometric K F t W) 2 (translated K F x z)=infrared S p P F t (K.b F) x + Gaussian.force (K.covariance F t) z/2 :=
  (geometric_prefix K F t W hW _ _ (by decide)).trans (K.force_square F t x z)

-- prescriptions portable for arbitrary t & forest
variable [Fintype V]

def Fk (r : ℕ) : Grade R r := Assembly.prescription (stage K F x) (hinge F) W.power (markFn S F W) (geometric K F t W) (K.covariance F t) (K.symm F t) r
variable (r : ℕ)
lemma fk_unit : UnitLeading (Fk K F t W x r) := Assembly.prescription_unit ..
lemma fk_sym : Order.Symmetric (Fk K F t W x r) := Assembly.prescription_sym _ _ _ _ _ _ _ (K.positive F t)

/-- `W` includes exogenous marked log drivers, no derivative rule using actual noise moments.
    `Assembly.prescription` is defined by Wick recurrence and subset expansions. Prove properties
    from that, match it with all-order Taylor moments independently (full Gaussian, off seam).
    Precise coefficient *identification*, not an assertion about integrated RG error. Compare
    to Taylor before dividing. -/
lemma table (i : R.Mode) (a : Index r) :
    (Fk K F t W x r).part (Join.pair i a)= (a.val.card.factorial:ℂ)*∫ z, rows (expansions W.power (markFn S F W) (geometric K F t W)) i a.val.card (translated K F x z) ∂Gaussian.cloud (K.covariance F t) := (Assembly.gather _ _ _ _ _ _ _ (K.positive F t) i a).2

variable {r} in
private lemma prescription_ident {J : Type} {Q Q' : Matrix J J ℝ} {H : Q.IsSymm} {H' : Q'.IsSymm} (ht : Q=Q') (M : Hot (Board R r) → Next.Rank.Normal.poly J) : Cloud.prescription Q H 0 M=Cloud.prescription Q' H' 0 M := by subst Q'; rfl
lemma fkChoice (t' : S.Choices) : Fk K F t W x r=Fk K F t' W x r := by
   have he:= geometric_choice K F t W t'
   have hG : ∀ (i : Hot (Board R r)), Assembly.generator (stage K F x) (hinge F) W.power (markFn S F W) (geometric K F t W) r i=Assembly.generator (stage K F x) (hinge F) W.power (markFn S F W) (geometric K F t' W) r i := by
      intro i; unfold Assembly.generator Assembly.naked; simp_rw [(he.iteratedFDeriv ℝ _).eq_of_nhds]
   unfold Fk prescription; rw [funext hG]; exact prescription_ident (K.convention F t t') _


end YM.Comparison.RG02.Bulk
