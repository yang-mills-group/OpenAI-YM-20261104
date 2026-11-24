import YM.AllOrder.High.Typhos
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Raw
open Filter Function Lattice RG Pressure Pressure.Stores Tree Wilson Finset MeasureTheory
open Push Push.AbsoluteSums Push.AbsoluteSums.Paths Push.AbsoluteSums.Footprint
open SectorMeasure Presented Oriented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side}
open PhysicalNext.Repeat.Height
-- `Stage.Height π` cutoff strict. issue Barricade p when inflating ONLY specific error labels. excludes arbitrary non-pay Φ. truth.
abbrev active (u:ℝ)(τ:ℕ→ℕ)(R:Rep G f): Rep G f:= {R with activities:= { R.activities with E:=fun i=> u^(τ i) • (R.activities.E i)}}
-- care S.L implicit and χ paths. no change poses in cert; not operation on evaluation identity.Mercury. used to pay. ONE-L.B.If sources boost.
def Productive (τ:ℕ→ℕ){S:StepData c f}(P:Teller G)(T:Tube G S)(x:ℝ)(R:Rep G f) := Intake P T x (active (grow G S.patch.L x) τ R)
abbrev stake (c f:Side)(V:ℕ→ℕ): LogLetter c f→ℕ:= Sum.elim V (fun _=>0)
def gradeT (V:ℕ→ℕ) (w:ℕ)(c f:Side)(i:LogLetter c f) := gradeA w c f i + stake c f V i
theorem masking (V:ℕ→ℕ)(u:ℝ)(R:Rep G f)(i:ℕ)(U:Config G f): (active u V R).activities.regularOccurrence R.p i U = u^(V i)* R.activities.regularOccurrence R.p i U:= by unfold Activities.regularOccurrence; dsimp only; by_cases h:Healthy R.p.threshold (R.activities.reg i).support U; rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]; rfl; rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,mul_zero] -- may not imported.
lemma posts {S: StepData c f}(τ:ℕ→ℕ)(x:ℝ)(R:Rep G f)(T:Tube G S)(U:Config G f)(V:Config G c)(i:LogLetter c f): expo T x (active (grow G S.patch.L x) τ R) U V i= grow G S.patch.L x^(stake c f τ i) * expo T x R U V i := by
 rcases i with j|j|j|j|j|j
 · change -( _ )= _^ (τ j)*(-_); rw [masking]; ring
 all_goals rw [show stake c f τ _=0 from rfl,pow_zero,one_mul]; rfl
-- gets inherited price for even these weights from earlier at Spec toll (infl distribution).
theorem inherit_torch (π:ℕ) (G : Gauge) (P : Teller G) (l : ℕ) {a ε : ℝ} (he : 0<ε) (ha : 0≤a)
    (hx : 4*ε < P.top.supportExponent) (hy : 8*ε < P.top.width) (hz : 8*ε < P.below.width) :
    ∃ n : ℕ, ∀ L : Side, n ≤ L.val → ∀ r : ℝ, -(1/2:ℝ) < r → ∀ r' : ℝ,
      ∀ᶠ x : ℝ in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S) (R : Rep G f), S.patch.L=L →
      Intake P T x R → ∀ (τ:ℕ→ℕ), Productive τ P T x R →
      ∃ z : LogLetter c f → ℝ, (∀ U V i, |expo T x R U V i| ≤ z i) ∧
        Sales (radiusB x) a ε (space T l (radiusB x) R) (fun i=>grow G L x^gradeT τ π c f i*z i) (extra T R) (betaF G x L ^ r) ∧
      ∃ w : ℕ → ℝ, (∀ i U, |R.activities.K i U| ≤ w i) ∧
        Sales (radiusB x) a ε (forcedFoot S.ratio l (radiusB x) R) w (forcedExtra R) (betaF G x L ^ r') := by
 obtain ⟨n,H⟩:= inherit_deep π G P l he ha hx hy hz; refine ⟨n,fun L hL r hp r'=> ?_⟩; filter_upwards [(YM.Work.E09.betaF_growth G L).eventually_gt_atTop 1,H L hL r hp r'] with x hx H c f S T R h hp τ ht
 subst L; obtain ⟨p,h,hp,hP⟩:= H _ _ S T _ rfl ht; let u:= grow G S.patch.L x; have hs:0<u:= Real.rpow_pos_of_pos (by linarith) _
 let z i:=p i/u^stake c f τ i; refine ⟨z,fun U V i=>?_ ,?_, hP⟩
 · unfold z; rw [le_div_iff₀ (pow_pos hs _)]; conv_lhs=> rw [mul_comm];
   have hf:=h U V i; rw [posts,abs_mul,abs_of_pos (pow_pos hs _)] at hf; exact hf
 have hh(i):u^ (gradeA π c f i+stake c f τ i)* z i = grow G S.patch.L x^gradeA π c f i *p i:= by rw [pow_add]; unfold z; field_simp; unfold u; ring
 change Sales _ _ _ _ (fun i=> u^ (gradeA π c f i+stake c f τ i)* z i) _ _; simp_rw [hh]; exact hp
end YM.ConnectedActivityE6.Raw
