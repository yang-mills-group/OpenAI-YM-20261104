import YM.Integration.WilsonHeldCubicCourse
import YM.Integration.WilsonGaussianDeterminantStage

/-! The complete integrated cubic price at the dates of the original Wilson
construction, including the spatial sum over its translated source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonHeldCubicElection
open Function Filter Finset MeasureTheory Matrix Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Coat Control Pulse Footprint Raw Matter Window Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Art Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy LocalTaylorR2 LocalTaylorR2.Kiln
open Axial Channel Canvas Itinerary Port WilsonHeldKineticTeamIntegral
open WilsonGaussianDeterminantStage (mode)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {Q : ConnectedActivityE6.Target G P} {c f L : Side}
    {S : StepData c f} {T : Tube G S} {R : Rep G f} {W μ x C : ℝ} {o : Target.Order G W}

def Bought (H : Cash W x μ L Q o C T R) (χ : Chi) (n j : ℕ) : Prop :=
  ∃ (a b B d r C₀ : ℝ) (l : ℕ) (Ξ : Utopia H j (mode G L x) d r C₀ χ),
    let η := -Raw.orientation*R.beta
    let w := fun i : Trans f => bill a b η x R.path.cubic i
    Sales (radiusB x) (Q.relative+1) Q.ε (atomFoot S.ratio Q.halo (radiusB x) R.path.cubic)
      (fun i => |B| * w i * (betaF G x L^(1/2:ℝ))^n) (atomCharge R.path.cubic)
        (betaF G x L^(-(1/4):ℝ)) ∧
    ∀ (M : Team R) (p : H.ThinP) (i : Trans f),
    M.signs S ⊆ p.val → Ac.Spark H.supportP p.val → troupe T R Q.halo (radiusB x) p.val →
    atomFoot S.ratio Q.halo (radiusB x) R.path.cubic i ⊆ H.unionP p.val →
    ∀ (F : Forest S.ratio) (X : Coat T F), X.x=x → X.width=o.K → X.manifest → X.χ=χ →
    Healthy (Pressure.temp x) (H.unionP p.val) X.V →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (V : E → Config G c) (y : E), Mode V y j (mode G L x) → V y=X.V →
    let K := debt (primary G) (n+3) R.path.cubic R o.a η i
    let τ := seating Q.halo x S R.path.cubic i
    Brush j (expense M p (|B|) (w i) τ j l Ξ) 1 (fun z =>
      Port.average (vary X (V z)) (podium S G (H.unionP p.val) (radiusB x))
        (fun F X z => Orbit.hero M H p F X z * K F X z)) y

private theorem shape {D E : Patch} (h : D.L=E.L) (k : D.J=E.J) : D=E := by
  cases D; cases E; cases h; cases k; rfl

def decal (G : Gauge) (χ : Chi) : Daisy.Charity.RG12.Decal G where
  rub P Q _ L W μ o _ i x := ∀ n ≤ i, ∀ j ≤ i, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
    (R : Rep G f) (C : ℝ) (H : Cash W x μ L Q o C T R), Stamp T → Bought H χ n j
  good P Q _ := by
    obtain ⟨h₀,owns⟩ := WilsonHeldCubicCourse.purchased P Q
    refine ⟨h₀,fun L hL W μ o _ l _ hw hμ => ?_⟩
    by_cases lacks : ∃ D : Patch, D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
    · obtain ⟨D,branches,len,ord⟩ := lacks
      have hv : Rate G L (-(1/2)) (mode G L) := Rate.power
      have pos : ∀ᶠ x in atTop, 0 ≤ mode G L x :=
        ((Work.E09.betaF_growth G L).eventually_gt_atTop 0).mono fun x hx => Real.rpow_nonneg hx.le _
      have each (n j : Fin (l+1)) : ∀ᶠ x in atTop, ∀ (c f : Side) (S : StepData c f) (T : Tube G S)
          (R : Rep G f) (C : ℝ) (H : Cash W x μ L Q o C T R), Stamp T → Bought H χ n j := by
        obtain ⟨a,b,B,d,r,C₀,k,ha,hb,hB,ready⟩ :=
          owns L hL D branches W μ hw hμ o (mode G L) hv pos n j χ
        have h₁ : Rate G L (-((n.val+4:ℕ):ℝ)/2) (fun x => B x*a x) := by
          simpa only [zero_add] using! hB.mul ha
        have h₂ : Rate G L 0 (fun x => B x*b x) := by
          simpa only [zero_add] using! hB.mul hb
        have rel : 0≤Q.relative+1 := by unfold Target.relative; linarith [Q.usable,Q.bound,Q.pos]
        have sums := shops G L Q.halo n 3 P.top.width Q.ε (Q.relative+1) Q.usable rel Q.grants.2.1
          h₁ h₂ (Rate.const P.top.paths) (1/2) 0 (-(1/4)) le_rfl (by norm_num) (by norm_num)
        filter_upwards [ready,sums] with x ready total c f S T R C H stamp
        have hs := H.laws.data.funds
        obtain ⟨Ξ,paid⟩ := ready c f S T R C H (shape (hs.length_eq.trans len.symm)
            (hs.funds.atStep.trans ord.symm)) stamp
        refine ⟨a x,b x,B x,d x,r x,C₀,k,Ξ,?_,paid⟩
        have hin := H.laws.intake
        have bounds := hin.cap.paths
        have price := hin.window.2
        rw [hs.length_eq] at bounds price
        have hor : |-Raw.orientation*R.beta|≤2*betaF G x L := by
          rw [abs_mul,abs_neg,abs_of_nonneg Raw.orientation_range.1.le,abs_of_nonneg hin.positive.le]
          exact (mul_le_of_le_one_left hin.positive.le Raw.orientation_range.2).trans price
        have receipt := total c f S hs.length_eq R.path.cubic bounds.three (-Raw.orientation*R.beta) hor
        convert receipt using 2 with i
        simp only [Real.rpow_zero,one_mul,Kiln.bill,abs_mul]
        split <;> ring
      have all := eventually_all.mpr fun n : Fin (l+1) => eventually_all.mpr (each n)
      filter_upwards [all] with x h n hn j hj
      exact h ⟨n,Nat.lt_succ_of_le hn⟩ ⟨j,Nat.lt_succ_of_le hj⟩
    · exact Eventually.of_forall fun _ _ _ _ _ _ _ S _ _ _ H _ => False.elim
        (lacks ⟨S.patch,H.laws.data.funds.funds.kernel,H.laws.data.funds.length_eq,
          H.laws.data.funds.funds.atStep⟩)

end YM.Integration.WilsonHeldCubicElection
