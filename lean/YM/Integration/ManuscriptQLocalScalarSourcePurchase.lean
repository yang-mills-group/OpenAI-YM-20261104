import YM.Integration.PhysicalAffineScalarRetainedSource
import YM.Integration.ManuscriptQLocalWindowPurchase

/-! Before the physical clock is chosen, purchase the actual independently
specified scalar-source order. Its period and positive temperature are
proved from the same chosen Run at every admitted interior stage. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarSourcePurchase
open Function Filter Lattice Wilson RG Tree Precision Pressure Supply Testing Stores
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Org Input Push Push.PriceCompiler Push.SectorMeasure Next.SectorChange Next.SectorChange.Rows
open AnalyticBridge AnalyticBridge.GaussianFieldAlignment AnalyticBridge.SectorAffine
open Progress.DirectedRecipe RG.Shoot Next.SectorChange.Gaussian FreeResolvent FreeResolvent.Affine
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open scoped Classical Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge}

structure Prices where
  spatial : ℝ
  ordinary : ℝ
  discarded : ℝ
  spatial_pos : 0<spatial
  ordinary_pos : 0<ordinary
  discarded_pos : 0<discarded

/-- The full source of the independently prescribed Gaussian stationary square. -/
def Bought {c f : Side} (S : StepData c f) (T : Tube G S) (Pt : Teller G) (n : ℕ) (x : ℝ) (r : Prices) :=
  ∀ (_F : Forest S.ratio) (k : S.Choices) (i : Rows.Receipt G S),
    ContDiffAt ℝ n (fun B : Vec G c 1 => PhysicalAffineScalarUncut.offset T k B i) 0 ∧
    ∀ (m : ℕ), m ≤ n → ∀ l : Fin m → raw G c,
    Real.exp (r.spatial*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l)) *
      |iteratedFDeriv ℝ m (fun B : Vec G c 1 => PhysicalAffineScalarUncut.offset T k B i) 0 (ray G c∘l)| ≤ (temp x)⁻¹^m * (r.ordinary*fiery G x S.patch.L) + (|slip| * r.discarded)*
        Real.exp (-ConditionalAffineSourcePrices.rate Pt S.patch.L*(till x:ℝ))

def Offer (Pt : Teller G) (P : Patch) (n : ℕ) (x : ℝ) (r : Prices) := 0<temp x ∧
  ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Pt.Funds S T → 100*(1+radiusB x) ≤ c.val → Bought S T Pt n x r

def Paid (n : ℕ → ℕ → ℕ) : Prediction G := fun {M} {D} {A} _ => ∃ r : ℕ → ℕ → Prices,
  ∀ j x, A.delay.betaEntry j ≤ x → ∀ i (st : StepStages j i) (fr : M.p.first ≤ i),
    Offer (query M.p M.K j i) (Clockwork.patch D st fr) (n j i) x (r j i)

/-- The constants and common stage threshold are chosen before the period,
forest, marks, physical stage and Run. This purchase leaves the price map fixed. -/
theorem prepaid (n : ℕ → ℕ → ℕ) (s : Sheet G) (K : MapPrices) : Prepaid (Paid n) s K := by
  intro _ _ _ _ _ _ _
  refine ⟨fun _ => 0,fun l _ D _ _ _ _ _ protection _ _ V _ => ?_⟩
  let s' := ThroughLaunch.raise s l
  have rows (j i : ℕ) : ∃ r : Prices, ∀ᶠ x : ℝ in atTop, ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      Offer (query s' K j i) (Clockwork.patch D st fr) (n j i) x r := by
    by_cases hi : StepStages j i ∧ s'.first ≤ i
    · let P := Clockwork.patch D hi.1 hi.2
      obtain ⟨d,N,M,hd,hN,hM,H⟩ := PhysicalAffineScalarRetainedSource.full G P (query s' K j i) (s'.has P) (n j i)
      refine ⟨⟨d,N,M,hd,hN,hM⟩,?_⟩
      filter_upwards [H,monitors G P.L] with x hx htmp
      intro st fr
      refine ⟨htmp.1,?_⟩
      intro c f S T hS hT hc F k z
      simpa only [hS] using hx S T hS hT hc htmp.1 F k z
    · exact ⟨⟨1,1,1,zero_lt_one,zero_lt_one,zero_lt_one⟩,Eventually.of_forall fun _ st fr => False.elim (hi ⟨st,fr⟩)⟩
  choose r hr using rows
  have simultaneous (j : ℕ) : ∀ᶠ x : ℝ in atTop,
      ∀ i (st : StepStages j i) (fr : s'.first ≤ i),
        Offer (query s' K j i) (Clockwork.patch D st fr) (n j i) x (r j i) := by
    let E := fun (i : ℕ) (x : ℝ) => ∀ (st : StepStages j i) (fr : s'.first ≤ i),
      Offer (query s' K j i) (Clockwork.patch D st fr) (n j i) x (r j i)
    have prices := eventually_transitions j atTop E (fun i _ => hr j i)
    exact prices.mono fun x hx i st fr => hx i st st fr
  obtain ⟨β,_,hβ,ready⟩ := collect_upper V.betaEntry _ simultaneous
  let W : Delays protection := {V with betaEntry:=β}
  refine ⟨W,⟨hβ,le_rfl,le_rfl,le_rfl⟩,fun W' hW _ _ _ _ => ?_⟩
  intros
  exact ⟨r,fun j x hx => ready j x ((hW.beta j).trans hx)⟩

/-- The preorder can be used with the original program selection at every authentic retargeted price. -/
theorem allPrices (n : ℕ → ℕ → ℕ) : FundedPredictionSupply.AllPrices (@Paid G n) := fun s _ => prepaid n s _

/-- No size, temperature, path, branch or forest obligation is left in this
selected-stage form of the full signed ordinary-source price. -/
theorem realized (R : Run G) {n : ℕ → ℕ → ℕ} (paid : Paid n R.kit) (N m p : ℕ) (hm : m<N) :
    let S := R.alloy.B.a.clock.op m p
    let x := R.alloy.B.a.clock.hatBeta m
    let j := R.alloy.B.a.clock.J (m+1)
    let i := R.alloy.B.a.clock.J m
    let T := ships R.alloy.B N m p
    0<temp x ∧ Bought S T (query R.metals.p R.metals.K j i) (n j i) x (paid.choose j i) := by
  intro S x j i T
  let B := R.alloy.B
  have st := step_paid B.a m
  have fr := first_le B.valid m
  have hL : S.patch.L=R.rolls.L j := block_eq B.valid m
  have hJ : S.patch.J=j := (Testing.proceeds B N m p hm).atStep
  have hP : S.patch=Clockwork.patch R.rolls st fr := by
    cases h : S.patch
    rw [h] at hL hJ
    unfold Clockwork.patch
    congr
  have hs : 100*(1+radiusB x) ≤ (B.a.S.side m p).val := by rw [add_comm 1]; exact B.a.fits.sizeT m p
  have h := paid.choose_spec j x (B.valid.pays m) i st fr
  exact ⟨h.1,h.2 S T hP (Testing.proceeds B N m p hm) hs⟩

end YM.Integration.ManuscriptQLocalScalarSourcePurchase
