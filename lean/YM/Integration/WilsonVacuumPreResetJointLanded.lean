import YM.Integration.WilsonVacuumPreResetJointPublished

/-! A signed finite earlier correction field, on the actual protected sheet,
is compared with the complete numerical forest input obtained from each of
its independently registered winding polynomials. Every torus sum is taken
before its finite size is charged. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointLanded
open WilsonCoeffUV
open Filter Function Finset Lattice Wilson RG Laurent Bloch Exterior Blue FreeResolvent Precision
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic Stationary Work.G05 Tree Pressure Pressure.Stores Pressure.Tube
open Push Push.Uniform Push.AbsoluteSums ConnectedActivityE6 SliceRows Coat Matter Blaze RG01.Sounder
open WilsonVacuumPreResetJointField WilsonVacuumPreResetJointRaw WilsonVacuumPreResetJointStack
open WilsonVacuumPreResetJointPublished WilsonLimitConstruction Analysis
open private collected from YM.Integration.WilsonVacuumPreResetJointSite
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {σ C : ℝ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def numerical (a : PrismA G) (d : ℕ) (Z : Coat T F) : Arguments G c f → ℝ :=
  blockTaylor d (polynomial a d ∘ blockTaylor d (WilsonCubicOriginalTorus.coordinates G f ∘ changes univ Z))

theorem tabulated (a : PrismA G) (hs : 0 < σ) (money : Commission a.cells σ C a.grade)
    (X : Coat T F) (p : Molecule S) (kept : p.toLeft=∅)
    (sun : flags (Pressure.temp X.x) X.V=∅) (Y : F.Slice G) (d : ℕ) :
    let Z := (Matter.planted X p).wrapY Y
    blockTaylor d (realRead a ∘ field univ Z) = numerical a d Z := by
  intro Z
  unfold blockTaylor numerical
  apply Finset.sum_congr rfl
  intro k hk
  have hp := WilsonVacuumPreResetJointPublished.seated a hs money X p kept sun Y d k (by simpa using hk)
  simp only [Tensor.coeff,Z,hp]

theorem measured (a : PrismA G) (hs : 0 < σ) (money : Commission a.cells σ C a.grade)
    (X : Coat T F) (p : Molecule S) (kept : p.toLeft=∅)
    (sun : flags (Pressure.temp X.x) X.V=∅) (Y : F.Slice G) (ρ : ℝ) (r j : ℕ)
    {y : E} {z : E → Arguments G c f} {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    let Z := (Matter.planted X p).wrapY Y
    Brush j ((Fintype.card (Site f):ℝ) * (|ρ| * rowBill G σ C (a.rise+2) j r t)) 1
      (fun w => ρ*(FundedPeriodAction.action f a (field univ Z (z w)) - numerical a (r+2) Z (z w))) y := by
  intro Z
  let W : book G (a.rise+2) := ⟨a.cells,σ,C,hs,money.toll,money.hue⟩
  let d := r+2
  let h := j+d+1
  have cap (v : Arguments G c f) (_ : ‖v‖ ≤ t) :
      Brush h ((Fintype.card (Site f):ℝ)*(C*W.premium (linkFee G h) h)) 1 (realRead a ∘ field univ Z) v := by
    exact collected (fun s w => W.settle s (field univ Z w))
      (fun s => W.settle_notes _ (links univ Z h) s v)
  have price := (LocalTaylorR2.Mesh.priced (d:=d) ht ht' cap read).smul ρ
  rw [tabulated a hs money X p kept sun Y d] at price
  refine price.climb (le_of_eq ?_) (le_refl (1:ℝ))
  unfold rowBill W book.premium
  rw [Real.norm_eq_abs]
  dsimp only [h,d]
  ring

def filed (A : SeriesA G) (u : ℝ) (d : ℕ) (Z : Coat T F) (v : Arguments G c f) : ℝ :=
  (A.map fun a => u^(a.grade-a.rise)*numerical a d Z v).sum

theorem original (A : SeriesA G) (hs : 0 < σ) (money : Draw A σ C)
    (X : Coat T F) (p : Molecule S) (kept : p.toLeft=∅)
    (sun : flags (Pressure.temp X.x) X.V=∅) (Y : F.Slice G) (ρ u : ℝ) (r j : ℕ)
    {y : E} {z : E → Arguments G c f} {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1) (read : Brush j t 1 z y) :
    let Z := (Matter.planted X p).wrapY Y
    Brush j ((Fintype.card (Site f):ℝ)*charge A σ C ρ u j r t) 1
      (fun w => ρ*(FundedPeriodAction.rendered f A u (field univ Z (z w)) - filed A u (r+2) Z (z w))) y := by
  intro Z
  induction A with
  | nil =>
    simpa [charge, FundedPeriodAction.rendered, filed] using (Brush.certified (k:=j) (x:=y) zero_le_one (0:ℝ))
  | cons a A ih =>
    have ha := measured a hs (money.2 a List.mem_cons_self) X p kept sun Y (ρ*u^(a.grade-a.rise)) r j ht ht' read
    have hr := ih ⟨money.1, fun b hb => money.2 b (List.mem_cons_of_mem _ hb)⟩
    have both := ha.gathering hr
    rw [show (Fintype.card (Site f):ℝ)*charge (a::A) σ C ρ u j r t =
        (Fintype.card (Site f):ℝ)*(|ρ*u^(a.grade-a.rise)| * rowBill G σ C (a.rise+2) j r t) +
          (Fintype.card (Site f):ℝ)*charge A σ C ρ u j r t by
      simp only [charge, List.map_cons, List.sum_cons, mul_add]] 
    apply both.shimmy (Filter.Eventually.of_forall fun w => ?_)
    simp only [FundedPeriodAction.rendered,filed,List.map_cons,List.sum_cons]
    ring

end YM.Integration.WilsonVacuumPreResetJointLanded
