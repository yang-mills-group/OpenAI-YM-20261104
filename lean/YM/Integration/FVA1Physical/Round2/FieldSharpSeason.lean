import YM.Integration.FVA1Physical.Round2.FieldSharpTransfer
import YM.Integration.FVA1Physical.Wilson.ExactOrder
import YM.Integration.FVA1Physical.Sources.Round2.FieldReceipt

/-! The sharp physical mixed field reading on the unchanged incoming action.
Only the native field certificate for the implementing step is consumed. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Filter Function Set Finset Lattice RG YM.Wilson Tree Precision Exterior Pressure
open RGComparison.Core16 RGComparison.Core16.Spool MSbar MSbar.Lis MSbar.Wave
open MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Mosaic MSbar.Bulk
open MSbar.Bakery MSbar.Whisk MSbar.Cacao MSbar.Rolling MSbar.Bakery.Film
open Push.Uniform YM.Integration.FVA1Physical.Wilson Next.SectorChange
open scoped Classical Topology
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

def PhysicalFieldComparison (A : Mosaic.Issue G) (χ : ChartRatio G) (y η : ℝ)
    (p L : ℕ) (part : Bool) (b : Site A.f) (Z : Positions (Primary A.c G)) : Prop :=
  ∀ (o : ι→Site A.f), (∀ i : Slice J, separation b (legs J o i).1 ≤ L*closeN y) →
    let g:=A.fClock
    |Bulk.expect A.S A.pre (postcard G A.c g Z) (fun U=>look part (Spool.tally J o U)) -
      taste p (bulkColumn A χ (g•Z) (jointFieldBank J A o part) p) g| ≤ g^((p:ℝ)+1-η)

theorem inherited_field_season (V : Voice G) (clear : Clear G V) (χ : ChartRatio G)
    (hχ : LocalRatio χ) (simple : G.Simple) (H H' : RG.Stage) (P : Patch) (K : KernelChoices)
    (branch : P.Branches K G) (p s L : ℕ) (part : Bool) {D η : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hp : η < (p:ℝ)+1) :
    ∀ᶠ x : ℝ in atTop, ∀ (A : Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season V H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x; let n:=p+2
      Kind A.T → Expanse A.T 1 n → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s n →
      ∀ (b : Site A.f) (Z : Positions (Primary A.c G)), ‖Z‖ ≤ D →
      FieldPort A χ V n L J part y (y^pawn n) b Z →
      PhysicalFieldComparison J A χ y η p L part b Z := by
  filter_upwards [mixed_field_sharp_transfer J V clear χ hχ simple H H' P K branch p s L part hD hη hp,
    same_order_field_rows J V clear χ hχ simple H H' P K branch (p+2) s 0 L part hD
      (div_pos hη (by norm_num : (0:ℝ)<8))] with x transfer buyer
  intro A patch kernel season y n kind plane wedge b Z hZ ports o near
  have hg : 0≤A.fClock := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have scaled : ‖A.fClock • Z‖ ≤ A.fClock*D := by rw [norm_smul,Real.norm_of_nonneg hg];gcongr
  have book:=buyer A b patch kernel season kind plane wedge (A.fClock•Z) scaled o near
  have ha : 0≤αm y := by unfold αm hatW Alto.flurry;positivity
  apply transfer A patch kernel season kind plane wedge Z b o hZ near
  · intro i _ hi
    rw [normalizedRows_read]
    exact Bout.looks ha (book i hi)
  · intro pal U hU
    have pay:=ports pal o near U hU
    exact pay

end YM.Integration.FVA1Physical.Round2.Curvature
