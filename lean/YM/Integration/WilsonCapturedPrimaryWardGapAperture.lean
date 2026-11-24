import YM.Integration.WilsonCapturedPrimaryWardGapRestoration
import YM.Integration.WilsonCapturedPrimaryWardSeats
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWardGapAperture
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Push
open Extraction Extra.Histories PhysicalNext.Repeat.Legato
open Bandage Stock RG16.Literal RG05Readout Native Address Many Records Harvest Copper
open RG12 RG17 Climb Trace.Pilot MergeProof Next.Extract PhysicalNext.Repeat Legato
open MergeProof.Ribbons MergeProof.Ribbons.ManyCopies Cells Accent Motion
open Trace.Physical.GermGraph GridApprox Next.Rank Ribbon Trace.Physical
open XSpace XSpace.Rose Push.GridApprox OPE OPE.Cards OPE.Orbits Spec
open WilsonCapturedPrimaryPhysicalArray WilsonCapturedPrimaryActiveArms
open WilsonCapturedPrimaryFaceWallet WilsonThermometerOwnOffsetField WilsonReflectedPhysicalRate
open WilsonCapturedPrimaryWardRestoration
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {n : ℕ} {f : Extraction.Order}
variable (V : ∀ d, SectionData (R.family.labels.level d)) (W : Mark.Weave G)
  (P : ∀ d, (ℕ×ℕ) → (R.family.label d ≃ₗ[ℂ] R.family.label d)) (b : Presentation R.family)

open WilsonCapturedPrimaryWardGapHome (column)
open RG05Readout.Address

def scaled (l:ℕ) (d:Fin n→ℕ) (y:(i:Fin n)→Palette R.family (d i)) (i:Fin n) : Palette R.family (d i) :=
  ((R.family.S.a l:ℂ)^(d i)) • y i

def exposed {N p l:ℕ} (d:Fin n→ℕ) (o:Fin n→Site (R.family.side N p))
    (S:Shelf (N:=N) (p:=p) R l d o) (live:l≤N) (y:(i:Fin n)→Palette R.family (d i)) (i:Fin n) :=
  column R (p:=p) (S.route i) live (scaled R l d y i)

theorem funded {N p l:ℕ} (d:Fin n→ℕ) (o:Fin n→Site (R.family.side N p))
    (S:Shelf (N:=N) (p:=p) R l d o) (live:l≤N) (y:(i:Fin n)→Palette R.family (d i)) :
    WilsonCapturedPrimaryNamedReturn.primary R (p:=p) d S.route live (exposed R d o S live y) y := by
  intro i
  have nz : ((R.family.S.a l:ℂ)^(d i)) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (R.family.S.a_pos l).ne')
  rw [exposed,WilsonCapturedPrimaryWardGapHome.column,scaled,map_smul,Pi.smul_apply]
  let a : ℂ := (R.family.S.a l:ℂ)^(d i)
  let v := finer (S.route i) live (y i) (primaryLetter (d i))
  let line := (R.family.factory (d i) N p).terminal
  change line v = a⁻¹ • line (a • v)
  exact ((congrArg (a⁻¹ • ·) (line.map_smul a v)).trans (by rw [smul_smul,inv_mul_cancel₀ nz,one_smul])).symm

/-- The original fine repair and the reflected-arm bill use the same occupied radii. -/
theorem original (room : CellHyp R.family f) (simple : G.Simple)
    (slow : WilsonWindowReportingPace.Slow R.kit) (v J : ℕ) (wide : 4 < v)
    (φ : Test n) (d : Fin n → ℕ)
    (portfolio : ∀ d, Mark.Portfolio R.family.params (V d) (W d))
    (issued : Hearthside R.family V W P b (Bandage.fly R.alloy.B.a)) :
    ∀ᶠ r : ℝ in 𝓝[>]0, let l:=launch R simple v r
    ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε →
    ∀ᶠ z : ℕ × ℕ in f.fuse, ∃ live : l≤z.1, ∀ (o : Fin n → Site (R.family.side z.1 z.2)),
    WilsonCenteredCompactBooking.mass R φ r z o ≠ 0 → ∀ (axis : Option (Fin n))
      (S:Shelf (N:=z.1) (p:=z.2) R l d (registered o axis)) (s : Finset (Fin n))
      (x : (i : Fin n)→R.family.label (d i)) (y:(i:Fin n)→Palette R.family (d i)), (∀ i∈s, ‖x i‖ ≤ M) →
      let E := exposed R d (registered o axis) S live y
      PaidAt R.family.S z.1 z.2 J (R.family.beta z.1 z.2) ((∏i∈s,(1+size (y i)))*ε)
        (filed R d x s (registered o axis)-WilsonCapturedPrimaryWardGapFaces.adjusted R V P d x E s (registered o axis)) := by
  obtain ⟨A,nn,paid⟩ := WilsonCapturedPrimaryWardGapRestoration.original R V W P b room simple slow v J wide φ d portfolio issued
  filter_upwards [paid] with r bill
  obtain ⟨k,ready⟩ := bill.exists
  dsimp only
  intro M hM ε pos
  let l:=launch R simple v r
  let weight (i:Fin n) := A i*R.family.S.a k^(-(d i:ℝ)-1)+1+2*Fintype.card (R.family.labels.level (d i)).Index
  let angle (i:Fin n) := ‖(R.family.S.a l:ℂ)^(d i)‖
  let mass (s:Finset (Fin n)) := (((2:ℕ)^s.card-1:ℕ):ℝ)*∏ i∈s,(weight i*(1+M)+2*angle i)
  let δ (z:ℕ×ℕ) := Real.exp (-(1/64:ℝ)*R.family.S.scale z.1)
  have gone : Tendsto δ f.fuse (𝓝 0) := Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg (by norm_num) (R.family.S.divergent.comp (WilsonCapturedPrimaryWardRestoration.upper f)))
  have small (s:Finset (Fin n)) : ∀ᶠ z:ℕ×ℕ in f.fuse, δ z * mass s ≤ ε := by
    have limit : Tendsto (fun z=>δ z*mass s) f.fuse (𝓝 0) := by simpa using gone.mul_const (mass s)
    exact (limit.eventually_lt_const pos).mono (fun _ h=>h.le)
  filter_upwards [ready,eventually_all.mpr small] with z priced below
  obtain ⟨h,start,ink⟩ := priced
  refine ⟨start,?_⟩
  intro o support axis S s x y norm
  obtain ⟨inside,price⟩ := ink o support axis S s x (scaled R l d y)
  refine ⟨h,inside,price.trans ?_⟩
  have wp (i) : 0 ≤ weight i := by dsimp only [weight]; positivity [nn i,R.family.S.a_pos k]
  have ap (i) : 0 ≤ angle i := norm_nonneg _
  have tv : 0 ≤ ∏i∈s,(1+size (y i)) := Finset.prod_nonneg (fun i _=>by linarith [size_ge (y i)])
  have factor_bound : ∏i∈s,(factor R k (d i) (A i) (x i)+2*size (scaled R l d y i)) ≤
      ∏i∈s,((weight i*(1+M)+2*angle i)*(1+size (y i))) := by
    apply Finset.prod_le_prod
    · intro i _
      exact add_nonneg (mul_nonneg (wp i) (by positivity)) (mul_nonneg (by norm_num) (size_ge _))
    · intro i hi
      simp only [scaled,size_smul]
      change weight i*(1+‖x i‖)+2*(angle i*size (y i)) ≤ _
      have bound := mul_le_mul_of_nonneg_left (norm i hi) (wp i)
      have budget := mul_nonneg (mul_nonneg (wp i) (show 0≤1+M by linarith)) (size_ge (y i))
      nlinarith [ap i]
  calc
    _ ≤ (((2:ℕ)^s.card-1:ℕ):ℝ)*δ z*∏i∈s,((weight i*(1+M)+2*angle i)*(1+size (y i))) :=
        mul_le_mul_of_nonneg_left factor_bound (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    _ = (δ z*mass s)*(∏i∈s,(1+size (y i))) := by rw [Finset.prod_mul_distrib]; dsimp only [mass]; ring
    _ ≤ ε*(∏i∈s,(1+size (y i))) := mul_le_mul_of_nonneg_right (below s) tv
    _ = _ := mul_comm _ _

end YM.Integration.WilsonCapturedPrimaryWardGapAperture
