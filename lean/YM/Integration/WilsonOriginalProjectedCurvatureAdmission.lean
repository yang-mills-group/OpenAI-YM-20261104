import YM.Integration.WilsonOriginalProjectedCurvatureMarkerIncome

/-! Reprice a complete original independent cohort at a declared positive
application expense, with an exact inverse on every occupied mode. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureAdmission
open Function Finset Lattice Wilson RG Source Labels Marker
open PhysicalNext.Repeat.Legato LocalComparison ComparisonDensity.Address
open Comparison.Density.RenderM MergeProof.Accent FVA1
open ActualOriginalQReaders ActualOriginalQPackets NativeCurvatureTensor
open WilsonOriginalProjectedCurvatureBudget WilsonOriginalProjectedCurvatureSalary
open WilsonOriginalProjectedCurvaturePassport WilsonOriginalProjectedCurvatureEnvelope
open FullQLocal FullQLocal.RenderedStep
open WilsonOriginalProjectedCurvatureCredits
open scoped Classical BigOperators
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B) (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ) (N : ℕ)
  (σ : ℝ) (extra : V → ℕ) (w : V→ℝ)
local notation "Group" => Funded Q D u μ orders N σ
local notation "X" => WilsonOriginalProjectedCurvatureLamps.cohort Q D u μ orders N σ extra

theorem divide {a γ:ℝ} (pos:0<a)
    (paid : QuadraticLocal.Earn.Offers X w σ γ) : QuadraticLocal.Earn.Offers X (fun i=>w i/a) σ (γ/a) := by
  intro x
  have h := paid x
  let f (i:Group) := if (X i).center=x then Poly.toll w (X i).mode * (X i).height σ else 0
  let k (i:Group) := if (X i).center=x then Poly.toll (fun j=>w j/a) (X i).mode * (X i).height σ else 0
  have e (i:Group) : k i=f i/a := by
    have mode : (X i).mode=(Stock.census V).fire i.1.1.1 :=
      (WilsonOriginalProjectedCurvatureRender.geometry Q D u μ orders N i.1 σ (extra i.1.1.1) i.2).1
    by_cases c : (X i).center=x
    · simp only [k,f,if_pos c,mode,Poly.toll,Census.fire,Finset.prod_singleton]
      ring
    · simp [k,f,c]
  change (∀i, 0≤k i) ∧ Summable k ∧ (∑'i,k i)≤γ/a
  refine ⟨fun i => (e i).symm ▸ div_nonneg (h.1 i) pos.le,(hasSum_fintype k).summable,?_⟩
  rw [tsum_fintype,Finset.sum_congr rfl (fun i _=>e i),←Finset.sum_div]
  apply div_le_div_of_nonneg_right _ pos.le
  simpa only [tsum_fintype] using h.2.2

variable (run : Run G) (J : Request V)
local notation "charge₀" => WilsonOriginalProjectedCurvatureClock.charge run J u σ σ extra w
theorem original (K:ℕ) (hw:∀i,0<w i) :
    ∃C : ℝ, 0<C ∧ ∃ b : ℕ, ∀ (N p L : ℕ) (o : V → Site (run.family.side L p)) (orders : V→ℕ),
    (∀i,orders i≤K) → L≤N → 0<Pert.Asymptotics.regulatorRun run.family N p L →
    Pert.Asymptotics.regulatorRun run.family N p L≤1 → ∀ (Ω:ℝ),0<Ω →
    let D₀ := ActualOriginalQPointSetup.pointDatum run J p L o
    let X₀ := WilsonOriginalProjectedCurvatureLamps.cohort Q D₀ u (μ-run.family.S.scale N) orders N σ extra
    let a := max 1 ((C*(1+‖run.family.S.scale N‖)^b)*charge₀)
    (∀i,0<w i/(a*Ω)) ∧ QuadraticLocal.Earn.Offers X₀ (fun i=>w i/(a*Ω)) σ Ω⁻¹ ∧
      (∀k:(Stock.census V).Mode, Poly.toll (fun i=>w i/(a*Ω)) k*(a*Ω)^k.val.card = Poly.toll w k) := by
  obtain ⟨C,hC,b,h⟩:=WilsonOriginalProjectedCurvatureMarkerIncome.original (run:=run) (J:=J) (Q:=Q) (u:=u) (μ:=μ) (σ:=σ) (extra:=extra) (w:=w) K hw
  refine ⟨C,hC,b,?_⟩
  intro N p L o orders ho hL hg hx Ω hΩ D₀ X₀ a
  have pos:0<a:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  have offered:=divide Q D₀ u (μ-run.family.S.scale N) orders N σ extra (fun i=>w i/a) hΩ
    (h N p L o orders ho hL hg hx).2.1
  refine ⟨fun i=>div_pos (hw i) (mul_pos pos hΩ),?_,
    WilsonOriginalProjectedCurvatureMarkerIncome.recovery w (mul_pos pos hΩ)⟩
  simpa only [div_div,one_div] using offered

end YM.Integration.WilsonOriginalProjectedCurvatureAdmission
