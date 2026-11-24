import YM.Integration.WilsonPhysicalMarkedDefectPhysicalHistory
import YM.Integration.WilsonPhysicalMarkedDefectHistoryRates
import YM.Integration.WilsonWindowBookPurchase

/- The width chosen by the actual common-rent physical constructor on a fixed
scalar test disk is a finite table indexed before the cutoff and period.
Book its reciprocal on the original delayed temperature, before selecting R. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
open Function Filter Set Finset Lattice Wilson RG RG.Supply Source Pressure Input Org Precision
open Progress.DirectedRecipe Payments Push.AbsoluteSums Push.PriceCompiler
open Next.Scheduling Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces Extra.Iteration Extra.Histories
open QuadraticLocal QuadraticLocal.Mentor QuadraticLocal.Earn QuadraticLocal.Affinity QuadraticLocal.Advent QuadraticLocal.Advent.Sycamore QuadraticLocal.Syl
open Marker RG3.Annuncia MergeProof.Accent FVA1Physical.Round2.Curvature FVA1Physical.Round2.CP5
open scoped Topology BigOperators Classical

def marks : Census Unit := Stock.census Unit
def chart (_ : Unit) : Set ℂ := {z | ‖z‖≤1}
def reader (_ : Unit) : ℂ →ₗ[ℝ] ℂ := LinearMap.id
theorem admissible (i:Unit) (z:ℂ) (h:z∈chart i) : ‖reader i z‖≤1 := h

def radius {G:Gauge} {d:ℕ} (σ:ℝ) (a:CoverLabel G d) : ℝ :=
  (engineering_fleet (Replica (fun _:Unit=>()) marks) (fun _:Unit=>a) σ reader chart admissible).choose

theorem positive {G:Gauge} {d:ℕ} (σ:ℝ) (a:CoverLabel G d) : 0 < radius σ a :=
  (engineering_fleet (Replica (fun _:Unit=>()) marks) (fun _:Unit=>a) σ reader chart admissible).choose_spec.1

variable {G:Gauge} {M:Metals G} (D:Rolls M.p)
    (S:Roots (G:=G) M.p.profile M.K M.p.kernel) (φ:ℕ→ℕ)

def Paid {P:Protection D} (W:Delays P) : Prop :=
  ∀ (x k d:ℕ), k≤x → d≤x → ∀ a:CoverLabel G d, ∀ t:ℝ, W.betaEntry x ≤ t →
    (radius (Poetry.Agenda.seed S φ (Burn.horizon k) x) a)⁻¹ ≤ t^((x:ℝ)+1)⁻¹

theorem priced {P:Protection D} (W:Delays P) :
    ∃ V : Delays P, DelayLe W V ∧ ∀ Z : Delays P, DelayLe V Z → Paid D S φ Z := by
  let F (x:ℕ) (t:ℝ) := ∀ k∈Finset.Iic x, ∀ d∈Finset.Iic x, ∀ a:CoverLabel G d,
    (radius (Poetry.Agenda.seed S φ (Burn.horizon k) x) a)⁻¹ ≤ t^((x:ℝ)+1)⁻¹
  have occur (x:ℕ) : ∀ᶠ t:ℝ in atTop, F x t := by
    apply (eventually_all_finset (Finset.Iic x)).2
    intro k _
    apply (eventually_all_finset (Finset.Iic x)).2
    intro d _
    have each (a:CoverLabel G d) := (tendsto_rpow_atTop (by positivity : 0<((x:ℝ)+1)⁻¹)).eventually_ge_atTop
      ((radius (Poetry.Agenda.seed S φ (Burn.horizon k) x) a)⁻¹)
    filter_upwards [(eventually_all_finset (Finset.univ : Finset (CoverLabel G d))).2 (fun a _=>each a)] with t h
    exact fun a=>h a (Finset.mem_univ _)
  obtain ⟨A,_,lower,agenda⟩ := collect_upper W.betaEntry F occur
  refine ⟨{W with betaEntry:=A},⟨lower,le_rfl,le_rfl,le_rfl⟩,?_⟩
  intro Z growth x k d hk hd a t ht
  exact agenda x t ((growth.beta x).trans ht) k (Finset.mem_Iic.mpr hk) d (Finset.mem_Iic.mpr hd) a

def law (G:Gauge) (φ:ℕ→ℕ) : VowsR.LawScroll G φ where
  clause M D _ _ _ _ _ _ _ _ S _ _ _ W := Paid (M:=M) D S φ W
  permits := by
    intro s T Q C E he
    refine ⟨fun _=>0,?_⟩
    intro ℓ _ D q Wp Z Q' S' h Pw T₀ Y B hP W
    exact priced (M:=ThroughLaunch.currency s T ℓ) D Q φ W

/-- The genuine selector may use its final, different MapPrices.  No equality
between that price and an independently compiled roots invoice is required. -/
theorem permitted (s : Sheet G) (price : MapPrices) :
    WilsonWindowBookPurchase.Permitted (law G φ) s price := by
  intro Q C E he
  refine ⟨fun _=>0,?_⟩
  intro ℓ _ D w u Z post scouts h P θ tab B hB W
  exact priced (M:=WilsonWindowBookPurchase.raised s price ℓ) D Q φ W

variable (R:Legato.Run G) (simple:G.Simple)
    (roots:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)

include simple

theorem observed (paid:Paid R.rolls roots φ R.alloy.delay) (b k d:ℕ)
    (hk:k ≤ R.alloy.B.a.clock.J (b+1)) (hd:d ≤ R.alloy.B.a.clock.J (b+1)) (a:CoverLabel G d) :
    (radius (Poetry.Agenda.seed roots φ (Burn.horizon k) (R.alloy.B.a.clock.J (b+1))) a)⁻¹ ≤
      (R.alloy.B.a.clock.hatBeta (b+1))^((R.alloy.B.a.clock.J (b+1):ℝ)+1)⁻¹ := by
  apply paid _ k d hk hd a
  exact (R.alloy.B.valid.pays b).trans (Push.Corrected.Last.band_le R.alloy.B.a simple (Nat.le_succ b))

theorem subpower (paid:Paid R.rolls roots φ R.alloy.delay) (ε:ℝ) (hp:0<ε) :
    ∀ᶠ b:ℕ in atTop, ∀ k d, k ≤ R.alloy.B.a.clock.J b → d ≤ R.alloy.B.a.clock.J b →
      ∀ a : CoverLabel G d, (radius (Poetry.Agenda.seed roots φ (Burn.horizon k) (R.alloy.B.a.clock.J b)) a)⁻¹ ≤
        (R.alloy.B.a.clock.hatBeta b)^ε := by
  obtain ⟨K,hK⟩ := exists_nat_ge ε⁻¹
  filter_upwards [eventually_ge_atTop 1,R.alloy.B.a.fits.deep.eventually_ge_atTop K,
     (Sycamore.too R simple).eventually_ge_atTop 1] with b hb hbK hot
  intro k d hk hd a
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have size : ε⁻¹ ≤ (R.alloy.B.a.clock.J (b+1):ℝ)+1 := by
    have h : (K:ℝ)≤(R.alloy.B.a.clock.J (b+1):ℝ) := by exact_mod_cast hbK
    linarith
  have spent : ((R.alloy.B.a.clock.J (b+1):ℝ)+1)⁻¹ ≤ ε := by
    rw [←one_div,div_le_iff₀ (by positivity)]
    simpa only [mul_inv_cancel₀ hp.ne'] using mul_le_mul_of_nonneg_left size hp.le
  exact (observed φ R simple roots paid b k d hk hd a).trans (Real.rpow_le_rpow_of_exponent_le hot spent)

end YM.Integration.WilsonPhysicalMarkedDefect.SingletonRent
