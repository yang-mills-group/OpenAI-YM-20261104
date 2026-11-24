import YM.Integration.FVA1Physical.Wilson.ComposedDegree

/-! A full-degree rooted bank remains an input at arbitrary requested
derivative order. The admissible power margin for one inherited transition
depends only on the preceding fixed degree and perturbative order. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open PhysicalNext.Repeat.Legato Push.Uniform MSbar.Midpoint MSbar.Bakery.Film
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open scoped Classical Topology BigOperators
variable {G:Gauge}

def bankDegree (p m:ℕ) := m*(p+1+p)+2

def bankSlack (p m ℓ:ℕ) := inputSlack p m (bankDegree p m) (margin_pos ℓ)/2/2

theorem bankSlack_pos (p m ℓ:ℕ) : 0 < bankSlack p m ℓ :=
  half_pos (half_pos (inputSlack_pos p m (bankDegree p m) (margin_pos ℓ)))

def BankPaid {c:Side} (b:Site c) (y:ℝ) (s p m:ℕ) (δ:ℝ) (T : Nesting G c) : Prop :=
  ∀ i ≤ p,(PowerSeries.coeff i T).totalDegree ≤ m ∧
    Vault (Measuring.chart c G) {b} (αm y) s m 0 (PowerSeries.coeff i T) (y^δ)

theorem BankPaid.through {c:Side} {b:Site c} {y δ:ℝ} {s p m:ℕ} {T:Nesting G c}
    (paid : BankPaid b y s p m δ T) (h:ℕ) {i:ℕ} (hi:i ≤ p) :
    Vault (Measuring.chart c G) {b} (αm y) s h 0 (PowerSeries.coeff i T) (y^δ) := by
  have a0 : 0 ≤ αm y := by unfold αm hatW Alto.flurry;positivity
  have cost := Bout.across (0:View (Primary c G)) (paid i hi).2 a0
    (show ‖(0:View (Primary c G))-0‖ ≤ 0 by simp) (paid i hi).1 h
  simpa only [add_zero,one_pow,mul_one] using cost

def inheritedBankGate (J:Voice G) (clear:Clear G J) (simple:G.Simple) (H H':RG.Stage) (P:Patch)
    (K:KernelChoices) (p m s ℓ:ℕ) : ℝ :=
  if br:P.Branches K G then if hm:1 ≤ m then (eventually_atTop.mp (inherited_field_rows J clear
    (Next.Foundations.chart G) (chart_ok G) simple H H' P K br p m (bankDegree p m) s hm (margin_pos ℓ))).choose
  else 0 else 0

def inheritedBankMenu (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) : ℝ :=
  ∑ e:Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1),
    |inheritedBankGate J clear simple H H' P K e.1.val e.2.1.val e.2.2.1.val e.2.2.2.val|

theorem inheritedBankGate_le (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':RG.Stage) (P:Patch) (K:KernelChoices) {p m s ℓ:ℕ}
    (hp:p ≤ H.order) (hm:m ≤ H.order) (hs:s ≤ H.order) (hl:ℓ ≤ H.order) :
    inheritedBankGate J clear simple H H' P K p m s ℓ ≤ inheritedBankMenu J clear simple H H' P K := by
  let e:Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1):=
    (⟨p,by omega⟩,⟨m,by omega⟩,⟨s,by omega⟩,⟨ℓ,by omega⟩)
  let f (e:Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1) × Fin (H.order+1)) :=
    inheritedBankGate J clear simple H H' P K e.1.val e.2.1.val e.2.2.1.val e.2.2.2.val
  exact (le_abs_self (f e)).trans (single_le_sum (fun i _=>abs_nonneg (f i)) (mem_univ e))

end YM.Integration.FVA1Physical.Wilson
