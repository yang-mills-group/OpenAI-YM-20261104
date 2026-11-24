import YM.Integration.WilsonIndependentCapturedRootLimit
import YM.Integration.WilsonOriginalCappedDeckHearing

/-! The occupied group-field binding on the actual auxiliary boards pays
the quadratic rooted charge of the signed cover coefficient. Only a fixed
finite collection of directions must fit the chosen lift at a time. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedAngularWinding
open Filter Finset Lattice RG RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Spatial
open RegulatorIR.Budget.FVAAlt2.Wind RegulatorIR.Budget.FVAAlt2.Wind.Pine RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open ActualRunAdmissionScales Pert.Asymptotics
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical TwoReset PhysicalNext.Repeat.Legato
open WilsonOriginalOccupiedAngularPage WilsonOriginalPolarizedAngularPage WilsonOriginalLinkedAngularPage
open WilsonIndependentCapturedRootTariff
open scoped BigOperators Topology ENNReal Classical

variable {G : Gauge} {W : Type} {M : W → ℕ} {X Y : Page M → Type}
abbrev SiteSlot (G : Gauge) (n : Side) := Site n × Stationary.Loc G 1

def printed {r : ℕ} {n : Side} (F : Stationary.Link G n → ℂ) (x : Tuple (SiteSlot G n) r) : ℝ :=
  (coefficient r F x).re / (r.factorial:ℝ)

private theorem bill {r : ℕ} {n : Side} (F Z : Stationary.Link G n → ℂ) (x : Tuple (SiteSlot G n) r) :
    ‖printed F x - printed Z x‖ ≤ ‖coefficient r F x - coefficient r Z x‖ := by
  unfold printed
  rw [←sub_div,←Complex.sub_re,norm_div,Real.norm_of_nonneg (Nat.cast_nonneg (α:=ℝ) r.factorial)]
  apply (div_le_self (norm_nonneg _) (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos r))).trans
  exact Complex.abs_re_le_norm _

theorem original (R : Run G) (simple : G.Simple) (fund : RG05Preconstruction.ReadoutPurchase R.b)
    (a b c q r : ℕ) (leg : Fin r) :
    ∀ᶠ m : ℕ in atTop, ∀ N per : ℕ, m<N →
      let n := R.family.side m per
      let g := regulatorRun R.family N per (m+1)
      let H := R.family.path.levels.clock.hatBeta m
      ∀ (S : Sky X Y) (root : W → Room) (page : Page M) (sides : ℕ → Side)
        (divide : ∀ k, n.val ∣ (sides k).val)
        (arc : Arch (X page) atTop (fun k=>SiteSlot G (sides k)))
        (F Z : (k:ℕ) → Stationary.Link G (sides k) → ℂ) (A B : Packet (X page) r)
        (l u v : (k:ℕ) → Site (sides k)) (span : (k:ℕ) → Positions (sides k) (Stationary.Loc G 1) r → ℝ)
        (ρ D : ℝ) (spent fare : ℕ → ℝ),
      above atTop A (fun k=>Packet.offer (arc.spring k) (printed (F k))) →
      above atTop B (fun k=>Packet.offer (arc.spring k) (printed (Z k))) →
      0<ρ → ρ⁻¹ ≤ H^b → 0≤D → D≤(n.val:ℝ)/8 →
      (∀ k, ContDiff ℝ r (F k) ∧ ContDiff ℝ r (Z k) ∧
        (∀ h, board (divide k) (u k) (move G) (F k) h=board (divide k) (v k) (move G) (Z k) h) ∧
        (∀ x, (separation (l k) (x leg).1:ℝ) ≤ span k x + D) ∧
        (∑ x, Real.exp (ρ*span k x)*‖coefficient r (F k) x‖) ≤ spent k ∧
        (∑ x, Real.exp (ρ*span k x)*‖coefficient r (Z k) x‖) ≤ fare k ∧
        2*(spent k+fare k) ≤ H^a*g^(-(c:ℝ))) →
      (∀ x : Tuple (X page) r, ∀ᶠ k : ℕ in atTop,
        0 ≤ span k (arc.gloss.pack k x) ∧ ∀ j, dist (root page.bindW) ((S.maps page).pos (x j)) ≤
          (span k (arc.gloss.pack k x)+D)*S.radius page) →
      markQ (S.coverQ root 2 page) (A-B) ≤ ENNReal.ofReal (cost D ρ * g^q) := by
  filter_upwards [WilsonOriginalCappedDeckHearing.original R simple fund a b c q r leg] with m ready
  intro N per cutoff n g H S root page sides divide arc F Z A B l u v span ρ D spent fare
    original prescribed strip aperture nonneg short funds physical
  apply WilsonIndependentCapturedRootLimit.passed S root page original prescribed nonneg strip
  intro E
  have hits : ∀ᶠ k:ℕ in atTop, ∀ x ∈ E, arc.gloss.spring k (arc.gloss.pack k x) = x ∧
      0 ≤ span k (arc.gloss.pack k x) ∧ ∀ j, dist (root page.bindW) ((S.maps page).pos (x j)) ≤
        (span k (arc.gloss.pack k x)+D)*S.radius page := by
    exact (eventually_all_finset E).mpr (fun x _ => (arc.gloss.tides x).and (physical x))
  filter_upwards [hits] with k fixed
  refine ⟨fun x=>span k (arc.gloss.pack k x),fun x hx=>(fixed x hx).2,?_⟩
  let p : Tuple (X page) r → Tuple (SiteSlot G (sides k)) r := arc.gloss.pack k
  let target := fun x=>Real.exp (ρ*span k x/2)*‖coefficient r (F k) x-coefficient r (Z k) x‖
  obtain ⟨sf,sz,binding,reach,left,right,total⟩ := funds k
  have sheet := ready N per cutoff (sides k) (divide k) (l k) (u k) (v k) (F k) (Z k) sf sz binding
    (span k) ρ D (spent k) (fare k) strip aperture short reach left right total
  calc
    _ ≤ ∑ x ∈ E, target (p x) := by
      apply sum_le_sum; intro x hx
      have enter (h : Packet (SiteSlot G (sides k)) r) : Packet.offer (arc.spring k) h x = h (p x) := by
        have same := Packet.offer_eq (arc.spring k) h (p x)
        change Packet.offer (arc.spring k) h (arc.gloss.spring k (p x)) = h (p x) at same
        rwa [(fixed x hx).1] at same
      exact mul_le_mul_of_nonneg_left (by rw [enter,enter]; exact bill (F k) (Z k) _) (Real.exp_pos _).le
    _ = ∑ y ∈ E.image p, target y := (sum_image (fun x hx y hy he=>
      (fixed x hx).1.symm.trans ((congrArg (arc.gloss.spring k) he).trans (fixed y hy).1))).symm
    _ ≤ ∑ y, target y := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    _ ≤ _ := sheet

end YM.Integration.WilsonIndependentCapturedAngularWinding
