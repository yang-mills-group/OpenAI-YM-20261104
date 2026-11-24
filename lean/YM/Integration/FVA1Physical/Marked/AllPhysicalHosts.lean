import YM.Integration.FVA1Physical.Marked.AllHosts
import YM.RG20.Edict

/-! Every assignment of failed short sources to true vacuum hosts is summed
with one finite coincidence cost. Even after dividing by the stage's forced
allowance the geometric vacuum cost beats every prescribed inverse power
of the physical scale. The remaining visible factors are the local stencil
invoices and their individual one-tile support weights. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Finset Marker Qlocal Quipu Quipu.Sonnet Tern Push.AbsoluteSums
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {M : Type} [Fintype M] [Nonempty M]

theorem pattern_price (P : Rep G n) (pos : M → Site n) (C : M → ℝ) (hC : ∀ j, 0 ≤ C j)
    {κ : ℝ} (hk : 0 ≤ κ) (small : Push.Local.hitWidth P.p * κ ≤ 1) :
    (∑ s : M → M, patternInvoice P (fun j => Tale.court P.p.B (pos j)) C κ s) ≤
      Fintype.card (M → M) * (∏ j, Real.exp P.p.supportExponent * C j) * (Push.Local.hitWidth P.p * κ) := by
  let a := fun j => Real.exp P.p.supportExponent * C j
  let e := Push.Local.hitWidth P.p * κ
  have posE : 0 ≤ e := mul_nonneg (zero_le_one.trans (Push.Local.width_one_le _)) hk
  have price (s : M → M) : patternInvoice P (fun j => Tale.court P.p.B (pos j)) C κ s ≤ (∏ j,a j)*e := by
    have hι (k : representatives s) : 0 ≤ blockInvoice P (group s k) (fun j => Tale.court P.p.B (pos j)) C (head s k) κ := by
      unfold blockInvoice
      exact mul_nonneg (prod_nonneg fun j _ => mul_nonneg (Real.exp_nonneg _) (hC j))
        (mul_nonneg (Nat.cast_nonneg _) hk)
    refine (prod_le_prod (fun k _ => hι k) (fun k _ => local_block_invoice P _ pos C hC (head s k) hk)).trans ?_
    change (∏ k : representatives s, (∏ j ∈ group s k,a j)*e) ≤ _
    rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_coe]
    have geom : (∏ k : representatives s, ∏ j ∈ group s k, a j) = ∏ j,a j := by
      exact (Finset.prod_coe_sort (representatives s) (fun x : M => ∏ j ∈ univ.filter (fun v => s v = x), a j)).trans
        (prod_fiberwise_of_maps_to (s:=univ) (t:=representatives s) (g:=s) (fun j hj => mem_image_of_mem s hj) a)
    rw [geom]
    have nonempty : (representatives s).Nonempty :=
      ⟨s (Classical.choice ‹Nonempty M›), mem_image_of_mem _ (mem_univ _)⟩
    apply mul_le_mul_of_nonneg_left _ (prod_nonneg (fun j _ => mul_nonneg (Real.exp_nonneg _) (hC j)))
    simpa only [pow_one] using pow_le_pow_of_le_one posE small nonempty.card_pos
  exact (sum_le_sum (fun s _ => price s)).trans_eq (by simp [nsmul_eq_mul,mul_assoc,e,a])

end YM.Integration.FVA1Physical.Marked

namespace YM.Qlocal.Actual.Season.Exchequer
open Filter Lattice RG Wilson Pressure Tree Marker Extra.Trajectories RG3.Script.Picnic
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open ConnectedActivityE6 AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song
open Push Push.Uniform Metric Height Roof Input Org Supply Pane Slide Further.PhysicalPeriodLimitF933
open PriceCompiler ThroughLaunch Opera Boulevard Trio Lantern Roost AllOrder Transit Transit.WheelP
open Floe Floe.Step.PlanV Pace Ink Ink.Money Quipu Quipu.Sonnet Tern
open Program Program.Certificate Calendars Moonset Rooms Studio Squall Parabola
open Emissions Integration LocalComparison FVA1Physical.Marked Finset Push.AbsoluteSums
open scoped BigOperators Classical Topology

/-- All vacuum host assignments on the same purchased marked representation,
including the actual divided forced norm. The uniformity of the paid error is
over all relative positions, tests, periods and actual trajectories. -/
theorem purchased_all_host_assignments {G : Gauge} (X : Run G) (gauge : G.Simple) (q : ℕ) :
    ∀ᶠ m in atTop, ∀ {V Ω M : Type} [Fintype V] [DecidableEq V] [Fintype M] [Nonempty M]
      {R : Roots (G := G) X.metals.p.profile X.metals.K X.metals.p.kernel}
      {B : Census V} {ξ : V → ℕ} {b i k qd N z j p : ℕ} {δ : ℝ}
      {path : ℕ → Floe.Layout G} {Γ : ℕ → Pace.Coin}
      {x : (t : ℕ) → RG.Rep G (X.alloy.B.a.S.side t p)}
      {o : (t : ℕ) → V → Site (X.family.side t p)} {S : (t : ℕ) → V → Support (X.family.side t p)}
      {T : Ray B} {W : Rooms.Wallet Ω (o m) (x m) B ξ qd b},
      Metre X.alloy X.kit X.T path Γ z N p k x → z ≤ m → m ≤ N →
      Studio.Shell X R ξ b i T o S δ m W (x := x) (j := j) (k := k) →
      ∀ modes : M → Senses B,
      let d := Hull.divisor X.alloy.B.a m
      let pos := fun s => o m (Sonnet.root (modes s))
      let src := fun s => Tale.court (x m).p.B (pos s)
      let g := Coat.gStep (X.T.history N p m).beta
      let ray := Studio.tagScale B X m j T
      let C := fun s => (ray (modes s).val)⁻¹ * valueInvoice G ξ qd b (modes s) g
      let F := fun u s => shortValue W (modes s) (Stores.till (X.alloy.B.a.clock.hatBeta m)) g u
      let β := X.alloy.B.a.clock.hatBeta m
      ∃ bound : (s : M → M) → representatives s → ℕ → ℝ,
        (∀ s k i, 0 ≤ bound s k i) ∧
        (∀ u (π : M → ℕ) U, |∏ k : representatives (hostPattern π),
          ownerBlock (x m) (fibre π (distinctHosts π k)) src F u (distinctHosts π k) U| ≤
          ∏ k, bound (hostPattern π) k (distinctHosts π k)) ∧
        SumBudget (fun π : M → ℕ => d⁻¹ * ∏ k : representatives (hostPattern π),
          (x m).p.mass (enlarged (x m) (fibre π (distinctHosts π k)) src (distinctHosts π k))
            (bound (hostPattern π) k (distinctHosts π k)))
          ((((Fintype.card (M → M):ℝ) * ∏ s, Real.exp (x m).p.supportExponent * C s) * (β^q)⁻¹)/2) := by
  filter_upwards [Graces.Edict.hits_paid gauge X.alloy.B.a q] with m stage
  intro V Ω M _ _ _ _ R B ξ b i k qd N z j p δ path Γ x o S T W track lo hi shell modes d pos src g ray C F β
  have hp := (track.1.walk m lo hi).truep
  have hv := Hull.luminous X.alloy.B.a m
  have paying : Push.Local.hitWidth (x m).p * d ≤ (β^q)⁻¹/2 := by
    rw [hp.point]
    exact stage.1
  have small : Push.Local.hitWidth (x m).p * (d*d) ≤ 1 := by
    have hβ : 1 ≤ β := (X.alloy.B.a.fits.delayed _).le
    have less : (β^q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hβ)
    rw [← mul_assoc]
    apply (mul_le_of_le_one_right (mul_nonneg (zero_le_one.trans (Push.Local.width_one_le _)) hv.1.le) hv.2.1).trans
    exact paying.trans (by linarith)
  have kp : (x m).activities.KBound (x m).p (d*d) := by
    unfold d; rw [← hv.2.2]; exact hp.valid.labels.boundK
  have hc (s) : 0 ≤ C s :=
    mul_nonneg (inv_nonneg.mpr (shell.rental.pos _).le)
      (sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (Vase.ticketC_pos ..))
  have hf (u s U) : |F u s U| ≤ C s := by
    let A := Stanza.son (W.prediction u) b
    have hweight : |W.weight u (modes s)| ≤ (ray (modes s).val)⁻¹ :=
      ((le_inv_mul_iff₀ (shell.rental.pos _)).mpr (shell.starts u _)).trans_eq (mul_one _)
    unfold F shortValue
    rw [abs_mul]
    exact mul_le_mul hweight (wake_bound A _ _ (shell.optics u) (Prior.yard_p ..) g U) (abs_nonneg _)
      (inv_nonneg.mpr (shell.rental.pos _).le)
  obtain ⟨bound,h0,h1,h2⟩ := all_host_assignments (x m) src F C hc hf kp
  refine ⟨bound,h0,h1,budget_loosen (budget_scale (inv_nonneg.mpr hv.1.le) h2) ?_⟩
  let P := (Fintype.card (M → M):ℝ) * ∏ s, Real.exp (x m).p.supportExponent * C s
  have H : 0 ≤ P := mul_nonneg (Nat.cast_nonneg _) (prod_nonneg fun s _ => mul_nonneg (Real.exp_nonneg _) (hc s))
  have hinv : d ≠ 0 := hv.1.ne'
  calc
    _ ≤ d⁻¹ * (P * (Push.Local.hitWidth (x m).p * (d*d))) :=
      mul_le_mul_of_nonneg_left (pattern_price (x m) pos C hc (mul_nonneg hv.1.le hv.1.le) small) (inv_nonneg.mpr hv.1.le)
    _ = P * (Push.Local.hitWidth (x m).p*d) := by field_simp
    _ ≤ P * ((β^q)⁻¹/2) := mul_le_mul_of_nonneg_left paying H
    _ = _ := by ring

end YM.Qlocal.Actual.Season.Exchequer
