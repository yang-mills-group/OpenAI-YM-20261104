import YM.Integration.FVA1Physical.Round2.FieldBirthTariff
import YM.Integration.FVA1Physical.Round2.PhysicalChartDomain
import YM.Integration.FVA1Physical.Round2.FieldWidthTariff
import YM.Integration.FVA1Physical.Round2.FieldChartIndices
import YM.Integration.FVA1Physical.Marked.ChartSpatial

/-! Pay the full spatial sum of ordinary derivatives of the true normalized
current physical insertion, with an independent point at every word.
This bound is independent of lattice volume. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Source Labels Extra.Histories Precision
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato ThroughLaunch Roof Push.PriceCompiler
open Next.Foundations UVNext.CouplingReset Graces Roost
open Push.Local Push.AbsoluteSums LocalLTE Further.LogJets Push.Uniform
open Integration.FVA1Physical.Marked RGComparison.Core16.Spool MSbar MSbar.Lis MSbar.Midpoint MSbar.Rolling MSbar.Whisk
open MSbar.Heath.Stock MSbar.Mosaic
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] {d N n j : ℕ}

def fieldShelf (a : I → CoverLabel G d) (H : Stage) (radius : ℕ) : ℝ :=
  Real.exp (H.supportExponent + 2) * (lampFare H (Fintype.card I) radius + 3 * stencilBound (freshLamps a))

theorem current_charge_on (R : PhysicalNext.Repeat.Legato.Run G) (hG : G.Simple)
    (hj : j < N) (start : R.t 0 ≤ j) (a : I → CoverLabel G d)
    (ready : ∀ i, R.t (a i).1.val ≤ j + 1) (b : Site (R.family.side j n))
    (o : I → Site (R.family.side (j+1) n)) (part : Bool) (radius q s : ℕ) (positive : 0 < q)
    (Z : List (Primary (R.family.side j n) G) → Positions (Primary (R.family.side j n) G)) :
    let H := R.family.path
    let S := H.levels.clock.op j n
    let A := H.rep N n (j+1)
    let B := (H.rep N n j).p
    let h := H.levels.params (j+1)
    let x := H.levels.clock.hatBeta j
    let g := cue A.beta
    let f := fun z => Bulk.expect S A (postcard G (R.family.side j n) g z) (fun U => look part (tally (freshLamps a) o U))
    (∀ i, separation (o i-S.ratio.embed b) 0 ≤ radius) →
    radius + LocalLTE.Vault.terr G d ≤ A.p.B →
    (∀ l, ‖g • Z l‖ < 1 ∧ palace (g • Z l) ∈ Boulevard.sunny B) →
    q ≤ B.order →
    0 < αm x →
    (((s:ℝ)+1)*αm x+2*αm x)*q*(6*B.B+2:ℝ) ≤ B.supportExponent →
    fieldCharge (Measuring.chart (R.family.side j n) G) b (αm x) s q Z f ≤
      wordSupportFare G q s x * ((2:ℝ)^q * chartFactor G q * fieldShelf a h radius) := by
  intro H S A B h x g f foot fit domain order pos room
  let y := S.ratio.embed b
  let v := fun i => o i - y
  let δ := H.levels.clock.forcedAllowance (j+1)
  let u := localFieldTariff A.p a h.columns radius
  let φ := fun U => look part (tally (freshLamps a) v U)
  let price := birthCost A.p (lampSupport a v) δ (u+‖(φ 1:ℂ)‖) (2*stencilBound (freshLamps a))
  have hp := R.makes.wilson.represents N n (j+1) hj
  have hd : 3 ≤ R.alloy.B.a.clock.J (j+1) := (R.makes.stages 0).1.trans
    (R.alloy.B.a.fits.mono (start.trans (Nat.le_succ _)))
  have scale : A.p = R.alloy.B.a.budget (j+1) := hp.vac
  have permit : hitWidth A.p * Real.sqrt δ ≤ 1 := by
    rw [scale,Blush.glyph_eq]
    exact R.b.stamp _ _ (step_paid R.alloy.B.a (j+1)) 0 ((Nat.zero_le 3).trans hd) _
      (R.alloy.B.valid.pays (j+1)) |>.2 _ _ (params_eq R.alloy.B.valid (j+1)) rfl
  have paid : price ≤ fieldShelf a h radius := single_ball_fare h A.p a
    (by rw [scale];rfl) (by rw [scale];rfl) (by rw [scale];rfl) radius v foot fit part (forcedPos R.alloy.B.a (j+1)) permit
  have rate1 : Doors.rate (H.S.block j) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (H.S.block j).property) (by norm_num)
  have shelf0 : 0 ≤ fieldShelf a h radius := by
    unfold fieldShelf lampFare
    have col : 0 ≤ h.columns := zero_le_one.trans h.columns_ge
    have st := (stencilBound_pos (freshLamps a)).le
    positivity
  have price' : Doors.rate (H.S.block j)*price ≤ fieldShelf a h radius :=
    (mul_le_mul_of_nonneg_left paid (Doors.rate_pos _).le).trans (mul_le_of_le_one_left shelf0 rate1)
  have actual := current_run_chart_sup R hG hj start a ready y o part radius foot q s positive pos pos.le
    (fun l => Z (l.map (bondKeys G (R.family.side j n)))) (fun l _ => (domain _).1)
    (fun l _ => (domain _).2) order room
  dsimp only at actual
  rw [show S.ratio.parent y = b from S.ratio.embed_parent b] at actual
  rw [charge_in_bonds]
  apply actual.trans
  have fare := paid_actual_chart hG R (n:=n) hj q
  have hfare : 0 ≤ |g|^q * earnE B G q := mul_nonneg (pow_nonneg (abs_nonneg _) _) (floorP G _ _)
  have support0 : 0 ≤ wordSupportFare G q s x := by
    unfold wordSupportFare
    have cc := (count_pos pos).le
    positivity
  change wordSupportFare G q s x * (|g|^q * (earnE B G q * (Doors.rate (H.S.block j)*price))) ≤ _
  rw [←mul_assoc (|g|^q)]
  exact mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left price' hfare).trans
    (mul_le_mul_of_nonneg_right fare shelf0)) support0

end YM.Integration.FVA1Physical.Round2.Curvature
