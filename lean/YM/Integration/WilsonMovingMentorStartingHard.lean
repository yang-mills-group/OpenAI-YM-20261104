import YM.QuadraticLocal.Startup.Headway
import YM.QuadraticLocal.Advent

/-! The original Pavilion interior argument on the actual chosen physical
Concourse. Keep its exact incoming Second and its true upper forced rent. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorStartingHard
open QuadraticLocal QuadraticLocal.Advent
open Function Filter Finset Lattice Wilson RG RG.Supply Pressure Input Org Precision Next.Scheduling
open Next.Scheduling.Clock AnalyticBridge VerifiedReset ConnectedActivityE6 PhysicalNext Repeat
open Progress.DirectedRecipe Payments Push AbsoluteSums PriceCompiler
open AllOrder AllOrder.Transit WheelP AllOrder.Floe AllOrder.Floe.Step PlanV Pane ThroughLaunch
open Roost Legato Graces
open Extra.Iteration
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius Asymptotics
open Extra.Histories
variable {G: Gauge} (R:Run G) (g : G.Simple)
local notation "S"=> R.alloy.B.a
local notation "Ta"=> R.T
local notation "Sz"=> R.metals.p
local notation "A"=> R.alloy
local notation "F"=> R.kit
local notation "Z"=> R.family
local notation "c"=> R.family.side
variable {m n i b q k N:ℕ} (h:WayStation R.kit) (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
set_option quotPrecheck false
local notation "ρ"=> Burn.horizon k
local notation "Φ"=> R.alloy.B.a.clock.hatBeta
local notation "τ"=> R.alloy.B.a.clock.op i n
local notation "Y"=> R.alloy.B.a.clock.J (i+1)
local notation "I"=> R.alloy.B.a.clock.J i
local notation "L"=> R.rolls.L Y
local notation "X"=> R.alloy.B.a.budget i
local notation "W"=> R.alloy.B.a.budget (i+1)
local notation "xd"=> Φ i
local notation "γ"=> Φ (i+1)
local notation "Vd"=> (Φ i)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)(Ψ:(i:ℕ)→RG.Rep G (R.family.side i n))
variable (v:Concourse R.alloy R.kit R.T π Γ m N n k Ψ)
variable (K₀:TicketP R.alloy R.kit D Q)
variable (l:m≤ i)
local notation "P"=> Ψ (i+1)
local notation "P'"=> Ψ i
local notation "H"=> Opera.Guide R.alloy.B (R.kit.shape)
local notation "wa"=> Time.forecastK S i (R.kit).scout (P).beta
local notation "wp"=> Time.quoteHard S i (R.kit).book (P).beta
local notation "y₀"=> Willow.haloSlack (X).B
local notation "Γ'"=> R.T.history N n
open Integration.LocalComparison
local notation "κ'"=> forcedDivisor Z i
open Travel
open QuadraticLocal.Hard QuadraticLocal.Spes QuadraticLocal.Kiosk Marker Spes.Market ComparisonDensity.Address
private lemma dummy {K: Marker.Census PUnit.{1}} (x:K.Mode): x.val.card≤1:= by simpa using Finset.card_le_univ x.val
private def Kes : Marker.Census PUnit.{1} := ⟨Finset.univ,Finset.mem_univ _,fun _=>Finset.mem_univ _,fun _ _ _=>Finset.mem_univ _⟩
private def empty {n:Side}{V:Type}[DecidableEq V]{T: Marker.Census V}{o:V→Site n}{p:BudgetPoint}: Lamps Unit Empty G p o T:= ⟨(fun i=> Empty.elim i),(fun i=> Empty.elim i),(fun i=> Empty.elim i),(fun i=> Empty.elim i),fun _=> (fun i=> Empty.elim i),fun _=> (fun i=> Empty.elim i),(fun i=> Empty.elim i),fun _=>  (fun i=> Empty.elim i)⟩ -- V T bind
local notation "τφ"=> R.family.path.levels.clock.op i n
local notation "hΞ"=> (P').p.supportExponent
local notation "β!"=> (P).beta
include h v l K₀
theorem interior (r:i < N) : Topline P' (Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta):=by
   obtain ⟨U,hU,⟨WC⟩⟩:= (v.2 i l r).earns; have hm' :(1:ℕ)≤ I:= by have hm:= (S).clock.adm i; omega
   obtain ⟨Wq,y,bω,hT⟩:= h.frost.license _ _ (step_paid S i) 1 I hm' le_rfl hm'; let P₁:=hT (Φ i) (R.alloy.B.valid.pays i); obtain ⟨E,he⟩:= invited R h D Q π Γ Ψ v K₀ l r I U P₁
   have hp:=(later R π Γ Ψ v (Nat.le_succ_of_le l) r).truep; have h':= hp.valid.labels;
   let v0:PUnit.{1}→ Site (c (i+1) n):=fun _=>0
   let X':= rentValid h'.forced h'.boundK; let Λ:Gallery Unit Empty v0 P Kes:= ⟨empty,Hard.rent X'⟩
   have hb₀ := (Hard.leasing (w:=1) (α:=Unit) («R»:=Kes) (o:=v0) X'); have hγ : (A).B.a.clock.forcedAllowance (i+1) ≤ 1:=by unfold RG.Calendar.forcedAllowance RG.Calendar.monitor; exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
   have hp' : Λ.Pays 1 (P).p.supportExponent 1 1:= ⟨⟨Empty.elim,(fun e=> e.elim),(fun e=> e.elim),fun x=> budget_finite (fun e=>e.elim) (by rw [Finset.univ_eq_empty,Finset.sum_empty]; exact zero_le_one)⟩,Hard.mono _ hb₀ hγ⟩
   obtain ⟨w'⟩:= Travel.sealed Λ 1 hp'; have hx:= spare R π Γ Ψ v (Nat.le_succ_of_le l) r
   have hn(i:PUnit.{1}):0<(1:PUnit.{1}→ℝ) i:=zero_lt_one
   have ht:= (Travel.docket U WC E Λ 1 w' hn hx dummy (by norm_num) () (Classical.choice (Tree.select (τφ).ratio ((τφ).patch.odd_side)))).2.1
   have hL:= Hard.transfer _ _ () ht hn; unfold Topline; rw [show (Ψ i).p.B=(X).B from congr_arg BudgetPoint.B (later R π Γ Ψ v l r.le).truep.point]; exact ⟨WC.intermediate,_,⟨WC.second⟩, hL⟩

theorem original (r:i<N) (q:ℕ) (hq:q≤R.alloy.B.a.clock.J i) :
    Topline (Ψ i) (Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta) ∧
    Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta ≤
      (R.alloy.B.a.clock.hatBeta (i+1))^(-(q:ℝ)) * forcedDivisor R.family i :=
  ⟨interior R h D Q π Γ Ψ v K₀ l r, force_bill R h π Γ Ψ v l r hq⟩


omit h v l K₀ in
private theorem after_raise {x y δ f:ℝ} (hx:1≤x) (hxy:x≤y) (hδ:0≤δ)
    (a e h:ℕ) (bill:f≤y^(-((a+e*h:ℕ):ℝ))*δ) :
    (x^e)^h*f≤y^(-(a:ℝ))*δ := by
  have px:=zero_le_one.trans hx
  have py:0<y:=(zero_lt_one.trans_le hx).trans_le hxy
  calc
    (x^e)^h*f ≤ (x^e)^h*(y^(-((a+e*h:ℕ):ℝ))*δ) :=
      mul_le_mul_of_nonneg_left bill (pow_nonneg (pow_nonneg px _) _)
    _ ≤ (y^e)^h*(y^(-((a+e*h:ℕ):ℝ))*δ) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg px _) (pow_le_pow_left₀ px hxy _) _)
        (mul_nonneg (Real.rpow_nonneg py.le _) hδ)
    _ = y^(-(a:ℝ))*δ := by
      rw [Real.rpow_neg py.le,Real.rpow_neg py.le,Real.rpow_natCast,Real.rpow_natCast,pow_add,pow_mul]
      field_simp

theorem refunded (r:i<N) (q ell load:ℕ) (attained:q+ell*load≤R.alloy.B.a.clock.J i) :
    Topline (Ψ i) (Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta) ∧
      ((R.alloy.B.a.clock.hatBeta i)^ell)^load * Time.quoteHard R.alloy.B.a i R.kit.book (Ψ (i+1)).beta ≤
      (R.alloy.B.a.clock.hatBeta (i+1))^(-(q:ℝ))*forcedDivisor R.family i := by
  refine ⟨interior R h D Q π Γ Ψ v K₀ l r,?_⟩
  apply after_raise ((S).fits.delayed i).le _ (Real.sqrt_nonneg _) q ell load
    (force_bill R h π Γ Ψ v l r attained)
  rw [PriceCompiler.beta_eq R.alloy.B.valid i]
  exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)


omit v l K₀ in
theorem terminal (q ell load:ℕ) (attained:q+ell*load≤R.alloy.B.a.clock.J N)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N)) :
    Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N) ∧
    ((Φ N)^ell)^load*(R.family.path.levels.clock.forcedAllowance N)≤
      (Φ N)^(-(q:ℝ))*forcedDivisor R.family N := by
  refine ⟨top,after_raise ((S).fits.delayed N).le le_rfl (Real.sqrt_nonneg _) q ell load ?_⟩
  change _ ≤ (Φ N)^(-((q+ell*load:ℕ):ℝ))*Blush.glyph (Φ N)
  rw [mul_comm _ (Blush.glyph _),
    (AllOrder.Quay.e_all (a:=R.family.path.levels) (n:=N) rfl (zero_lt_one.trans ((S).fits.delayed N))).2]
  exact ((h.passport _ _ (step_paid S N) _ (R.alloy.B.valid.pays N)).portions
    0 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) 0 (by omega) (q+ell*load) attained).enough

theorem throughout (q ell load:ℕ) (reached:i≤N) (attained:q+ell*load≤R.alloy.B.a.clock.J i)
    (top:Topline (Ψ N) (R.family.path.levels.clock.forcedAllowance N)) :
    ∃ f, Topline (Ψ i) f ∧ ((Φ i)^ell)^load*f≤(Φ i)^(-(q:ℝ))*forcedDivisor R.family i := by
  rcases eq_or_lt_of_le reached with eq|interiorDate
  · subst i
    exact ⟨_,terminal R h Ψ q ell load attained top⟩
  · obtain ⟨installed,estimate⟩:=refunded R h D Q π Γ Ψ v K₀ l interiorDate q ell load attained
    have xy:Φ i≤Φ (i+1):=by rw [PriceCompiler.beta_eq R.alloy.B.valid i]; exact le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
    refine ⟨_,installed,estimate.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))⟩
    exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans ((S).fits.delayed i)) xy (neg_nonpos.mpr (Nat.cast_nonneg _))

end YM.Integration.WilsonMovingMentorStartingHard
