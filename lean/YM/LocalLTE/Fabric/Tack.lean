import YM.LocalLTE.Fabric.Jazz
import YM.LocalLTE.Bonnet.Quiet
import YM.LocalLTE.Fabric.Priced
import YM.LocalLTE.Rate.Permit
/-! Curve witness & receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost
open UVNext.CouplingReset Animals
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open YM.LocalLTE.Inset ClockB Urns Trio Slide Marlin
-- NOTE scope. factor uses `T` Launch.
variable {G:Gauge} {X:Metals G} {D:Rolls X.p} {A: Alloy X D} (R: Roost.Factor A){p0:ℕ} -- use eta
variable {R} {ε : ℝ} (H:Funding R p0 ε)
local notation "Wf"=> H.w
variable {N m n k:ℕ} {s:Set ℝ} {a:ℝ} {Q:In A.B.a m n}(F:Career H N m n s a Q)
local notation "T" => A.B.a
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "C₀" => R.target
local notation "J"=> A.B.a.clock.J (m+1)
local notation "I"=> A.B.a.clock.J m
local notation "s₀"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "z" => Trio.base (Trio.resize H.w.ℓ (Rain.lint R.target A m)) (radiusB x₀)
local notation "A₀" => A.B.a.S.side m n
local notation "O" => Chi.canonical
local notation "γ" => A.B.kin.alpha N m
open Coup Scarf East LocalLTE.Fan Pastel
-- Tag for outputs. Function for any Era. Layer J. `ψ` pre-general as low as needed at all stages.
variable {p:ℕ} (W : Trail H p) (hm:m<N)
variable {R₁:Rep G (A.B.a.S.side (m+1) n)}
    (hV: Lives A.B.bake N (m+1) n R₁)(hx:R₁.beta∈ band A.B.a (m+1))
    (U: Guide A.B R.shape N m n R₁) (hU:Opera.Price A.B R.shape N m n R₁ U)
namespace Trail
local notation "L'"=> D.L J
local notation "A'"=> A.B.a
local notation "ξ"=>betaF G x₀ L'
local notation "J'"=> X.p.profile I
local notation "µ"=>Coup.monthly (G:=G) (D.L J) x₀ (3*(W.mass H m))
local notation "κ"=> W.crew H m*radiusB x₀
-- Local permit inputs. Tag budget wiring.Plaw. Use independent F tables.
variable {tag:ℕ→ℕ}
variable (hl : W.Hired H R₁ tag)
set_option quotPrecheck false
-- Exact cost EARLY per Step in projects.Budgets. ADD Pure predictor soon
local notation "S₁"=> (stagnate H.w.ℓ (Rain.lint R.target A m))*radiusB x₀
lemma breadth : (stagnate H.w.ℓ (Rain.lint R.target A m))*radiusB x₀ < κ ∧ 2*z ≤ κ ∧ (32*κ)< (A.B.a.S.side m n).val:= by
    have he:= step_paid (A.B.a) m; have hx:= W.must (J) (I) he
    obtain ⟨hl,hr⟩:= size_wire ((A.B.a.budget m).B_pos) hx
    refine ⟨hl,hr,?_⟩; have hP:= W.pay.shell (J) (I) he; have hN:= W.pay.growth (J) (I) he
    let d:= A.delay.shells J; let z':= W.crew H m; have ht:0<d:= (show 0<32*(1+z') by omega).trans_le hP
    have hk:0<z':=by have _: _:=hx; unfold Coup.wire at hx; unfold z' Trail.crew; omega
    let x₁:= (A.B.a.budget m).B; let y:= (A.B.a.budget (m+1)).B
    apply lt_of_lt_of_le ?_ (A.B.valid.volume m n); change 32*(z'*x₁) < d*(1+x₁+y)^_
    suffices hi: x₁< (1+x₁+y)^A.delay.growth J from by
       rw [←Nat.mul_assoc]; exact lt_of_le_of_lt (Nat.mul_le_mul_right x₁ ((Nat.mul_le_mul_left 32 (show z' ≤1+z' from by omega)).trans hP)) (Nat.mul_lt_mul_of_pos_left hi ht)
    exact lt_of_lt_of_le (b:=1+x₁+y) (by omega) (le_self_pow₀ (by omega) (by omega))

local notation "Ξ"=> Rain.lint R.target A m
include W
lemma budgetGoal : W.hop H m*(betaF G x₀ (D.L J))^(chip 0) ≤ forecastE (A.B.a) m:=by
   have he:= Trail.aware H W (m:=m); have hx:= (Trail.earned H W (m:=m)).rung; have hy:0 < (ξ):= lt_of_lt_of_le hx (le_add_of_nonneg_right (YM.Work.E04.shift_nonneg G _))
   refine le_trans (mul_le_mul_of_nonneg_right he.2 (Real.rpow_nonneg hy.le _)) (mul_le_mul_of_nonneg_left ?_ (Time.credit_pos ..).le); rw [Coup.chip_zero,← Coup.e_now (D.L J) x₀ hy]; change _ ≤ δE x₀
   apply Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_anti₀ (Real.sqrt_pos.mpr hx) (Real.sqrt_le_sqrt (le_add_of_nonneg_right ?_))) (by norm_num); exact YM.Work.E04.shift_nonneg ..
local notation "S'"=> ClockB.lanternPay G (D.L J) (X.p.profile I) H.w.q x₀
local notation "Q'"=> (fronts (m:=m) (A:=A) (C:=R.target) H.w)
local notation "ℒ" => East.lectures U p H.w.ℓ tag
abbrev vested (tag:ℕ→ℕ)(k':ℕ) := East.locker U (East.lectures U p H.w.ℓ tag) k'
local notation "D'"=> Beam.marquee U B
abbrev lobby (f:ℕ→ℕ)(k':ℕ):= Scarf.diamond (Beam.marquee U B) (Trail.vested (p:=p) H U f k') (W.crew H m * radiusB x₀)
local notation "M"=> (lobby H W U tag)
local notation "V$"=> vested (p:=p) H U tag
local notation "e₁"=> Coup.lacquer (G:=G) (D.L J) (X.p.profile I) H.w x₀ (3*W.mass H m)
local notation "t₁"=> Coup.tune (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀
lemma stairV (k':ℕ): Rooms (Beam.marquee U B|>.reg) (vested (p:=p) H U tag k') (κ) (A.B.a.budget m) (W.crew H m):= East.shots U (East.lectures U p H.w.ℓ tag) B (fun _ hi=> hi.1) (Trail.breadth H W (n:=n)|>.1.le) (le_refl _) rfl -- include n through W etc
local notation "t₀"=> (Meadow.timbresN (Meadow.intern U) («χ»:=Chi.canonical) γ H.w.ℓ)
local notation "e"=> Coup.bring (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) (W.crew H m) x₀ (3*W.mass H m)
variable (Y₁:Expose (A:=A) (R:=R.shape) H.w R₁.beta N m) (M₁:Maps (A:=A) (C:=R.target) H.w m N)
local notation "fa"=> Y₁.read H.w k
local notation "A!"=> Meadow.ash U O H.w.ℓ k γ
local notation "g"=> (ornament (c:=A₀) Q' fa)
local notation "Y!"=> (YM.LocalLTE.Patch.failure B Q' z fa U γ H.w.ℓ k)
local notation "F'"=> Coup.freezes (G:=G) (D.L J) (X.p.profile I) H.w (Rain.lint R.target A m) x₀ (3*W.mass H m)
variable (hp: Meadow.Budget (A.B.a.budget m) ((Beam.marquee U (A.B.a.budget m)).reg) (Meadow.ash U Chi.canonical H.w.ℓ k (A.B.kin.alpha N m)) (ClockB.lanternPay G (D.L (A.B.a.clock.J (m+1))) (X.p.profile (A.B.a.clock.J m)) H.w.q (A.B.a.clock.hatBeta m))) (hq:Y₁.Yields H.w k)
include hV hx hm hl hp
set_option maxHeartbeats 400000 in
lemma oldTol : Meadow.Budget B (D'|>.reg) (t₀ k|>.logRead) e₁ := by
    -- assemble directly avoid Kan.
    let G₀:= Height.away (X.p.profile I)
    have hx':= W.estate H hm hV hx U hl
    have hz : 1≤ ξ:= H.vote.cash _ _ (step_paid (A.B.a) m)|>.2 _ (A.B.valid.pays m)|>.light.1
    have hy: turnFee B=G₀:=Rain.jersey (m:=m) (A:=A)|>.2.2.2
    exact East.weather (t:=s₀) U B O µ G₀ _ hy rfl (fun i=> East.bloom ξ (tag i)) (fun i=> East.bloom_bill hz (tag i)) hx' γ H.w.ℓ k hp
omit hl hp
include hq M₁
omit W in
lemma oldGold : Meadow.Budget B (leap (c:=A₀) z) (g) t₁ :=by
   have he:=(R.pledging.agenda _ _ (step_paid A.B.a m)).1; have ht:= Urns.decency R.pledging hm hV hx
   exact Urns.textile H.w hm R.inn H.vote R.pledging.jewels ht he R.pledging.conducts.full Y₁ M₁ R.floor (R.settles _ _) hq -- edit
-- new Lamp funds.
include hU hl hp
variable (k₁:ℕ)
def bindZ (tag:ℕ→ℕ)(k':ℕ):= Marlin.lodge (W.lobby H U tag k') (κ) (κ)
def sense (tag:ℕ→ℕ) (k k₁:ℕ) := Scarf.hesitates B (D') (Trail.vested (p:=p) H U tag k₁) (κ) z (t₀ k) (YM.LocalLTE.Patch.failure B Q' z (Y₁.read H.w k) U γ H.w.ℓ k) ((Trio.ornament (c:=A₀) Q' (Y₁.read H.w k))) -- syntax edit
local notation "He'"=> (Trail.sense H W U Y₁ tag k k₁)
lemma hosts (x:Site A₀) : Trio.Tidy B (neighbors (κ) x) (He' x) ∧ (∀ V,He' x V≠0→ ¬ Healthy (B).threshold (neighbors (κ) x) V)∧∀ V, ‖He' x V‖ ≤ F':=by
   let K:=(R.expense J I).wanting; have he:=(R.pledging.agenda _ _ (step_paid A.B.a m)).1; have ht:= Urns.decency R.pledging hm hV hx
   have hR:= breadth H W (m:=m) (n:=n); refine Scarf.spires B (D') (Trail.vested (p:=p) H U tag k₁) (κ) z (κ) («T»:= (t₀ k)) g Y! ?_ (W.oldTol H hm hV hx U hl hp) (Trail.oldGold H hm hV hx Y₁ M₁ hq) (stairV H W U _) (by omega) le_rfl x -- edit
   intro i; have h:= Urns.hauls H.w hm R.inn H.vote R.pledging.jewels ht he R.pledging.conducts.full R.pledging.conducts.income U hU hV hx Y₁ k i
   obtain ⟨hX,hy,hz⟩:=h; have ht: neighbors (2*z) i ⊆ neighbors (κ) i:= fun j hj=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hj).trans hR.2.1)
   rw [W.ambition] at hz; exact ⟨⟨Work.H03.reads_larger ht hX.uses,hX.borel,hX.invariant⟩,fun V hp he=> hy _ hp (healthy_mono ht he),hz⟩
end Trail
end YM.PhysicalNext.Repeat.Mallow
