import YM.RGComparison01.AuxCover
/-!
# Closing auxiliary comparisons
 Keep same unit before treating vacuum and marked polynomials. Explicit scalar retained;
 it's normalized by solar which should not be compared here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxBeam
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open PhysicalNext.Repeat Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open Push.AbsoluteSums Fare Sienna AuxDesk Token AuxFabric AuxConstant AuxMiles AuxWeigh AuxPackage
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MatrixOrder
variable {G : Gauge} (A:ChartRatio G) {P : Teller G} {C Λ b d D v u u' a σ μ : ℝ} {n j k q' q : ℕ}
section layout
variable {c f:Side} {S:StepData c f} (T:Tube G S) (F:Forest S.ratio) (ρ:Bid.Dir G c→AxisChart G F)
  (i:S.Choices) (B:BudgetPoint) (β:ℝ) (e J:Config G f→ℝ)
local notation "W" => shot A F T ρ i
local notation "U₀" => Lapis.table F i T.up T.high
local notation "g" => gStep β
local notation "M₀" => Lapis.gram F T.up T.high ρ i
local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)

def weighLess : Xs→ℝ:= weighed T B β (gross e 1)
def read_J : Xs→ℝ:= weighed T B β (gross e J) / weighLess T B β e
def uniquePart : ℝ := Real.log (solar F A β) - Lantern.shade M₀ 0
def givenLog (x:Xs):= Real.log (weighLess T B β e x)- uniquePart A T F ρ i β
variable (E U : Poll.Body (Precision.Key F G) → ℝ × Positions (Uniform.Primary c G) → ℝ)
local notation "K" => rescale F T A ρ B i β (gross e 1)
abbrev noneCo (q n:ℕ) := AuxPackage.bill A T F ρ i E 1 q 0 n
def logVia (q n:ℕ) := AuxStage.pacify Real.log (noneCo A T F ρ i E q n) 1 n + (-1:ℝ) • AuxCover.collector A T F i ρ
def markCo (q q' n:ℕ):=AuxStage.Points.weave (AuxPackage.bill A T F ρ i E U q q' n) (AuxStage.pacify (fun x:ℝ=> x⁻¹) (noneCo A T F ρ i E q n) 1 n)
-- assembly cost common upper volume independent
variable {x:Positions (Uniform.Primary c G)} (hh:LocalRatio A) (he:0<β)
    (p : AuxStage.Points v d (gStep β) n j (rescale F T A ρ B i β (gross e 1)) x (noneCo A T F ρ i E q n))
    (hp : AuxStage.Points u d (gStep β) n j (rescale F T A ρ B i β (gross e J)) x (AuxPackage.bill A T F ρ i E U q q' n))
local notation "V" => noneCo A T F ρ i E q n
include p hh he
lemma bound_at (hb : g ≤ 1) (hz : V 0=fun _=>1) (hA : AuxStage.inter v 2 n*g ≤ 1/2) :
    (K x)∈Icc (1/2:ℝ) (3/2) ∧ 0 < weighLess T B β e x:= by
  let k:= assay F T A ρ i β x; have hk : 0<k:= mul_pos (sun _ _ _ he hh) (Real.exp_pos _)
  have hg:= Fare.gS β he|>.1
  have ht:= p.off_one (p:=1) hz hg.le hb |>.bound
  have hB:v+AuxStage.Points.allowance v n ≤ AuxStage.inter v 2 n := le_add_of_nonneg_right (by norm_num)
  have hU:= abs_le.mp (show |K x-1|≤1/2 from ht.trans ((mul_le_mul_of_nonneg_right hB hg.le).trans hA))
  have hV: 1/2 ≤ K x:= by linarith only [hU.1]
  refine ⟨⟨hV,by linarith only [hU.2]⟩,?_⟩
  have hz0:= (le_div_iff₀ hk).mp (show 1/2 ≤ weighLess T B β e x / k from hV)
  exact lt_of_lt_of_le (by positivity) hz0
local notation "I₀" => closedBall (0:ℝ) (1/2)
variable (hb : gStep β≤1) (hz : noneCo A T F ρ i E q n 0=fun _=>1) (hA : AuxStage.inter v 2 n*gStep β ≤ 1/2)
include hb hz hA
lemma log_P (H : ∀ y∈I₀, Brush (n+j+1) C 1 (fun t:ℝ=>Real.log (t+1)) y)
   (hB : AuxStage.Points u d (gStep β) n j (AuxCover.off A T F i ρ β) x (AuxCover.collector A T F i ρ)) :
    AuxStage.Points (AuxStage.label Real.log C v 1 n j+u) d g n j (givenLog A T F ρ i B β e) x (logVia A T F ρ i E q n):= by
  let v:= solar F A β; let k(x:Xs):=assay F T A ρ i β x; let P₀:= weighLess T B β e
  have h:=AuxStage.attend Real.log 1 p (gS β he).1 hb hz (hA.trans (by norm_num)) (fun y hy=> H y (closedBall_subset_closedBall hA (ball_subset_closedBall hy))) (by omega) (by omega)
  have hw:= h.add (hB.scale (-1)); rw [norm_neg,norm_one,one_mul] at hw
  have hs:= bound_at A T F ρ i B β e E hh he p hb hz hA; have hz:= (show AuxStage.Points _ _ _ _ _ K _ _ from p).full (gS β he).1.le hb |>.smooth
  have hV : 0 < v := Fare.sun _ _ _ he hh
  refine hw.adjust ?_; filter_upwards [hz.continuousAt.eventually (lt_mem_nhds (show 0 < K x from (by linarith only [hs.1.1])))] with y hy
  have hp : 0 < k y:= mul_pos hV (Real.exp_pos _)
  have hY :0 < P₀ y:= by
    have H := (lt_div_iff₀ hp).mp (show 0 < P₀ y / k y from hy); rwa [zero_mul] at H
  change Real.log (P₀ y) - uniquePart _ _ _ _ _ _= Real.log (P₀ y / k y)+(-1)*AuxCover.off A T F i ρ β y
  rw [Real.log_div hY.ne' hp.ne']; unfold k uniquePart AuxCover.off assay; unfold v at hV; rw [Real.log_mul hV.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
include hp
lemma mark_P (H : ∀ y∈I₀, Brush (n+j+1) C 1 (fun t:ℝ=> (t+1)⁻¹) y) :
    AuxStage.Points (AuxStage.Points.fuse n j u (AuxStage.label (fun x:ℝ=> x⁻¹) C v 1 n j)) d g n j (read_J T B β e J) x (markCo A T F ρ i E U q q' n):= by
  let k(x:Xs):=assay F T A ρ i β x; let P₀:=weighLess T B β e
  have h:= AuxStage.attend (fun x:ℝ=>x⁻¹) 1 p (gS β he).1 hb hz (hA.trans (by norm_num)) (fun y hy=> H y (closedBall_subset_closedBall hA (ball_subset_closedBall hy))) (by omega) (by omega)
  apply (hp.multiply h (gS β he).1.le hb).adjust; refine Eventually.of_forall fun y=>?_
  have hk:0<k y:=mul_pos (Fare.sun _ _ _ he hh) (Real.exp_pos _)
  change weighed T B β _ _/P₀ y= weighed T B β _ _/k y * (P₀ y/k y)⁻¹; rw [←div_eq_mul_inv, div_div_div_cancel_right₀ hk.ne']
end layout

variable {L:Side} {f u : ℝ→ℝ}
lemma side_cost (h : Geo G L f) (hp : Geo G L u) (k n : ℕ) : Geo G L (fun t=> AuxCover.sideFee k n (f t) (u t)):= by
  have he: Geo G L (fun t=> AuxCover.readAt n (f t)):= Geo.rot _ (((Geo.fixed 1|>.joins h)).joins (Geo.fixed 1|>.joins h)) h
  unfold AuxCover.sideFee; refine Geo.joins (office h hp (q:=2) (k:=k) he) (office h hp (k:=k) (q:=0) (he.joins h))
where
  office (h: Geo G L f) (hp : Geo G L u) {k q:ℕ} {g:ℝ→ℝ} (hg:Geo G L g) : Geo G L (fun t=> ritual_fee q k (g t) 0 (u t)):= by
    let p:=q+k+1; have hf:= hp.power p
    exact (((Geo.fixed _).times (hg.joins (Geo.fixed _))).times hf).joins ((hg.times hf).joins (Geo.fixed _))
end YM.RGComparison01.AuxBeam
