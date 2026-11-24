import YM.LocalLTE.Pool.Frame
/-! # Boundary surface payments on same theory. Extra regular stencil tags; hail projection and rotate. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonStartup.Frost
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open AnalyticBridge VerifiedReset Collection Price
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf Urns
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
open Start Animals
open Padded Ovens Pipes
variable {x t :ℝ} (M:ℕ) {κ k:ℝ} (p: BudgetPoint)(c:Clip)
local notation "W" => (bank n G M)
local notation "P" => iceCap (n:=n) G M p c x κ
variable (hs : Reliable G κ k) (hG:G.Simple)(hn:20<n.val) (hb:Decent c p)
-- Use βhat = t. Set χ models rates unit. 
variable (η:ℝ) (L:Side)
variable (ht : 1 ≤ t) (hx: ‖x‖≤2*t) (hd:c.direct≤1)(hG:G.Simple)(hn:20<n.val)(hP: p.threshold ≤ Start.threshold G p.order p.power) (ha:4 ≤ p.B)
-- rates extra. choose Λ_j. pay Price tψ small.History. Psi before Tor.
variable (he:η>0) (hh: 2*t*Start.item G p≤ η*t^(chip 0))(hv:∀ j:ℕ, j≤M → 2*t*(turnFee p*(betaF G t L)^(Urns.dust j-1))≤ η*t^(chip (j+1)))
variable (hW:∀ j:ℕ,j≤M→∀ (o:PlaqAxes), p.supBounds (0:Site n) (neighbors 4 0) (residual G (0,o)-glaze G o κ j) ((betaF G t L)^(Urns.dust j-1)))
local notation "P₀"=> Start.weight c x
include hx hd hP hW hG hs hn hh he ht hv
lemma brilliance (i:Card M n) : p.supBounds i.2.native (neighbors 4 i.2.native) (Frost.part G M c x κ i) (2*(η*t^(chip i.1.val))) :=by
    let j':=i.1.val; let o:=i.2; let R' : Pot G n:= P₀ • o.accrual; let F j:= P₀ • Frost.draft G o κ j
    have h : ‖P₀‖ ≤ 2*t:= (Start.weight_le _ hd).trans hx
    let Y:= neighbors 4 o.native; have hl:p.Regular Y o.accrual (G:=G):= VerifiedReset.reg_larger (Start.accrual_regular ..) ((shore'₀ o).trans (shore_l _)); have hQ:p.Regular Y R':= Start.times_reg _ hl
    have hp j:p.Regular Y (F j):= Start.times_reg _ (Frost.plot p hs hG hn _ o).1
    have hη : p.supBounds o.native Y R' (η*t^(chip 0)):= VerifiedReset.sup_le (Start.times_bound _ (VerifiedReset.sup_larger (accrual_fit o hP) ((shore'₀ o).trans (shore_l _)))) ((mul_le_mul_of_nonneg_right h (item_pos ..).le).trans hh)
    let g j:=η*t^(chip j); have h₀ j:0≤ g j:=mul_nonneg he.le (Real.rpow_nonneg (zero_le_one.trans ht) _)
    have hy (i:ℕ) (hi:i≤ M):p.supBounds o.native Y (R'-F i) (g (i+1)):=by
       let q:= glaze G (n:=n) o.2.2 κ i
       have hp:= Frost.mist G hs i (i:=o) (hW i hi _); unfold R' F; rw [← smul_sub]; exact VerifiedReset.sup_le (Start.times_bound _ hp) ((mul_le_mul_of_nonneg_right h hp.1).trans (hv i hi))
    have hP {s t:ℕ}(hx:s≤t):g t≤g s:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (by unfold Pastel.chip; gcongr)) he.le -- inspect chip
    unfold Frost.part rota; split
    next hz=>
       rw [hz, smul_sub]; exact VerifiedReset.sup_le (hy M le_rfl) (le_mul_of_one_le_left (h₀ _) one_le_two)
    split
    next hz =>
       rw [hz]; change p.supBounds _ _ (F 0) (2*g 0); rw [show F 0=R'-(R'-F 0) from by abel]; apply VerifiedReset.sup_le (VerifiedReset.sup_sub hQ (VerifiedReset.reg_sub hQ (hp 0)) hη (hy 0 (by omega))) ((add_le_add le_rfl (hP (Nat.le_succ _))).trans (Eq.le (two_mul _).symm))
    next hh hz=>
       rw [smul_sub]; let k:= j'-1; have ht:j'≤M:=by omega
       change p.supBounds _ _ (F j'-F k) (2*g j'); rw [show F j'-F k=R'-F k -(R'-F j') from by abel]
       have hv':k+1=j':=by unfold k j'; omega
       apply VerifiedReset.sup_le (VerifiedReset.sup_sub (VerifiedReset.reg_sub hQ (hp k)) (VerifiedReset.reg_sub hQ (hp j')) (hy k (by omega)) (hy j' ht))
       rw [two_mul,hv']; exact add_le_add le_rfl (hP (Nat.le_succ _))
-- budget mass on Padded. 
include ha
open Extra.Iteration Quotes
open East Padded
abbrev age (n: Side)(M:ℕ)(i:ℕ): ℕ := (Padded.name (Frost.Card M n) i).1.val
def kettleP (p: BudgetPoint)(M:ℕ)(η:ℝ):= ((M+2:ℕ):ℝ)*((Fintype.card Signed:ℝ)*(Fintype.card PlaqAxes:ℝ))*(kiosk p.supportExponent 1*(2*η))
local notation "V"=> kettleP p M η
set_option quotPrecheck false
local notation "P'"=> ((bank n G M).reg)
lemma bankCoins : ∃ f:ℕ→ℝ, (∀ i,p.supBounds (P' i|>.site) (P' i|>.support) ((P).regular i) (f i)) ∧ anchored p P' (fun i=>f i*East.bloom t (age n M i)) ((kettleP p M η)*t^(chip 0)):=by
    let k:=name (Card M n); let g j:=2*(η*t^(chip j)); let f i:= if fixed (Card M n) i then g (k i|>.1.val) else 0
    let a:=t^(chip 0); let X i:=(P' i).support; refine ⟨f,fun i=>?_,fun i=>?_⟩
    · unfold f; rw [reggo]; split; exact brilliance G M p c hs hG hn η L ht hx hd hP he hh hv hW (k i) -- edit
      exact Start.zero_bound
    let h (j:ℕ) := g j * East.bloom t j; let F (j:Card M n):= if j.2.native=i then p.mass (neighbors 4 j.2.native) (h j.1.val) else 0
    have hy j:F j≥0:=by
      unfold F; split
      next=> exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (mul_nonneg zero_le_two (mul_nonneg he.le (Real.rpow_nonneg (zero_le_one.trans ht) _))) (East.bloom_nn (zero_le_one.trans ht) _))
      next=>exact le_rfl
    refine Padded.budget (g:=F) (fun j=> ?_) hy ?_
    · dsimp only; unfold f; by_cases hH:fixed (Card M n) j
      · rw [if_pos hH,if_pos hH]; rfl
      rw [if_neg hH,zero_mul,if_neg hH]; simp [BudgetPoint.mass]
    -- count exactly, all Keys. 
    have hz j:h j=2*η*a:=by unfold h g; rw [←mul_assoc, mul_assoc, mul_comm (t^(chip j)), East.bloom_price _ _ (zero_lt_one.trans_le ht), ← Coup.chip_zero]
    let T:=p.mass (neighbors 4 i) (2*η*a)
    have hF (j:Card M n): F j=(if j.2.native=i then T else 0)  := by
       unfold F; rw [hz]; split; next he=> rw [he]
       next=>rfl
    simp_rw [hF]; rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _ : Key n=> _),Fintype.sum_prod_type (fun _ : WilsonStartup.Cell n=> _)]; simp [Key.native]
    have hz:T≤ kiosk p.supportExponent 1* (2*η*a):=by
         apply mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ p.exponent_pos.le)) (mul_nonneg (mul_nonneg zero_le_two he.le) (Real.rpow_nonneg (zero_le_one.trans ht) _)); exact_mod_cast Scarf.standing 4 p 1 i (by omega)
    change (∑ _ : Fin (M+2), ∑ _ : Signed, ∑ y:Site n, ∑ _ : PlaqAxes, (if y=i then T else 0)) ≤_
    have hp : ∑ y:Site n, ∑ _ : PlaqAxes, (if y=i then T else 0)= (Fintype.card PlaqAxes:ℝ)*T:= by rw [Finset.sum_comm]; simp
    simp_rw [hp]
    simp
    unfold kettleP; push_cast; nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg (Fintype.card PlaqAxes))) (Nat.cast_nonneg (Fintype.card Signed))) (show 0≤(M:ℝ)+2 by positivity)]
end YM.WilsonStartup.Frost
