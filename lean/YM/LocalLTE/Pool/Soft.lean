import YM.LocalLTE.Pool.Kiosk
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
omit hx hd hP hW hG hs hn hh he ht hv
lemma suture (i:Key n)(h:p.threshold ≤ Start.threshold G p.order p.power)(U:Config G n): ‖maskH G p i U‖ ≤ 2*Start.item G p:=by
    have ht:= Start.accrual_fit (i) h; exact (norm_sub_le ..).trans ((add_le_add (CouplingShape.mask_cost (VerifiedReset.sup_larger ht ((shore'₀ i).trans (shore_l _))) _) (CouplingShape.mask_cost ht _)).trans_eq (two_mul _).symm)
lemma s_sut (i:Key n)(h:p.threshold ≤ Start.threshold G p.order p.power)(U:Config G n)(hd:c.direct≤ 1)(hv: ‖x‖ ≤2*t) (hT: 2*t*Start.item G p≤ η*t^(chip 0)) : ‖Start.weight c x * maskH G p i U‖ ≤ 2*(η*t^(chip 0)):=by
    rw [norm_mul]; apply le_trans (mul_le_mul ((Start.weight_le x hd).trans hv) (suture G p i h U) (norm_nonneg _) ((norm_nonneg _).trans hv)); linarith
-- HIT per support near site.pay before Bar.Surf
abbrev ηT (p:BudgetPoint) := p.supportExponent
abbrev chum (p: BudgetPoint) := (ballCost 4 :ℝ)*((Fintype.card Signed:ℝ)*(Fintype.card PlaqAxes:ℝ))*kiosk (p.supportExponent+1) 1
abbrev soft (p:BudgetPoint)(η t:ℝ) := chum p*(2*(η*t^(chip 0)))
include hP ha hx hd hh he ht
open Extra.Iteration Quotes
open Payments
lemma haunt : ∃ q:ℕ→ℝ,softCost p W q (soft p η t) ∧ ∀ i (U:Config G n), ‖(P).logarithm i U‖ ≤ q i:=by
    let a:=η*t^(chip 0); let b:= 2*a; let q (i:ℕ):= if fixed (Key n) i then b else 0; have hx':0≤b:=mul_nonneg zero_le_two (mul_nonneg he.le (Real.rpow_nonneg (zero_le_one.trans ht) _))
    refine ⟨q,⟨fun i=>?_,fun x=>?_⟩,fun i U=>?_⟩
    · unfold q; split <;> first|exact hx'|exact le_rfl
    · let Y (i:Key n):=neighbors 4 (Key.native i); let F (i: Key n):= if x∈Y i then b * Real.exp ((ηT p+1)*coverNumber p.B (Y i)) else 0
      refine Padded.budget (α:=Key n) (g:=F) (fun j=> ?_) (fun i=> ?_) (?_)
      · unfold q; by_cases h:fixed (Key n) j
        · rw [if_pos h, if_pos h]; rfl
        rw [if_neg h,if_neg h]; simp
      · unfold F; split; exact mul_nonneg hx' (Real.exp_nonneg _); exact le_rfl
      let u:=b*kiosk (p.supportExponent+1) 1; have hu:0≤u:=mul_nonneg hx' (Real.exp_nonneg _)
      have hp (i:Key n): F i ≤ if i.native ∈ neighbors 4 x then u else 0 :=by
            have he:x∈ Y i ↔ i.native∈ neighbors 4 x:=by unfold Y; rw [neighbors_mem, neighbors_mem, separation_comm]
            unfold F; simp_rw [he]; split
            next h=> refine mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left ?_ (by unfold ηT; have he:=p.exponent_pos; positivity))) hx'; exact_mod_cast Scarf.standing 4 p 1 i.native (by omega)
            exact le_rfl
      let l (i:Key n): ℝ := if i.native ∈ neighbors 4 x then u else 0
      apply (Finset.sum_le_sum (g:=l) (fun i _=> hp i)).trans
      rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type (fun _: WilsonStartup.Cell n=> _)]
      change (∑ _:Signed,∑ y:Site n,∑ _:PlaqAxes, (if y∈neighbors 4 x then u else 0)) ≤ _
      have ht: ∑ y:Site n,(if y∈neighbors 4 x then u else 0)=(Finset.card (neighbors 4 x):ℝ)*u:= by rw [← Finset.sum_filter]; simp
      have hv : ∑ y:Site n, ∑ _ : PlaqAxes,(if y∈neighbors 4 x then u else 0)=(Fintype.card PlaqAxes:ℝ)*((Finset.card (neighbors 4 x):ℝ)*u):= by rw [Finset.sum_comm]; simp_rw [ht]; simp
      simp_rw [hv]; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]
      have hy : (Finset.card (neighbors 4 x):ℝ) ≤ ballCost 4 := by exact_mod_cast Animals.neighbors_card 4 x -- edit
      exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hy hu) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Eq.le (by change _ = (chum p)*b; unfold chum u; ring))
    · dsimp only [iceCap]; unfold q; split
      next h=> exact s_sut G p c η _ hP U hd hx hh
      simp

end YM.WilsonStartup.Frost
