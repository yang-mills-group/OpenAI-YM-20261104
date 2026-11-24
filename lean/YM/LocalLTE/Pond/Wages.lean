import YM.LocalLTE.Pond.Copper
/-! Budget handoff, oxidizing pre+post affines. No receptive assumptions on stencil prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Collection.Price
open Function Filter Lattice RG Pressure Precision Tree Wilson Finset
open Progress.DirectedRecipe
open Push Pressure.Tube Push.AbsoluteSums Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Pulse Mask Poll Coat Blaze Brush
open UVNext.PricedKernels Next.Scheduling
open PhysicalNext.Repeat Fare Lapis Lantern Shellac Token Sienna Boulevard Scarf
open LocalLTE.FrameBox LocalLTE.FrameBox.Hall Grove LocalLTE.Fan Pastel StressFlux
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable (G : Gauge) {n : Side} {j:ℕ} {C V: ℝ}
attribute [local instance] Gauge.frobInner
-- uniform over all low rows. weights only station 
open Residual Geo Animals
open Quotes
variable {G}
open Extra.Iteration Urns
variable {t σ C' Λ Δ α k κ a v w u:ℝ} {c:Clip} {L:Side} {p:BudgetPoint} {d N:ℕ}
variable {R:PathData G}(hR:R.Bounds c σ C' Λ) (hv : Width p c σ)(hG:G.Simple)(hn:20<n.val)(hg:32*p.B<n.val) (ht:p.B=Pressure.radiusB t) (hC:p.threshold=Pressure.temp t) (he:p.threshold ≤2*Pressure.fiery G t L)(hx:1 ≤ betaF G t L) (hb:3 ≤ p.B)(hk:Reliable G κ k) (hd:WilsonStartup.Decent c p)
-- Numerics.After.D.D F.bore universe all.Current.True accuracy.
variable (X:Listing G n) (g:Source G n) (P0:ℕ→Pot G n)(V:Tour X d)
-- regular term ∀ reactor. F_j cumulative input. ε_φ from P. Lens
variable (m :ℕ) (hM: Merchant G L κ p.order p.power m d t)(hF:Found G L κ p.order p.power m t)
variable (hg' : Meadow.Budget p X.reg g.logRead a) (hV: Portrays X d κ m g.logRead V)
local notation "u₀"=> betaF G t L ^ Urns.dust m
variable (hr:32*d<n.val)
include hr hV ht hC he hg' hG hk hn hR hv hd hb hM hF hx hg
-- NUM model caps. low kernel synth κ.
def vest (p:BudgetPoint)(Δ α:ℝ)(m h:ℝ) (c:Clip)(G:Gauge)(σ C':ℝ): ℝ:= m*(resetFee G p*h)+(turnFee p*(|Δ| *p.threshold^2)*(slope p σ*lowBase G c p σ C') +(turnFee p * (|Δ| * m))*(anchoredFee p lowCount*lowerSize c C')) +tH p*(turnFee p *(|α+Δ| *p.threshold^3)*(slope p σ*highBase G p σ C')+(turnFee p*(|α+Δ| * m))*(anchoredFee p highCount*(C'+C')))
def postal (p:BudgetPoint)(Δ α:ℝ)(m h:ℝ) (c:Clip)(G:Gauge)(σ C':ℝ) := vest p Δ α m h c G σ C'
lemma crown (α Δ:ℝ) : Stocked p (Price.tubeX R p X) (archive X R c g α Δ - Price.vane R c p X d V κ α Δ m g.logRead) (vest p Δ α (betaF G t L ^ Urns.dust m) a c G σ C'):=by
    obtain ⟨s',hs',ht'⟩:= hg'
    have hz (i:EKey n):=Collection.Local.quote_regular (X:=X) (v:=g) hG hR hd α Δ (fun i=> (ht' i).2) (fun i=> (ht' i).1) i
    let E:=u₀; let B₁ :=c
    let F:= archive X R c g α Δ; let P:= Price.vane R c p X d V κ α Δ m g.logRead; let Y:= Price.tubeX R p X
    let A₁:= turnFee p * (|Δ| * E); let A₂:= turnFee p * (|α+Δ| * E); have hy:0≤E:= Real.rpow_nonneg (zero_le_one.trans hx) _
    let θ (i:ℕ):= E*s' i; let ψ' (i:Faces n):=A₁* |i.2.mark R c|; let ω' (i:Spikes n):=A₂*(i.2.charge R)
    let φ (i:Faces n):=(if p.B ≤ i.2.length R then Lret p R c Δ i else 0); let th' (i:Spikes n):=(if p.B ≤ i.2.length R then Hret p R α Δ i else 0); let Q:=Sum.elim θ (Sum.elim (φ+ψ') (th'+ω')); have hy₁:0≤ A₁:=mul_nonneg (turnFee_pos p).le (mul_nonneg (abs_nonneg _) hy); have hy₂:0≤ A₂:=mul_nonneg (turnFee_pos p).le (mul_nonneg (abs_nonneg _) hy)
    have he₁:= Quotes.anchored_scale (r:=A₁) hy₁ (Price.lBase (n:=n) hR p hv)
    have h₁:= Price.lambC (n:=n) hR p Δ hv
    have he₂:=Quotes.anchored_scale (r:=A₂) hy₂ (hBase (n:=n) hR p hv); have h₂:= Price.hartC (n:=n) hR p Δ α hv
    have hψ (i:Faces n): 0≤ ψ' i:=mul_nonneg hy₁ (abs_nonneg _); have hω (i:Spikes n):0≤ ω' i:=mul_nonneg hy₂ (Finset.sum_nonneg fun _ _=> abs_nonneg _)
    let f:=(F-P)
    have H(i:EKey n): p.supBounds (Y i|>.site) (Y i|>.support) (f i) (Q i) :=by
     rcases i with i|i|i
     · change p.supBounds (X.reg i).site (expand _) (rebate _ _ - Price.hail X d V g.logRead κ m i) (E*s' i)
       cases h: V i with
       | none=>
          unfold Price.hail; rw [h,hV.stays i h]; change p.supBounds _ _ (rebate (X.reg i) 0-0) _; rw [Magnet.reclaim p,sub_zero]
          exact VerifiedReset.sup_le (VerifiedReset.sup_const (0:ℝ)) (abs_zero.trans_le (mul_nonneg hy (ht' _|>.2.1)))
       | some A'=> unfold Price.hail; rw [h,mul_comm E]; exact hM p rfl rfl hC he n hr (X.reg i) A' _ _ (ht' _ |>.1) (ht' _ |>.2) hG
     · let q:=i.2; let W:= i.1; change p.supBounds W.2 _ (Low.fresh R c q 0 (factor*Δ) ∘ W.view-swan R c p m κ 0 (factor*Δ) q ∘ W.view) (φ i+ψ' i)
       by_cases h: Low.length R q < p.B
       · let g':=swan R c p m κ (0:Site n) (factor*Δ) q; let f':=Low.fresh R c q (0:Site n) (factor*Δ)
         have he:= hF n p.B ht hg c R hR p rfl rfl rfl hC he hb hd (factor*Δ) (factor*α) (0:Site n)|>.1 q h
         have ht:p.Regular (q.home R p 0) (f'-g'):= reg_sub (Low.fresh_regular R c q 0 hd (factor*Δ)) ((Price.payL hb hd hk hG (0:Site n) hn q (factor*Δ) (R:=R) (j:=m)).1) -- edit
         unfold φ; rw [if_neg (not_le.mpr h),zero_add]; apply VerifiedReset.sup_le (W.sup ht he); unfold ψ' A₁; change turnFee p*_≤_; rw [abs_mul,abs_of_pos factor_pos]; have hx:= mul_le_of_le_one_left (abs_nonneg Δ) factor_le; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx (abs_nonneg (q.mark R c))) hy) (turnFee_pos p).le]
       rw [swan,if_neg h,show (0:Config G n→ℝ) ∘ W.view=0 from rfl,sub_zero]; unfold φ; rw [if_pos (not_lt.mp h)]; exact VerifiedReset.sup_le (hz (Sum.inr (Sum.inl i))) (le_add_of_nonneg_right (hψ _))
     let q:=i.2; let W:= i.1; change p.supBounds W.2 _ (High.fresh R q 0 _ _ ∘ W.view - craneH R p m κ 0 (factor*α) (factor*Δ) q ∘ W.view) (th' i+ω' i)
     by_cases h: High.length R q < p.B
     · let g':=craneH R p m κ (0:Site n) (factor*α) (factor*Δ) q; let f':=High.fresh R q (0:Site n) (factor*α) (factor*Δ)
       have he:= hF n p.B ht hg c R hR p rfl rfl rfl hC he hb hd (factor*Δ) (factor*α) (0:Site n) |>.2 q h
       have ht:p.Regular (bloomH R p 0 q) (f'-g'):= reg_sub (reg_larger (High.fresh_regular R q (0:Site n) hR p _ _) (Price.erect R p (0:Site n) q)) ((Price.payH hR hk (P:=p) (0:Site n) q hG (factor*α) (factor*Δ) (j:=m)).1) -- edit
       unfold th'; rw [if_neg (not_le.mpr h),zero_add]; apply VerifiedReset.sup_le (W.sup ht he); change turnFee p*_≤_; rw [← mul_add,abs_mul,abs_of_pos factor_pos]
       unfold ω' A₂; have hq:0 ≤ q.charge R:= Finset.sum_nonneg fun _ _=> abs_nonneg _
       change turnFee p*((factor*|α+Δ| * q.charge R)*E)≤ _; have hx:= mul_le_of_le_one_left (abs_nonneg (α+Δ)) factor_le; linarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hx hq) hy) (turnFee_pos p).le]
     rw [craneH,if_neg h,show (0:Config G n→ℝ) ∘ W.view=0 from rfl,sub_zero]; unfold th'; rw [if_pos (not_lt.mp h)]; exact VerifiedReset.sup_le (VerifiedReset.sup_larger (hz (Sum.inr (Sum.inr i))) ((Price.boostT X (Sum.inr (Sum.inr i))).2)) (le_add_of_nonneg_right (hω _))
    have hgB:Meadow.Budget p X.reg g.logRead a:= ⟨s',hs',ht'⟩
    refine ⟨Q,fun i=> ⟨VerifiedReset.reg_sub ((Price.masters hR hG hn hd X g i α Δ (fun i=> (ht' i).1)).1) (Price.reflectance R c p X d V _ a hd hR hb hgB hk hG hn i|>.1) ,H i⟩,fun i=>?_⟩ -- edit reflect
    let N:= tH p; unfold vest; rw [add_assoc (betaF G t L^Urns.dust m*_)]
    apply Cost.sum
    · have hyQ:1≤ resetLoss G p:= le_trans (by norm_num : (1:ℝ) ≤ 2) (le_add_of_nonneg_right (multiplier_nonneg ..))
      have hz:= (Quotes.enlarging G X.reg (by omega) (fun i=> (ht' i).2.1) hs').1
      refine budget_mono (Quotes.anchored_scale hy hz i) (fun x=> ?_) (fun x=> ?_)
      · split; next=> exact mul_nonneg (Real.exp_nonneg _) (H (Sum.inl x)).1
        exact le_rfl
      change (if (X.reg x).site=i then p.mass _ (θ x) else 0) ≤ (if (X.reg x).site=i then p.mass _ (E*(resetLoss G p*s' x)) else 0)
      split
      next he=> exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (ht' x|>.2.1) hyQ) hy) (Real.exp_nonneg _)
      exact le_rfl
    apply Cost.sum
    · have hh: anchored p (lowEntry G R p) (φ+ψ') (turnFee p*(|Δ| * p.threshold^2)*(slope p σ*lowBase G c p σ C')+ A₁*(anchoredFee p lowCount*lowerSize c C')) := by
        intro i'; have hh:= budget_plus (h₁ i') (he₁ i'); convert hh using 2 with j; dsimp only [Pi.add_apply]; split
        next h => exact mul_add ..
        exact (zero_add _).symm
      exact hh i
    have hh: anchored p (highEntry G R) (th'+ω') (turnFee p*(|α+Δ| * p.threshold^3)*(slope p σ*highBase G p σ C')+A₂*(anchoredFee p highCount*(C'+C'))):=by
       intro i'; convert budget_plus (h₂ i') (he₂ i') using 2 with j; dsimp only [Pi.add_apply]; split
       next h=>exact mul_add ..
       exact (zero_add _).symm
    exact Price.heightL (p:=p) (fun i=> (H (Sum.inr (Sum.inr i))).1) hh i
end YM.AnalyticBridge.VerifiedReset.Collection.Price
