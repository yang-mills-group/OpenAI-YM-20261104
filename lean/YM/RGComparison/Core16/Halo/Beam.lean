import YM.RGComparison.Core16.Halo.Cosmos
/-!
# Local limit shape to the A/Fk cover (top-case entire regulator)
Aim derives existence plus power/cut ℓ tails w.r.t actual period indexing.
Presence of `G0 Height.Rift` at upper coarse level Ep always assumes incoming one terminal; perpetuates same Φ prescription. Not asserting positivity of kinetic symbol coefficients. ('α≥1' throughout as in Λ parser).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Halo
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage Push.Uniform Push.AbsoluteSums.Animals Lam
open PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{C F c f:Side}{P: Patch}{K:KernelChoices}{d:f.val=c.val*P.L.val}{E:F.val=C.val*P.L.val}{a:ℕ}{W:Oven P}{X:Shelf G (PlaqAxes⊕Axis) W.Xways}

section operations
lemma rebate (u v: Site c→ℝ){A:ℝ} (h:∀ x,|u x-v x| ≤ A): |assembly u-assembly v| ≤ A:= by
     unfold assembly; rw [←sub_div, ←sum_sub_distrib,abs_div,abs_of_pos (vol_pos ..),div_le_iff₀ (vol_pos ..)]; exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun i _=> h i)).trans_eq (by simp [vol,mul_comm]))

variable (hA:C.val=c.val*a)
set_option quotPrecheck false
local notation "∂L"=> (show c.val∣ C.val from ⟨a,hA⟩)
local notation "Ω"=> splitter ∂L

include hA
lemma beam (x:Site C){n:ℕ}(hn:2*n < c.val) : SliceMap (neighbors n x) (neighbors n (Ω x)) Ω := by
   let B:=neighbors n x
   refine ⟨fun i hi=>(neighbors_mem ..).2 ((Deck.less ∂L x i).trans ((neighbors_mem ..).1 hi)), fun i hi j hj h=> ?_, fun i hi=> ?_⟩
   · apply Deck.tiniest ∂L h
     apply lt_of_le_of_lt (separation_triangle i x j)
     rw [separation_comm i x]; refine lt_of_le_of_lt (Nat.add_le_add ((neighbors_mem ..).1 (show i∈neighbors n x from hi)) ((neighbors_mem ..).1 (show j∈neighbors n x from hj))) ?_; omega
   exact ⟨Deck.rise ∂L x i,(neighbors_mem ..).mpr ((Deck.climb ..).trans_le ((neighbors_mem n _ _).1 hi)),Deck.dawns ..⟩

lemma repeated (F:Site c→ℝ): assembly (F ∘ Ω) = assembly F:=by
    unfold assembly; let M:ℝ:=a; have he:Fintype.card (Site C)=a^4*Fintype.card (Site c):= by rw [site_card,site_card,hA,mul_pow,mul_comm]
    rw [show (∑ i,(F ∘ Ω) i)= _ from (Shingle.multiplied Ω (basefold ∂L hA) F), div_eq_div_iff (vol_pos C).ne' (vol_pos c).ne', nsmul_eq_mul,vol,vol,he,Nat.cast_mul]; ring

lemma billboard (F:Site C→ Site C→ℝ)(Y:Site c→Site c→ℝ){n:ℕ}(hn:2*n < c.val){b:ℝ}(hb:0≤b)(x:Site C) (h:∀ y∈neighbors n x, |F x y-Y (Ω x) (Ω y)| ≤ b) : |frontage x F n - frontage (Ω x) Y n| ≤ ballCost n*(n:ℝ)^2*b:=by
    let F' :Site C→ℝ:=fun y=> wt x y* Y (Ω x) (Ω y)
    unfold frontage; rw [bonds Ω (beam hA x hn) F' _ ?_]; swap; · intro i hi; dsimp [F',wt]; rw [Deck.starsL hA _ _ (lt_of_le_of_lt (Nat.mul_le_mul_left 2 ((neighbors_mem ..).1 hi)) hn)]
    rw [←sum_sub_distrib]; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun _=>(n:ℝ)^2*b) (fun y hy=>?_)).trans ?_)
    · unfold F'; rw [← mul_sub, abs_mul]; apply mul_le_mul ((unit x y).trans ?_) (h y hy) (abs_nonneg _) (sq_nonneg _); unfold gaugeCard; exact_mod_cast (show _ ≤ n^2 from Nat.pow_le_pow_left ((neighbors_mem ..).1 (show y∈neighbors n x from hy)) 2)
    rw [sum_const,nsmul_eq_mul]; exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (neighbors_card ..)) (by positivity : 0≤(n:ℝ)^2*b)).trans_eq (mul_assoc ..).symm
end operations

variable (hW:P.Branches K G)(pW:Parcel.Oven.Offers W X K)
    {B : Forest (StepData.mk P K d).ratio}{B':Forest (StepData.mk P K E).ratio} (hA:C.val=c.val*a) (hB:2≤ c.val) (H: Bid.Larger (G:=G) (StepData.mk P K d)) (H' : Bid.Larger (G:=G) (StepData.mk P K E)) (V:Pinnage (zoom E d hA) B' B)(h : 24*(X.sector.b+1) ≤ c.val) {r:ℕ}

variable (w:G.ColorIndex)

def kernel (K :KernelChoices) (W: Oven P)(X:Shelf G (PlaqAxes ⊕ Axis) W.Xways)(B : Forest (StepData.mk P K d).ratio)(w:G.ColorIndex)(k:ℕ)(u v: Site c):= nth k (Lam.pokes W X B (ch w u) (ch w v))
def rate (X:Shelf G (PlaqAxes ⊕ Axis) W.Xways) := Silk.shade X/3
lemma rate_pos (X:Shelf G (PlaqAxes ⊕ Axis) W.Xways):0<rate X:= div_pos Silk.shade_pos (by norm_num)
lemma fixrate (X:Shelf G (PlaqAxes ⊕ Axis) W.Xways):3*rate X= Silk.shade X:=by unfold rate; ring

def returnMass (γ q:ℝ)(n:ℕ) := γ*(tail q n*(ceiling 2 q*countCost q))
local notation "ρ"=> rate X

def boundMass (L A:ℝ)(c:Side)(X:Shelf G (PlaqAxes ⊕ Axis) W.Xways):= let n:=c.val/16; (((ballCost n)*(n:ℝ)^2*A)*tail (Silk.shade X) n)+2*returnMass L (rate X) n

variable {x y:ℝ} (hX:KernelFare W X K r x)(hy:0≤ y)(hY:Reel X y (r+2) (r+2)) (k l:ℕ)(hk:k ≤ r)
-- copy shape through ALL cells actual cost and synchronized e.M.
include H' H hX pW V h hB hy hY hk
lemma bills : |cache (kernel K W X B' w k)-cache (kernel K W X B w k)| ≤ boundMass x (Lam.Exact K X (r+2) pW.good y) c X:=by
   let n:=c.val/16; let z:=24*(X.sector.b+1); let s:= splitter (show c.val∣ C.val from ⟨a,hA⟩); let F':=kernel K W X B' w k; let Y:= kernel K W X B w k; let A:=Lam.Exact K X (r+2) pW.good y; have hT:= rate_pos X; have hp :0≤A:= Lam.bona _ _ _ hy
   have hF i j: |F' i j|≤ x*Decay (3*ρ) i j:= by rw [fixrate]; exact hX.price _ _ E H' B' _ _ k hk
   have hu i j: |Y i j| ≤ x*Decay (3*ρ) i j:= by rw [fixrate]; exact hX.price _ _ d H B _ _ k hk
   unfold cache; rw [←repeated hA (outs (kernel K W X B w k))]; apply rebate; intro i
   have he : |frontage i F' n-frontage (s i) Y n| ≤ ballCost n*(n:ℝ)^2*(A*tail (Silk.shade X) n):=by
       refine billboard hA F' Y ?_ (mul_nonneg hp (payoff ..|>.le)) i (fun j hj=>?_); · unfold n; omega
       have hl:= (neighbors_mem ..).1 (show j∈ neighbors n i from hj); let T:= StepData.mk P K E
       let p:= (P.L.val); let b:= hold T i; have hℓ: separation b (hold T j) ≤ p*n:= by unfold b hold; rw [FreeResolvent.Mid.upto]; exact Nat.mul_le_mul_left _ hl
       have hC : p*n+n+X.sector.b ≤ f.val/3:= by
          have hp:0<p:=P.L.pos; have hK:16*n ≤ c.val :=Nat.mul_div_le c.val 16 -- direction?
          have hn:=Nat.mul_le_mul_left p hK; have hE : f.val ≥ c.val:= by rw [d]; exact Nat.le_mul_of_pos_right _ hp
          rw [mul_comm p c.val,←d] at hn; have hF:p*(16*n)=16*(p*n):= by ac_rfl
          omega
       rw [tail,neg_mul,Real.exp_neg,←div_eq_mul_inv]; refine Lam.smooth_earn pW hA hB H H' V ?_ (ch w i) (ch w j) n (r+2) hy hY b ?_ ?_ _ (by omega) (by change separation i j<c.val; unfold n at hl; omega)
       · have hp:f.val≥c.val:= d ▸ le_mul_of_one_le_right (Nat.zero_le _) P.L.pos -- bug replacement
         omega
       · change separation b b+_+_ ≤ _; rw [separation_self]; omega
       change separation b (hold T j)+_+_≤_; omega
   apply (abs_sub_le (outs F' i) (frontage i F' n) (outs Y (s i))).trans ((add_le_add (cancels F' hT hX.pos hF i n) ((abs_sub_le (frontage i F' n) (frontage (s i) Y n) (outs Y (s i))).trans (add_le_add he (abs_sub_comm ..|>.trans_le (cancels Y hT hX.pos hu (s i) n))))).trans_eq ?_)
   change returnMass x (rate X) n+(↑(ballCost n)*(n:ℝ)^2*(A*tail (Silk.shade X) n)+returnMass x (rate X) n)=↑(ballCost n)*(n:ℝ)^2*A*tail (Silk.shade X) n+2*returnMass x (rate X) n; ring
-- elaborate arguments below
end YM.RGComparison.Core16.Halo
