import YM.RGComparison.Core16.Lam.Scan
/-!
# At TORUS, before endpoint limiting: ∑moment_fΛ mass transport

Large-to-small REP on coherently purchased K,S clocks, no beta-change stuff. Cost of closeλ windows with rooted u&v compared then initial release taken afterwards. Not consuming world count READY `Efficiencies` by uplifting entire torus measure. Θ sector through `Silk`. Price only on the *analytic* germ at that aperture used in the point-accuracy comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lam
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity Finset
open Precision Push.BetaTransport Next.Fluctuations Pressure
open Parcel Parcel.Oven Forge.Hut Silk Stage Push.Uniform Push.AbsoluteSums.Animals
open scoped Topology ContDiff PowerSeries BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge} {C F c f:Side} {P: Patch} {K:KernelChoices} {d:f.val=c.val*P.L.val} {E:F.val=C.val*P.L.val}
    {W:Oven P}{X:Shelf G (PlaqAxes⊕Axis) W.Xways}

variable (hS:P.Branches K G) (hW: Parcel.Oven.Offers W X K) (B:Forest (StepData.mk P K d).ratio) (H: Bid.Larger (G:=G) (StepData.mk P K d))
local notation "S"=> StepData.mk P K d
local notation "G0"=> gear S B X
-- no include
private lemma ghost (i j:Operand G c)(h:i.1≠j.1): smooth W X B i j=0:= by
   unfold Lam.smooth heatΨ Silk.stamps; rw [if_neg (show ¬ (tier i j).1=true by unfold tier; simp [h]),show night (G:=G) (harp B X i) 0 (price G0) [] = 0 from funext fun u=> nap (L:=W.Xways) .., day_zero]; -- typo

lemma order_bill (i j:Operand G c)(n:ℕ): nth n (pokes W X B i j)= nth n (smooth W X B i j)-nth (2+n) (osier W X B i j):=by unfold pokes nth pursed.solder; rw [map_sub,PowerSeries.coeff_mk]

private lemma far (i j:Operand G c)(t:ℕ)(h:t+2*X.sector.b ≤ separation i.1.1 j.1.1) {u v} (hp:u∈ (G0).soil (.inr i.1))(hv:v∈(G0).soil (.inr j.1)) : t ≤ separation ((G0).loc u) ((G0).loc v):= by
   let A:= hold S i.1.1; let B':= hold S j.1.1; let p:=(G0).loc u; let q:=(G0).loc v; have he: separation A p≤X.sector.b:= (member ..).1 hp; have hq:separation q B'≤ X.sector.b:=by rw [separation_comm q]; exact (member ..).1 hv
   change _ ≤ separation p q; have hz:= separation_triangle A p B'; have hm:= separation_triangle p q B'; have hh: t+2*X.sector.b ≤ separation A B':= by change _ ≤ separation ((S).ratio.embed _) ((S).ratio.embed _); rw [FreeResolvent.Mid.upto]; exact h.trans (le_mul_of_one_le_left (Nat.zero_le _) (by change 1 ≤ P.L.val; exact P.L.pos))
   omega

-- cost of derivative kernels with true θ Step_ℓ. Reimburse after amplification by REAL cap-price with σ = Lamp.
structure KernelFare (W:Oven P)(X:Shelf G (PlaqAxes⊕Axis) W.Xways)(K:KernelChoices)(r:ℕ)(y:ℝ): Prop where
    pos: 0≤y
    price : ∀ (c f:Side)(d:f.val=c.val*P.L.val), Bid.Larger (G:=G) (StepData.mk P K d)→ ∀ (B:Forest (StepData.mk P K d).ratio) (i j:Operand G c), ∀ k:ℕ, k ≤ r→
        |nth k (pokes W X B i j)| ≤ y * Decay (Silk.shade X) i.1.1 j.1.1

include hW hS
omit hS hW in
lemma expPaid {i j : Site c} : Decay (Silk.shade X) i j= (costLamp X (separation i j))⁻¹:=by unfold Decay costLamp; rw [neg_mul,Real.exp_neg]
lemma flowing (r:ℕ) : ∃ c:ℝ, KernelFare W X K r c := by
   let z:= X.sector.b; let P0:=(Axis×G.ColorIndex) × Axis × G.ColorIndex
   obtain ⟨v,hv,hp⟩:= silence hW.good (r+2) (r+2) (r+2); obtain ⟨U,c₀,h,hE,hL,hQ⟩:= marquee hS hW ⟨1,0,le_rfl⟩ r
   let F(p:P0):= bond_fee (tileΨ W K p.1) (tileΨ W K p.2) X.Q (r+2)
   let A:=∑ i:P0, |F i|
   have hz:0≤A:= sum_nonneg fun _ _ => abs_nonneg _; let x:= v*A+c₀; have ht:0≤x:= by unfold x; positivity
   refine ⟨x* costLamp X (2*z),mul_nonneg ht coin_pos.le, fun c f d H B i j k he=> ?_⟩
   let S':= StepData.mk P K d; let u:=separation i.1.1 j.1.1; rw [expPaid]; -- 
   let V(n:ℕ):= costLamp X n
   rw [← div_eq_mul_inv, le_div_iff₀ (coin_pos)]
   by_cases hh:u ≤ 2*z
   · have h' := hQ c f d H B i j|>.front k he; exact mul_le_mul (h'.trans (le_add_of_nonneg_left (mul_nonneg hv hz))) (Silk.shade_mono X hh) coin_pos.le ht
   have hi: i.1≠ j.1:= by intro h; unfold u at hh; rw [h,separation_self] at hh; omega
   let n:= u-2*z; have hN : n+2*z=u:= (Nat.sub_add_cancel (le_of_not_ge hh))
   have hU : |nth (2+k) (osier W X B i j)| ≤ v / V n * F (profileDatum i,profileDatum j):= by
       let p:=harp B X i; let q:=harp B X j; apply Silk.ramp (T:=_) (paint S' B hW H) (p:=p) (q:=q) (housed hW B H i).2 (housed hW B H j).2 (daily hS W _).1 (daily hS W _).1 hv hp (fun p hx q hq=> far B _ _ n hN.le hx hq) (by omega)
   rw [order_bill, ghost B i j hi,nth,map_zero, zero_sub,abs_neg]; change |nth _ _| * costLamp X u ≤ x*_
   have hx: 0<V n:=coin_pos
   refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hL) coin_pos.le)
   rw [show costLamp X u= V n* V (2*z) from hN ▸ sumgrid ..,←mul_assoc]; refine mul_le_mul_of_nonneg_right (le_trans (mul_le_mul_of_nonneg_right hU hx.le) ?_) coin_pos.le
   have he:F (profileDatum i,profileDatum j) ≤ A:= (le_abs_self _).trans (single_le_sum (f:=fun i=>|F i|) (fun i _=> abs_nonneg _) (mem_univ _)); refine LE.le.trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left he hv); field_simp
end YM.RGComparison.Core16.Lam
