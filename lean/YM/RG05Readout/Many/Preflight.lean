import YM.RG05Readout.Many.Storage
/-!
# Width envelopes at mesh levels, pressure symbols

One γ-envelope for all branches when propagating under repeated root
projection. Actual recovery in this version uses fixed POWER weights in
`βhat`, i.e. radii vanish. The graph input size is external parameter of
that valuation. Coalescing (without using child gaps) takes a fresh power
at each step. Long separated intervals here use actual ancestor span and
support estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Many
open Function Filter MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker Address Native View Bid Pressure
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G} {n m p N d:ℕ}{V W : Type*}[DecidableEq V] [Fintype V] {R:Census V}{a b x y A t' :ℝ} {D:Address.Rail C} {w:Worth} {r:ℕ→ℕ}
set_option quotPrecheck false
local notation "Z"=> C.path.levels
local notation "pB"=> C.path.levels.budget
local notation "K"=> C.path.levels.clock
local notation "β"=> C.path.levels.clock.hatBeta
local notation "X"=> C.path.levels.S
local notation "δ"=> renal C.path.levels
local notation "φ"=> near C.path.levels
local notation "κ"=> far C.path.levels
local notation "ζ"=> Legato.Bandage.fly C.path.levels
local notation "ℶ"=> C.path.levels.S.block
local notation "LD"=> Copper.ld C.path.levels
-- d height, s>= maybe. enforce q increments arbitrary polynomial mages. T.λ restoration≤ scaleS.E
lemma theta_up (a:ℝ) (hG:G.Simple) : ∀ᶠ m:ℕ in atTop, a ≤ β m:= (Next.Rank.Station.hat_rate Z hG).eventually_ge_atTop a
lemma beta_le' (hG:G.Simple): Monotone β:=by
    intro i j hi; unfold Calendar.hatBeta; exact add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono _).monotone hi) (Gauge.slopeConstant_pos hG).le) _
lemma shifts (h:Storage C D) (hG:G.Simple) : ∀ᶠ i:ℕ in atTop, (LD i)≤( (ℶ i).val:ℝ) ∧ ((ℶ i).val:ℝ) ≤ β i ∧ β (i+1) ≤ (β i)^2:=by
    filter_upwards [(theta_up 8 (C:=C) hG), theta_up (2+ G.slopeConstant) (C:=C) hG] with i hi hp
    let b':=(β i); have hb:= show 8 ≤ b' from hi; let L:= (ℶ i); have hs: (L.val:ℝ)≥1:=by exact_mod_cast L.property
    have hz:0≤ Real.log b':= Real.log_nonneg (by linarith only [hb])
    have he: (L.val:ℝ) ≤ β i :=by
       refine (h.preMesh i).trans ?_; unfold Lambda
       have hf: 1+Real.log (2+Real.log b') ≤ 2 +Real.log b':= by linarith only [Real.log_le_sub_one_of_pos (x:=2+Real.log b') (by linarith only [hz])]
       apply le_trans hf _; rw [show b'=2*(b'/2) from by ring] -- careful unfolds b' on rhs, Lean
       have hx:= Real.log_le_sub_one_of_pos (x:=b'/2) (by linarith only [hb]); rw [Real.log_mul (by norm_num) (by linarith only [hb])] ; have h2:=Real.log_le_sub_one_of_pos (x:=2) (by norm_num); change _ ≤ b'; linarith only [hb,hx,h2]
    refine ⟨Real.rpow_le_self_of_one_le hs (by exact (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (by positivity))),he,?_⟩
    have ht : β (i+1)=b' +G.slopeConstant*Real.log (L.val:ℝ):=by unfold Calendar.hatBeta; erw [Schedule.scale_succ]; dsimp only [b', Calendar.hatBeta, L]; ring
    rw [ht]; apply le_trans (add_le_add_right (mul_le_mul_of_nonneg_left ((Real.log_le_self (zero_le_one.trans hs)).trans he) (Gauge.slopeConstant_pos hG).le) _)
    change b'+_*b' ≤ b'^2; change _ ≤ b' at hp; nlinarith only [hp,hb]

-- tariff deductions local.R.N head pre budget. no analytic calls.
local notation "dt"=> fun (i j:ℕ)=>(β i)^j

theorem startPay (hG:G.Simple) (d:ℕ) (u:ℝ)(hu:0< u):
    ∃ k≥d+3,∀ᶠ i:ℕ in atTop, 0< κ i ∧ ∀ j:ℕ,j≤d → pricesTop ζ κ i j*u≤κ i*((β i)^k):=by
    -- pays for all levels. put ψ=k.Data, no saving charges
    obtain ⟨n,hn⟩ :(∃ n:ℕ,∀ i:ℕ, i≤d → ∀ p:Letter i,winter G (kept p)+1≤n) := by
       let x:= fun (j: Sigma (fun k:Fin (d+1)=> Letter k.val)) => winter G (kept j.2)+1
       refine ⟨Finset.univ.sup x, fun i hi p=> ?_⟩
       exact Finset.le_sup (f:=x) (Finset.mem_univ (@Sigma.mk (Fin (d+1)) (fun j:Fin (d+1)=>Letter j.val) (⟨i,by omega⟩:Fin (d+1)) p)) -- inference
    let k:= n+d+3
    refine ⟨k,(by dsimp [k]; omega),?_⟩
    filter_upwards [ (eventually_all_finset (Finset.range (d+1))).mpr (fun j _=>theta_up (C:=C) (pulseFee j*u*(Fintype.card (Letter j):ℝ)) hG)] with i hh
    have he:= (Z).fits.delayed i; have hz:0 < κ i:= div_pos (inv_pos.mpr (Real.sqrt_pos.mpr (zero_lt_one.trans he))) (by norm_num)
    refine ⟨hz,fun j hj=>?_⟩
    have hk: 0<k:= Nat.pos_of_ne_zero (by dsimp[k];omega)
    have hP: k-1+1=k:=by omega
    let M (p:Letter j):= κ i/ (Legato.Bandage.fly Z (kept (d:=j) p) i)
    have he'(p): M p ≤ κ i * (β i)^(k-1):=by
       unfold M Legato.Bandage.fly fog; rw [div_inv_eq_mul]; apply mul_le_mul_of_nonneg_left _ hz.le; apply pow_le_pow_right₀ he.le; have hp:= hn j hj p; dsimp [k]; omega
    unfold pricesTop; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p _=> he' p)) (feepos j).le) hu.le) ?_
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; have hx:= mul_le_mul_of_nonneg_right (hh j (Finset.mem_range.mpr (by omega))) (show 0 ≤ κ i*(β i)^(k-1) from mul_nonneg hz.le (pow_nonneg (zero_le_one.trans he.le) _)); rw [show β i*(κ i*(β i)^(k-1))= κ i*((β i)^k) from ?_] at hx; nlinarith only [hx]; rw [mul_left_comm,← pow_succ', hP] -- directions

-- m post exponent loans. with u fine allowance, t close modifier
noncomputable def markWidth (C:Family G)(m k:ℕ)(x:ℝ):= ((C.path.levels.clock.hatBeta m)^k)⁻¹ / x
variable (hC:Storage C D) (hG:G.Simple) (d k:ℕ) (hk:d+3 ≤ k)

structure Refresh (i:ℕ) :Prop where
    first (Q R U:ℝ) (hX:0<Q) (hy:0< R)(hu:U ≤ 1)(hu':0< U)(hY: Q ≤ ((C.S.block i).val:ℝ)^d*R): 2*(U*markWidth C (i+1) k R)*(Copper.ld C.path.levels i * (Copper.ld C.path.levels i * Q))≤1
    restoration (Q R:ℝ)(hX:0<Q)(hy:0< R)(hp:R ≤ ((C.S.block i).val:ℝ)^d*Q): markWidth C i k Q *((C.S.block i).val:ℝ)^d ≤ ((renal C.path.levels i)* markWidth C (i+1) k R)*mintK (C.path.levels.budget i).B
    sacrifice (Q R:ℝ)(hX:0<Q)(hy:0<R)(hp:R ≤ ((C.S.block i).val:ℝ)^d*Q): (markWidth C i k Q *((C.S.block i).val:ℝ)^d)/((β i)^(3*k+4)) ≤ (renal C.path.levels i)*markWidth C (i+1) k R -- `β` notation issue C explicit?

private lemma renal_value (i:ℕ):δ i = ((β (i+1))^ (2:ℕ))⁻¹:=by
    unfold Bandage.renal Mallow.probe; rw [Real.rpow_neg (zero_le_one.trans ((Z).fits.delayed _).le),Real.rpow_ofNat]
include hk hG hC
lemma refreshes : ∀ᶠ i:ℕ in atTop, Refresh (C:=C) d k i:=by
   filter_upwards [shifts hC hG, (Next.Rank.Station.hat_rate Z hG).eventually (polestar 1 zero_le_one (3*k+4) 0), theta_up (C:=C) 2 hG] with i hi hv he
   let x:= β i; let y:= β (i+1); let L:ℝ:=(ℶ i).val; let l:=LD i
   obtain ⟨hD,hL,hY⟩:=hi; have hlog:=beta_le' (C:=C) hG (show i ≤ i+1 from i.le_succ); have hl: l≤ L:= hD; have hl':= show L≤x from hL; have hg:=show 2 ≤ x from he; have hy:=show x≤y from hlog; have hx:=show 0<x by linarith only [hg]
   have hb:=show 0<y from hx.trans_le hy; have hℓ:l ≥ 1:= lamp_nn _
   -- Use coherent ratios here also for the coalescing window.
   have h0:0≤L:=by linarith
   have hxT : x^(3*k+4) ≤ mintK ((pB i).B):=by simp only [one_mul,add_zero] at hv; exact hv
   have hQ(Q R:ℝ)(hX:0<Q)(hR:0<R)(he:R ≤ L^d*Q): markWidth C i k Q * L^d ≤ δ i*markWidth C (i+1) k R*x^(3*k+4):=by
      have he' : L^d≤ x^d:= pow_le_pow_left₀ h0 hl' _
      have hs: y^k ≤ x^(2*k):=(pow_le_pow_left₀ hb.le (show y ≤ x^2 from hY) k).trans_eq (pow_mul ..).symm
      have hz: y^2≤x^4:=(pow_le_pow_left₀ hb.le (show y ≤ x^2 from hY) 2).trans_eq (pow_mul ..).symm
      -- clear
      suffices L^d*(y^2*y^k*R) ≤ x^(3*k+4) * (x^k*Q) by rw [renal_value]; unfold markWidth; change (x^k)⁻¹ / Q * L^d ≤ (y^2)⁻¹*((y^k)⁻¹/R)*x^(3*k+4); field_simp; nlinarith only [this]
      have hr:= he.trans (mul_le_mul_of_nonneg_right he' hX.le)
      apply (mul_le_mul he' (mul_le_mul (mul_le_mul hz hs (pow_nonneg hb.le _) (pow_nonneg hx.le _)) hr hR.le (by positivity)) (by positivity) (by positivity)).trans
      have hTx: d+(4+(2*k)+d) ≤ (3*k+4)+k:=by omega
      calc x^d*( x^4*x^(2*k)*(x^d*Q)) = x^(d+(4+(2*k)+d))*Q:=by simp only [pow_add]; ring
           _ ≤ x^(3*k+4+k)*Q:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith only [hg]) hTx) hX.le
           _ = _:=by rw [pow_add,mul_assoc]
   refine ⟨?_,fun Q R hx hr hq=> (hQ Q R hx hr hq).trans (mul_le_mul_of_nonneg_left hxT (by rw [renal_value]; unfold markWidth; exact mul_nonneg (inv_pos.mpr (pow_pos hb _)).le (div_nonneg (inv_pos.mpr (pow_pos hb _)).le hr.le))),?_⟩
   · intro Q R U hX hR hU hU' ht'; let W:=markWidth C (i+1) k R; have hW:0<W:=div_pos (inv_pos.mpr (pow_pos hb _) ) hR
     change 2*(U*W)*(l*(l*Q))≤1
     have hz:x^d ≤ y^d:=pow_le_pow_left₀ hx.le hy _
     have h: l*(l*Q) ≤ y^(2+d) * R:=by
         apply le_trans (b:=y*(y*(y^d*R))) _ (le_of_eq (by rw [pow_add]; ring))
         have hc:=hl.trans (hl'.trans hy)
         exact mul_le_mul hc (mul_le_mul hc (ht'.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (hl'.trans hy) d) hR.le)) hX.le hb.le) (mul_nonneg (zero_le_one.trans hℓ) hX.le) hb.le
     apply (mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hW.le hU) zero_le_two) h (by have hp:0≤l:=zero_le_one.trans hℓ; positivity) (by positivity)).trans
     have he':2*y^(2+d) ≤ y^k:= by
        calc 2*y^(2+d) ≤ y*y^(2+d):=mul_le_mul_of_nonneg_right (le_trans hg hy) (by positivity)
             _ = y^(2+d+1):=(pow_succ' ..).symm
             _ ≤ y^k:= pow_le_pow_right₀ (by linarith only [hy,hg]) (by omega)

     unfold W markWidth; change 2*((y^k)⁻¹/R)*(y^(2+d)*R)≤1; field_simp; nlinarith only [he']
   intro Q R hX hR H
   exact (div_le_iff₀ (pow_pos hx _)).mpr (hQ Q R hX hR H)
end YM.RG05Readout.Many
