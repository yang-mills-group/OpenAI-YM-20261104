import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPassengerVertex
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Procession

/-! Pay the source-labelled union mask in its original physical seat, so that
the nominal registered list can be used without moving the field or its denominator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1450000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local Push.AbsoluteSums.Paths
open AnalyticBridge VerifiedReset UVNext.PricedKernels
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{k:ℕ}
local notation "Fld" => Config G n

def seated (p:BudgetPoint)(t:Seat n)(a b:Atom G k)(W:Fld):ℝ:=
  shadow p (t.spread (contactSupport a b 0)) (fun Q=>contactBody a b 0 (t.view Q)) W

private theorem seated_bound (p:BudgetPoint)(t:Seat n)(a b:Atom G k)(W:Fld)
    (wallet:b.magnitude≤a.magnitude):|seated p t a b W|≤2*(a.magnitude*2^k):=by
  have nn:0≤a.magnitude:=by unfold Atom.magnitude;positivity
  by_cases ok:Healthy p.threshold (t.spread (contactSupport a b 0)) W
  · simp only [seated,shadow,masked_eq _ _ _ _ ok,sub_self,abs_zero];positivity
  simpa only [seated,shadow,masked_ne _ _ _ _ ok,zero_sub,abs_neg] using contact_body_bound a b _ (t.view W) wallet

theorem seated_contact_price (p:BudgetPoint)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V)(t:Seat n)(a b:Atom G k)
    (trim:b.length≤a.length)(wallet:b.magnitude≤a.magnitude){σ:ℝ}(sp:0<σ):
    |seated p t a b U-seated p t a b V|≤a.budget σ*((2:ℝ)^(k+2)*Real.exp (-(σ/4)*(D:ℝ))*
      Real.exp (-(σ/2)*(separation e.1 t.2:ℝ))):=by
  let X:=t.spread (contactSupport a b (0:Site n))
  let F:Fld→ℝ:=fun W=>contactBody a b 0 (t.view W)
  have loc:LocalOn X F:=by
    intro U' V' eq
    have eq':Agrees (↑(contactSupport a b (0:Site n)):Set (Site n)) (pull t.1 t.2 U') (pull t.1 t.2 V'):=agrees_pull t.1 t.2 eq
    have ha:=Next.Rank.Alarm.unmasked_space a (0:Site n) (t.view U') (t.view V')
      (agrees_mono eq' (fun _ hy=>Finset.mem_union_left _ hy))
    have hb:=Next.Rank.Alarm.unmasked_space b (0:Site n) (t.view U') (t.view V')
      (agrees_mono eq' (fun _ hy=>Finset.mem_union_right _ hy))
    simp only [F,contactBody,ha,hb]
  have reach(y:Site n)(hy:y∈X):separation t.2 y≤a.length:=by
    obtain ⟨v,hv,rfl⟩:=mem_image.mp hy
    change separation t.2 (turnSites t.1 t.2 v)≤a.length
    have dist:=turn_sep t.1 t.2 (0:Site n) v
    rw [t.turn_zero] at dist;rw [dist]
    rcases mem_union.mp hv with h|h
    · apply where_slot (0:Site n) a.leg v;rw [←atom_foot];exact h
    apply le_trans _ trim;apply where_slot (0:Site n) b.leg v;rw [←atom_foot];exact h
  have price:=local_shadow_price p e D a.length U V same cold after (1:Signed) t.2 X F loc reach
    (fun W=>contact_body_bound a b 0 (t.view W) wallet) sp
  have id(W:Fld):pull (1:Signed) 0 W=W:=by rw [pull_one];funext b;simp [Lattice.translate]
  have point:turnSites (1:Signed) 0 t.2=t.2:=by change affine 1 0 t.2=t.2;simp [affine]
  rw [id,id,point] at price
  apply price.trans_eq
  unfold Atom.budget;rw [pow_succ,pow_succ];ring

/-- One signed passenger packet as filed in every position, including
all wrapping sites and every label of its countable physical array. -/
def seatLedger (A B:ℕ→Atom G k)(p:BudgetPoint)(U:Fld):ℝ:=
  (Fintype.card Signed:ℝ)⁻¹*∑t:Seat n,∑'i,seated p t (A i) (B i) U

theorem seated_sums (A B:ℕ→Atom G k){σ C:ℝ}(sp:0<σ)
    (pay:SumBudget (fun i=>(A i).budget σ) C)(wallet:∀i,(B i).magnitude≤(A i).magnitude)
    (p:BudgetPoint)(t:Seat n)(U:Fld):Summable (fun i=>seated p t (A i) (B i) U):=by
  apply (pay.2.1.mul_right (2*(2:ℝ)^k)).of_norm_bounded;intro i
  apply (seated_bound p t (A i) (B i) U (wallet i)).trans
  nlinarith only [mul_le_mul_of_nonneg_right ((A i).lower_budget σ sp) (show 0≤(2:ℝ)^k by positivity)]

theorem seated_passenger_price (A B:ℕ→Atom G k){σ C:ℝ}(sp:0<σ)
    (pay:SumBudget (fun i=>(A i).budget σ) C)(trim:∀i,(B i).length≤(A i).length)
    (wallet:∀i,(B i).magnitude≤(A i).magnitude)
    (p:BudgetPoint)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (out:∀b:Edge (Site n),b≠e → U b=V b)(cold:Healthy p.threshold (halo D {e.1}) U)
    (after:e.1∉flags p.threshold V):|seatLedger A B p U-seatLedger A B p V|≤
    2*atomCash k σ C D:=by
  let c:ℝ:=(2:ℝ)^(k+2)*Real.exp (-(σ/4)*(D:ℝ))
  let w:=fun z:Site n=>Real.exp (-(σ/2)*(separation e.1 z:ℝ))
  let d:=fun t:Seat n=>fun i:ℕ=>seated p t (A i) (B i) U-seated p t (A i) (B i) V
  have cn:0≤c:=by dsimp only [c];positivity
  have cash:0≤C:=(tsum_nonneg pay.1).trans pay.2.2
  have diff(t:Seat n):HasSum (d t) ((∑'i,seated p t (A i) (B i) U)-(∑'i,seated p t (A i) (B i) V)):=
    (seated_sums A B sp pay wallet p t U).hasSum.sub (seated_sums A B sp pay wallet p t V).hasSum
  have one(t:Seat n):|(∑'i,seated p t (A i) (B i) U)-(∑'i,seated p t (A i) (B i) V)|≤
      (C*c)*w t.2:=by
    rw [←(diff t).tsum_eq]
    have per:∀i,‖d t i‖≤(A i).budget σ*(c*w t.2):=fun i=>seated_contact_price p e D U V out cold after t (A i) (B i) (trim i) (wallet i) sp
    exact (norm_tsum_le_tsum_norm (diff t).summable.norm).trans (((diff t).summable.norm.tsum_le_tsum per (pay.2.1.mul_right _)).trans (by
      rw [tsum_mul_right];exact (mul_le_mul_of_nonneg_right pay.2.2 (mul_nonneg cn (Real.exp_pos _).le)).trans_eq (mul_assoc ..).symm))
  let K:ℝ:=Fintype.card Signed
  have kp:0<K:=Nat.cast_pos.mpr Fintype.card_pos
  have geo:∑t:Seat n,(C*c)*w t.2≤K*((C*c)*basin (σ/2)):=by
    rw [Fintype.sum_prod_type]
    simp only [sum_const,card_univ,nsmul_eq_mul,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (funnel (half_pos sp) e.1) (mul_nonneg cash cn)) kp.le
  unfold seatLedger;rw [←mul_sub,←Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (inv_nonneg.mpr kp.le)]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (inv_nonneg.mpr kp.le)).trans
  apply (mul_le_mul_of_nonneg_left ((Finset.sum_le_sum (fun t _=>one t)).trans geo) (inv_nonneg.mpr kp.le)).trans_eq
  change K⁻¹*(K* _)=_;rw [inv_mul_cancel_left₀ kp.ne']
  dsimp only [c,atomCash];rw [pow_succ (2:ℝ) (k+1)];ring

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
