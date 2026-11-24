import YM.RG17.Corners

/-!
 Counts at actual positions, per root and costed root SUM.
 May group at b different from working m as dictated by local-cost
 producer, no cost here for a_b ≪ r or a_b ≫ r except explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Extraction Spec Table OPE Lattice Push.AbsoluteSums.Animals Filter Set Function Next.Rank
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G){n b N p:ℕ}{S:Table C.book}{f:Extraction.Order}

variable (F:Final C f S)(T:Test 1)(K:Set (Points (n+1)))

def yarns (b N p:ℕ)(h:b ≤ N)(z:Site (C.side b p)) (r:ℝ) := Finset.univ.filter (fun u:Fin (n+1)→Site (C.side N p)=>
    Order.cells C N p u ∈ gathersIn C F T K r ∧ (C.S.toDepth h p).parent (u 0)=z)

def spools (b N p:ℕ)(h:b≤ N)(r:ℝ):= Finset.univ.filter (fun z:Site (C.side b p)=> (yarns C F T K b N p h z r).Nonempty)

variable {C F T K}
private lemma ceilCost {b t:ℝ}(hb:0 ≤ b)(ht:0<t):
    t^4 * (↑(ballCost (⌈b/t⌉₊)) : ℝ) ≤ (2*b+3*t)^4 := by
    have h : ((⌈b/t⌉₊:ℕ) : ℝ) * t ≤ (b/t+1)*t:= mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (by positivity)).le ht.le
    rw [add_mul,div_mul_cancel₀ _ ht.ne',one_mul] at h
    simp only [ballCost,Nat.cast_pow,Nat.cast_add,Nat.cast_one,← mul_pow]; apply pow_le_pow_left₀ (by positivity); linarith
private lemma cart {α: Type*} [Fintype α][DecidableEq α] (U:Finset α) : (Finset.univ.filter (fun x:Fin n→α=>∀ i,x i ∈ U)).card = U.card^n:=by
    let V:= (Finset.univ.filter (fun x: Fin n→α=>∀ i,x i∈ U))
    let f : V ≃ (Fin n→ ↥U) := {
      toFun := fun x i=> ⟨x.val i, (Finset.mem_filter.mp x.2).2 i⟩
      invFun:= fun x=>⟨fun i=> x i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i=>(x i).2⟩⟩
      left_inv:= fun _=>rfl
      right_inv:= fun _=>rfl}
    rw [← Fintype.card_coe, Fintype.card_congr f,Fintype.card_fun]; simp
private lemma mill {U:Finset (Fin (n+1)→Site (C.side N p))}{h:b≤ N}(z:Site (C.side b p)){Z:ℕ}
    (hu:∀u∈U, (C.S.toDepth h p).parent (u 0)=z)
    (hh:∀u∈U,∀ i,separation (u 0) (u i) ≤ Z) : U.card ≤ (C.S.toDepth h p).count.val^4 * (ballCost Z)^n:=by
    let g:=C.S.toDepth h p
    let y(v:Site g.count):= g.assemble (z,v)
    let Q(v):=neighbors Z (y v)
    let S(v:Site g.count):= (Finset.univ.filter (fun x:Fin n→Site (C.side N p)=> ∀ i, x i∈Q v)).image (Fin.cons (α:=fun _=> Site (C.side N p)) (y v))
    have hp : U ⊆ Finset.univ.biUnion S:=by
       intro u h1; let v:=g.residue (u 0)
       have he: y v=u 0:=by unfold y; rw [← hu u h1]; exact g.unpack_at (u 0)
       refine Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _, Finset.mem_image.mpr ⟨(fun i=> u i.succ), Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i=> (neighbors_mem Z _ _).mpr (by simpa only [he] using hh u h1 i.succ) ⟩,?_⟩⟩
       funext i; cases i using Fin.cases <;> simp [he]
    apply (Finset.card_le_card hp).trans (Finset.card_biUnion_le.trans (le_trans (b:=∑ _v:Site g.count,(ballCost Z)^n) ?_ ?_)); swap
    · simp only [Finset.sum_const,Finset.card_univ,site_card,nsmul_eq_mul, g,Nat.cast_id]; rfl -- check
    apply Finset.sum_le_sum; intro v _; unfold S; apply Finset.card_image_le.trans; rw [cart]; exact Nat.pow_le_pow_left (neighbors_card Z (y v)) _

private lemma coarse {h:b≤ N}{μ:ℝ}{x:Site (C.side N p)}(hp:‖C.S.place x‖ ≤ μ) :
    C.S.a b * separation 0 ((C.S.toDepth h p).parent x) ≤ μ+C.S.a b:=by
   let g:= C.S.toDepth h p; let w:=g.count.val; let y:=g.parent x
   have ht:= C.S.embeds_scale g
   have hz : separation (g.embed y) 0=w*separation y 0:= by
       apply Eq.trans (congr_arg (separation (g.embed y)) (show (0:Site (C.side N p)) = g.embed 0 from g.root.map_zero.symm)); exact Station.both ..
   have hx : separation x (g.embed y) ≤ w:=by have h : 2*separation x (g.embed y) < w:=Station.midway g (C.S.toDepth_odd h _) _ ; omega
   have hv:= (separation_triangle (g.embed y) x 0); rw [hz,separation_comm (g.embed y) _] at hv
   have h' : (↑(w*separation y 0) : ℝ) ≤ ((w+separation x 0:ℕ):ℝ):=by exact_mod_cast (show _ from hv.trans (Nat.add_le_add_right hx _))
   push_cast at h'
   have hb:= (MergeProof.Ribbons.normC C N p x).1.trans hp
   rw [separation_comm,← ht,mul_assoc]; refine (mul_le_mul_of_nonneg_left h' (C.S.a_pos _).le).trans ?_; rw [mul_add]; linarith
variable (C F T K)
set_option maxHeartbeats 350000 in
theorem countableBill (hp:IsCompact K)(hh:K⊆conf _):∃ c d ν υ η:ℝ, 0≤c∧0≤d∧0 ≤ ν ∧ 0<υ ∧ 0<η ∧
    ∀ᶠ r in home,∀ (b N p:ℕ)(h:b≤ N), C.S.a N ≤ r →
       C.S.a b ^4 * (spools C F T K b N p h r).card ≤ c ∧
       ∀ z, let U:= yarns C F T K b N p h z r
            C.S.a N^(4*(n+1))*U.card ≤ d*C.S.a b^4 * r^(4*n) ∧
               ∀ u∈U, (∀ i,‖C.S.place (u i)‖≤ν) ∧ (∀ i j,C.S.a N*separation (u i) (u j) ≤ υ*r) ∧
                       (∀ i j,i≠j → η*r ≤ 2*C.S.a N *separation (u i) (u j)):=by
    obtain ⟨ν,υ,η,hv,hy,hη,he⟩:=stencilSpace C F T K hp hh
    refine ⟨(2*ν+5)^4, (2*υ+3)^(4*n),ν,υ,η,by positivity,by positivity,hv,hy,hη,?_⟩
    filter_upwards [he,positiveLength] with r hr hR b N p h hx
    let m:= C.S.a b; let k:= C.S.a N; have hk:0<k:= C.S.a_pos _; have hm:0 < m:= C.S.a_pos _
    let g:= C.S.toDepth h p
    have hz(z) u (hu:u∈yarns C F T K b N p h z r):= Finset.mem_filter.mp hu
    let Z:=⌈(ν+m)/m⌉₊; let X:= spools C F T K b N p h r
    have hi : X ⊆ neighbors Z 0:=by
       intro z hh; obtain ⟨u,hu⟩:= (Finset.mem_filter.mp hh).2; have hh:= (hz z u hu).2
       apply (neighbors_mem ..).mpr; apply (Nat.cast_le (α:=ℝ)).mp (le_trans ?_ (Nat.le_ceil _)); rw [le_div_iff₀ hm,mul_comm, ← hh.2]; exact coarse (C:=C) ((hr N p u hh.1).1 0)
    have h'Z:(X.card:ℝ) ≤ (ballCost Z:ℝ):=by exact_mod_cast (Finset.card_le_card hi).trans (neighbors_card ..)
    constructor
    · have hU:m ≤ 1:= by simpa [m] using C.S.strictAnti.antitone (show 0≤ b from Nat.zero_le _)
      refine le_trans (mul_le_mul_of_nonneg_left h'Z (by positivity)) ((ceilCost (add_nonneg hv hm.le) hm).trans ?_); apply pow_le_pow_left₀ (by positivity); linarith
    intro z; let U:=yarns C F T K b N p h z r; let J:=⌈υ*r/k⌉₊
    refine ⟨?_,fun u hu=> hr N p u (hz _ _ hu).2.1⟩
    have hh : U.card ≤ g.count.val^4 * (ballCost J)^n:=by
        apply mill z (fun u hu=>(hz _ _ hu).2.2); intro u hu i; have hb:= (hr N p u (hz _ _ hu).2.1).2.1 0 i
        apply (Nat.cast_le (α:=ℝ)).mp (le_trans ?_ (Nat.le_ceil _)); apply (le_div_iff₀ hk).mpr; rwa [mul_comm]
    have ht : k^4*(ballCost J:ℝ) ≤ ((2*υ+3)*r)^4:=by refine (ceilCost (by positivity) hk).trans ?_; apply pow_le_pow_left₀ (by positivity); linarith [show k≤ r from hx]
    have hS : k*(g.count.val:ℝ)=m:= C.S.embeds_scale _
    refine le_trans (mul_le_mul_of_nonneg_left (show (U.card:ℝ) ≤ (↑g.count.val:ℝ)^4 * (ballCost J:ℝ)^n from by exact_mod_cast hh) (pow_nonneg hk.le _)) ?_
    change k^(4*(n+1))*_ ≤ (2*υ+3)^(4*n)*m^4*r^(4*n); apply le_trans (b:=m^4*(((2*υ+3)*r)^4)^n) ?_ (le_of_eq (by rw [← pow_mul,mul_pow]; ring))
    apply le_trans (b:=m^4*(k^4*(ballCost J:ℝ))^n) (le_of_eq (by rw [← hS]; ring)); exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht _) (by positivity)
end YM.RG17
