import YM.RG11Proof.Rigidity.Ice.Frost

/-!
# Arbitrary engineering horizon frozen test on the Maxwell quotient

Reality + signed-coordinate equivariance are essential; also this proves NO
contact rank where Wick formulas before restriction need not descend. POSITIONS
are unregulated physical quotient's ones.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Labels Maxwell Function Extra.FD Reads Maxwell.Free Set Filter Pert.Position Gauge Pert
open scoped Classical BigOperators Topology ContDiff ComplexOrder
variable {G:Gauge}{F:Frames G}{d:ℕ}

local notation "K"=> PertExtension.Rigidity.Positive.gramC

private lemma visible₂ (p q:E F d)(x:Points 2): (freeTable F).useAt (freeTable F) x ![⟨d,p⟩,⟨d,q⟩]=visible F d x ![p,q]:=by
  have ht : visible F d x ![p,q]= (freeTable F).useAt (freeTable F) x (fun i=> (Sigma.mk d (![p,q] i):(freeTable F).Tag)):=rfl
  rw [ht]; apply congrArg ((freeTable F).useAt (freeTable F) x); funext i; fin_cases i <;> rfl
lemma Frigid.skew {b:Buffer F d}(h:Frigid b)(p q:E F d):
    K F (hierarchy F) 0 p (b.val q)+K F (hierarchy F) 0 (b.val p) q=0:=by
  let x := Extra.FD.couple (_root_.YM.basis 0) (0:E4)
  let a:=(freeTable F).adj (table_spin F) d 0
  have hv : x∈ conf 2 := Extra.FD.couple_ok (by intro ho; simpa [YM.basis_norm] using! congr_arg norm ho)
  have ha : a (b.val p)=b.val (a p):=by
    change Rigid.wear F d (Signed.mirror 0) ((freeTable F).conj (table_spin F) d (b.val p)) = _
    rw [Rigid.wear_ride,b.property.2.2.1,b.property.2.2.2.1 (Signed.mirror 0)]; congr 1
    change rideO F _ d _ = Rigid.wear F d (Signed.mirror 0) _; rw [Rigid.wear_ride]
  have H:= h 2 ![q,a p] x hv; rw [Fin.sum_univ_two] at H
  simp_rw [PertExtension.Rigidity.Positive.gramC_apply,visible₂]; rw [← H]
  change visible F d x ![_,a p]+visible F d x ![q,a (b.val p)]=_
  rw [ha]; congr 2 <;> { ext1 i; fin_cases i <;> simp }


private lemma shrinking {b:Buffer F d}(h:Frigid b)(hG:G.Simple)(hd : 4<d)(B:Adapted F d) (i : B.toBasis.J) :
    ∀ j:B.toBasis.J,(B.w i).1 ≤ (B.w j).1 → B.b.equivFun (b.val (B.b i)) j=0 := by
  let n:= (B.w i).1
  intro j hJ
  have ht : b.val (B.b i)∈ lower F n d:= by
    obtain H|H:=eq_or_lt_of_le (B.heights i)
    · rw [show n=d from H]; apply top_step
    exact b.property.2.1 n H _ (stairs B i le_rfl)
  rcases eq_or_lt_of_le hJ with hN|hS; swap; exact small_read B j hS _ ht
  let U : News F d:=⟨n,B.heights i,B.b i,B.pinned i,stairs B i le_rfl,web_grains B i⟩
  let z:= b.val (B.b i)
  obtain he : Reads.top n (writes F d z)=0 := h.top_zero hG hd U
  rw [← B.b.sum_equivFun z, map_sum,map_sum] at he
  have hr (a:B.toBasis.J):
    Reads.top n (writes F d (B.b.equivFun z a • B.b a))=
      writes F d (if (B.w a).1=n then B.b.equivFun z a • B.b a else 0):=by
    have ht:=web_grains B a
    split_ifs with hk
    · rw [map_smul,map_smul,←hk,MvPolynomial.weightedHomogeneousComponent_eq_self ht]
    rw [map_zero,map_smul,map_smul,show Reads.top n (writes F d (B.b a))=0 from MvPolynomial.weightedHomogeneousComponent_eq_zero' _ _ (fun c hc=>by rw [ht (MvPolynomial.mem_support_iff.mp hc)]; exact hk),smul_zero]
  simp_rw [hr,←_root_.map_sum] at he -- map_zero everywhere! 
  have hp := congr_fun (congr_arg B.b.equivFun ((map_eq_zero_iff _ (writes_inj F d)).mp he)) j
  rw [_root_.map_sum,map_zero,Finset.sum_apply,Finset.sum_eq_single j] at hp
  · rw [if_pos (show _=n from hN.symm),map_smul, Pi.smul_apply, Module.Basis.equivFun_self] at hp
    simpa using hp
  · intro a _ hj; split_ifs
    · rw [map_smul, Pi.smul_apply, Module.Basis.equivFun_self]; simp [hj]
    rw [map_zero]; rfl
  · exact fun hj=> (hj (Finset.mem_univ _)).elim


lemma Frigid.clear {b:Buffer F d}(h:Frigid b)(hG:G.Simple)(hd : 4<d) : b=0:=by
  let B:=tower F d
  let n (i:B.toBasis.J):= (B.w i).1
  have ht (r) (i:B.toBasis.J) (hi:n i=r): b.val (B.b i)=0:= by
    induction r using Nat.strong_induction_on generalizing i with
    | h k ih=>
      let v:=B.b i
      have hp: b.val (b.val v)=0:=by
        nth_rw 1 [← B.b.sum_equivFun (b.val v)]; rw [map_sum]; apply Finset.sum_eq_zero; intro j _
        rw [Rigid.dispatch_cmul]; rcases lt_or_ge (n j) (n i) with he| he
        · rw [ih (n j) (he.trans_eq hi) _ rfl,smul_zero]
        rw [show B.b.equivFun (b.val v) j=0 from shrinking h hG hd B _ _ he,zero_smul]
      by_contra H
      obtain hv := h.skew (b.val v) v
      have hU := PertExtension.Rigidity.Positive.gramC_pos F (hierarchy F) 0 (v:=b.val v) H
      rw [hp,map_zero,LinearMap.zero_apply,add_zero] at hv
      exact (ne_of_gt hU) hv
  apply Subtype.ext; apply ContinuousLinearMap.ext; intro x
  change b.val _=0; rw [←B.b.sum_equivFun x,map_sum]; simp_rw [Rigid.dispatch_cmul, fun i=> ht _ i rfl,smul_zero,Finset.sum_const_zero]

/-- Infinitesimal normalization nondegeneracy on the common real Maxwell-Wick space and
compatible with the tested finite-questionnaire interface. For every horizon,
even non-factorized complex smearing; Gram coerced back at one real gap. -/
theorem polar_rank (F : Frames G)(h : G.Simple)(d : ℕ): Frozen F d:= by
   rcases lt_trichotomy d 4 with hd|rfl|hd
   · exact Rigid.first_frozen F h hd
   · exact Rigid.frozen_four F h
   intro b (hb:Frigid b); exact hb.clear h hd
end YM.RG11.Rigidity.Ice
