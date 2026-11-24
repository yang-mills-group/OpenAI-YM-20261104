import YM.OPE.Compatible.Harks.Sycam
/-!
# layers of paid small initial/correction directions
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F] {r x b c t q:ℝ}
variable {a f:ℕ→ E}{g:ℕ→ F}{p:ℕ→ E→L[ℝ] E}
variable {d k:ℕ}{G:ℕ→Type}[∀ i,NormedAddCommGroup (G i)][∀ i,NormedSpace ℝ (G i)]
variable {μ:ℕ→ℝ}{T:Cuts d μ t x E G}
variable [∀ i,CompleteSpace (G i)][CompleteSpace E]
variable (T) {R:E→L[ℝ] E}
local notation "X!" => Ux R (μ k)
lemma enValve (h:Grooved T R)(hk:k<d)(hb:ShadeR T (k+1) r) (p:E)(hp:p∈T.flag (k+1)):∃ u∈T.flag (k+1),X! u = p:=by
    obtain ⟨b,H,b'⟩:=even T hb.Fast hb.ex (k+1) (by omega) hb.brisk; let A:= tale R p; have hA:Run (Ford R) A 0:=TALE R p; let u(i:ℕ):=(μ k)⁻¹^(i+1) • A i; let T':= ∑' i:ℕ,u i; have hy:= T.fast.trans hb.Fast.le; have hz:=T.tempo k hk; have hx:0 ≤ r/(μ k):=div_nonneg hy hz.le
    have hh:Summable u:=by
        have hp':Hex r A (b*‖p‖):= b' (Ford R) (fun _=>h) A hA hp; let x:= b*‖p‖*(μ k)⁻¹; refine Summable.of_norm (show Summable (fun i:ℕ=> ‖u i‖) from ?_)
        refine (Summable.of_nonneg_of_le (fun i=> norm_nonneg (u i)) ?_ ((summable_geometric_of_lt_one hx ((div_lt_one hz).2 (hb.slow _ (by omega)))).mul_left x)); intro i; unfold u; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity:0 ≤(μ k)⁻¹^(i+1))]; exact (mul_le_mul_of_nonneg_left (hp' i) (by positivity : 0 ≤ (μ k)⁻¹^(i+1))).trans_eq (show _ = x*(r/μ k)^i from by unfold x; rw [pow_succ,div_pow]; simp only [div_eq_mul_inv,inv_pow]; ring) -- invPow direction
    refine ⟨-T',?_ ,?_⟩
    · exact (T.flag _).neg_mem (tsum_mem (T.sealing (k+1) (by omega)) (fun i=>(T.flag _).smul_mem _ (Run.hero hA (fun _=> h) (by omega) hp i)))
    rw [shiftUx,map_neg,smul_neg]; have hv(i:ℕ):R (u i)=μ k • u (i+1):=by unfold u; rw [map_smul,hA,Pi.zero_apply,add_zero,smul_smul,pow_succ' _ (i+1),←mul_assoc,mul_inv_cancel₀ hz.ne',one_mul]
    have hu:R T'=μ k • (T'-u 0):=by
        unfold T'; rw [ContinuousLinearMap.map_tsum R hh]; simp_rw [hv]; rw [show (∑' i,u i)= _ from (show (∑' i,u i)=u 0+ ∑' j,u (j+1) from (hh.sum_add_tsum_nat_add 1).symm.trans (by simp))] -- fragile
        rw [add_sub_cancel_left]; exact tsum_const_smul'' ..
    rw [hu,smul_sub,show μ k • u 0=p from (by unfold u; erw [pow_one,smul_smul,mul_inv_cancel₀ hz.ne',one_smul]; rfl)]; abel
lemma liftLayer (h:Grooved T R)(hk:k<d)(hb:ShadeR T (k+1) r)(v:G k):∃ u∈ T.flag k, T.Tap k u=v ∧ X! u=0:=by
    let x:=T.lift k hk v; have hx:x∈T.flag k∧ T.Tap k x=v:=T.rises ..; obtain ⟨p,hp,ht⟩:=enValve T h hk hb (X! x) ((T.next _ hk _).mpr ⟨jumps_in h hk.le _ hx.1,by rw [TapJump h hk _ hx.1,sub_self,zero_smul]⟩); have hv:=(T.next k hk p).1 hp; refine ⟨x-p,(T.flag k).sub_mem hx.1 hv.1, ?_, by rw [map_sub,ht,sub_self]⟩; rw [map_sub,hx.2,hv.2,sub_zero]
lemma xen (h:Grooved T R)(hk:k<d)(hb:ShadeR T (k+1) r)(v:E):∃ z w:E,v=z+X! w∧ X! z=0:=by
    have ht(i:ℕ)(hh:i≤k):∀ v∈ T.flag i, ∃ w:E, v-X! w∈ T.flag k:=by
         induction hh using Nat.decreasingInduction with
         | self=>exact fun j hj=>⟨0,by rw [map_zero,sub_zero];exact hj⟩
         | of_succ n hN ih=>
            intro p hp; let v:= (μ n-μ k)⁻¹ • T.Tap n p; let w:=T.lift n (by omega) v; have hv:w∈T.flag n∧ T.Tap n w =v:=T.rises ..; have hh:= jumps_in (q:=μ k) h (by omega) w hv.1; have hx: p-X! w∈ T.flag (n+1):=by apply (T.next _ (by omega) _).mpr; refine ⟨(T.flag _).sub_mem hp hh,?_⟩; rw [map_sub, TapJump h (by omega) w hv.1,hv.2,show (μ n-μ k) • v= _ from (show (μ n-μ k) • v=T.Tap n p from by unfold v; rw [smul_smul,mul_inv_cancel₀ (sub_ne_zero.mpr (T.beats n k hN hk).ne'),one_smul]),sub_self]
            obtain ⟨t,H⟩:=ih _ hx; refine ⟨w+t,?_⟩; rw [map_add,←sub_sub]; exact H
    obtain ⟨w,Hw⟩:= ht 0 (by omega) v (T.first _); obtain ⟨z,H,ht,hz⟩:=liftLayer T h hk hb (T.Tap k _); obtain ⟨y,hy,hK⟩:=enValve T h hk hb (v-X! w-z) ((T.next _ hk _).mpr ⟨(T.flag _).sub_mem Hw H,(by rw [map_sub,ht,sub_self])⟩); exact ⟨z,w+y,(by rw [map_add,hK]; abel),hz⟩
lemma xDeep (h:Grooved T R)(hk:k<d)(hb:ShadeR T (k+1) r)(v:E)(n:ℕ):∃ z w:E,v=z+(X!^n) w∧ X! z=0:=by
    induction n with
    | zero=> exact ⟨0,v,(by simp), map_zero _⟩
    | succ n ih=>
         obtain ⟨z,w,rfl,hz⟩:= ih; obtain ⟨b,c,hb,hH⟩:=xen T h hk hb w; refine ⟨z+(X!^n) b,c,?_,?_⟩; rw [hb,map_add,← byway,pow_succ,add_assoc]; rw [map_add,hz,← byway,(Commute.self_pow X! n).eq,byway,hH,map_zero,add_zero]
end YM.OPE.Hark
