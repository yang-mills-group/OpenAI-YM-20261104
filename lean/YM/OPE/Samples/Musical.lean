import YM.OPE.Samples.Chairs
/-! # Small simultaneous snap along contours. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Trunk
open Function Filter MeasureTheory Lattice RG Wilson Polar Rhythm MergeProof Ribbons Finset
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C: Family G}{I L J:Type}[Fintype I][DecidableEq I]{i j k:I}{Q:Rhythm I} {H t u v w n A:ℕ} {f:Filter L} {X:L→ I→E4}
    {T:L→ℝ}{R r s: L→ℕ→ℝ} {α:ℕ→ℝ}{q e a b : L→ℝ}{M η:ℝ} {Y:L→ I→ E4}
set_option quotPrecheck false
local notation "μ"=> C.S.a
local notation "σ"=> (fun i=> C.path.levels.budget i)
local notation "U"=> Q.localTime H
variable {B: Border f T Q.limit R r α}{D:L→Loom Q}{P:ℝ} (h:Oscars B P D C)
namespace Oscars
local notation "K!"=> (fun i t=> (D i).launch t)
local notation "grid!"=> C.S.gridPoint
local notation "F!"=> Border.orbit Q H T r X
local notation "ρ!"=> (↑(Cloud.count I {0}):ℝ)
local notation "Γc"=> Cloud.grid {(0:E4)}
-- exact distance tolerance
private lemma provision_w {r v m n K u:ℝ}(hv:0 < u)(hm:0 ≤ m)(hn:2 ≤ n)(he:8*K*Real.exp 4*Real.exp 4 ≤ m)(hu: v*m ≤ n)(hy: 0 < v)(hp:1≤ K)(hr:0<r)(h:u ≤ r/n^32) : (n/r)*(u*v) ≤ (2* freeZone (n^2) K)⁻¹ :=by
    let z:=8*K*Real.exp 4*Real.exp 4; have hv':0< z:= by unfold z; have hK:0<K:= zero_lt_one.trans_le hp; positivity
    have hN:0<n:=zero_lt_two.trans_le hn
    have hZ: 2*freeZone (n^2) K= z*n^4:=by unfold z freeZone; ring
    rw [hZ]; refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h hy.le) (div_pos hN hr|>.le)).trans ?_
    have hv2:v*z ≤ n:= (mul_le_mul_of_nonneg_left he hy.le).trans hu; have he' : n*n^4*n ≤ n^32:=by rw [show n*n^4*n=n^6 by ring]; exact pow_le_pow_right₀ (one_le_two.trans hn) (by norm_num)
    field_simp; exact hv2.trans ((pow_one n).symm.trans_le (pow_le_pow_right₀ (one_le_two.trans hn) (by norm_num)))
private lemma snapBudget (i:ℕ)(z:I→ E4)(j:I): ‖grid! i (Γc (μ i) z (fun _ _=>0) j)- z j‖ ≤ μ i*(2*ρ!) :=by
    let v:= ρ!; have hp:0<v:= Int.cast_pos.mpr (Cloud.count_pos (I:=I) {(0:E4)}); let t:= μ i; let g:= grid! i (Γc t z (fun _ _=>0) j)-z j; have ht:0<t:=C.S.a_pos _
    have hu : ‖g‖^2 ≤ 4*(t*v)^2:=by
       rw [EuclideanSpace.real_norm_sq_eq]; apply le_trans (Finset.sum_le_sum (g:=fun _ :Axis=> (t*v)^2) (fun k _=>?_ )); simp
       rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Cloud.close_zero {(0:E4)} t ht z j k) _
    change ‖g‖≤t* (2*v); nlinarith only [hu, mul_pos ht hp]
include h
lemma snaps (hh:H ≤ Q.age Q.star){K:ℝ}(hK:1 ≤ K)(v:L→ I→ E4)(ht:∀ᶠ i in f,‖v i‖ ≤1/2) : ∃ y:L→ I→E4,∃ W:L→ I→ Cover, ∀ᶠ i in f,‖y i-v i‖ ≤ (2* freeZone (T i^2) K)⁻¹ ∧ ‖y i‖ ≤ 1 ∧ Seated Q C (D i) (F! i (y i)) H ∧ grid! (K! i Q.limit) ∘ W i= F! i (y i):=by
    let x i:=Border.orbit Q H T r X i (v i); let F i:=Q.stroke H (x i); let V i t:= Γc (μ (K! i t)) (F i) (fun _ _=>0); let p i j:= grid! (K! i (U j)) (V i (U j) j); let u':=2*ρ!; let D':=8*K*Real.exp 4*Real.exp 4; have hu:0 < u':= mul_pos two_pos (Int.cast_pos.mpr (Cloud.count_pos (I:=I) {0})); have hP:0 ≤ D':=(by unfold D'; have hK:0<K:= zero_lt_one.trans_le hK; positivity)
    let W i j:= F! i j; let η' i j:= T i /r i (U j); let y i j:= v i j+η' i j • (p i j-F i j); let X' i:= W i (y i)
    let Λ i:=grid! (K! i Q.limit); have he : ∀ᶠ i in f, ‖y i-v i‖ ≤ (2*freeZone (T i^2) K)⁻¹ ∧ ‖y i‖ ≤ 1 ∧ Seated Q C (D i) (X' i) H:=by
        have hp j:= (Q.timeBirth hh j).trans (Q.bounded j); filter_upwards [B.life.eventually_ge_atTop (u'*D'), B.life.eventually_ge_atTop 2,ht,eventually_all.mpr (fun j:I=> ((h.meter _ (hp j))).and ((B.rates _ (hp j)).pos))] with i hG hi hv hu'
        let v₀:=(2*freeZone (T i^2) K); have hy:2 ≤ v₀:=by
           have hz:= minBound (n:=T i^2) (one_le_pow₀ (one_le_two.trans hi)) hK; unfold v₀; nlinarith only [hz,hi]
        have hw : ‖y i-v i‖ ≤ v₀⁻¹:= by
           apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr (zero_le_two.trans hy))).mpr; intro j; rw [Pi.sub_apply]; unfold y; rw [add_sub_cancel_left,norm_smul,Real.norm_of_nonneg (div_pos (zero_lt_two.trans_le hi) (hu' j).2|>.le)]; exact (mul_le_mul_of_nonneg_left (snapBudget ..) (div_pos (zero_lt_two.trans_le hi) (hu' j).2|>.le)).trans (provision_w (C.S.a_pos _) hP hi le_rfl hG hu hK (hu' j|>.2) (hu' j|>.1.le))
        have hX(j) : Q.stroke H (X' i) j=p i j:=by
            unfold X' W Border.orbit -- notation expansion not at rw
            rw [Q.stroke_move hh]; have hF:F i j=Q.stroke H (X i) j +Border.pitches Q H T r i (v i) j:= Q.stroke_move hh ..; rw [show Border.pitches Q H T r i (y i) j=Border.pitches Q H T r i (v i) j+(p i j-F i j) from ?_,←add_assoc,← hF]; abel
            -- separate proof
            unfold Border.pitches y; rw [smul_add,smul_smul, show r i (U j) / T i * (η' i j)=1 from (by have he:=hu' j|>.2; have hp:0<T i:=zero_lt_two.trans_le hi; unfold η'; field_simp), one_smul]
        refine ⟨hw,?_,⟨fun j=> by rw [hX j]; exact ⟨_,rfl⟩,fun j a=> ?_,fun j k hj he d=>?_⟩⟩
        · have hy : v₀⁻¹ ≤ 1/2:=by rw [← one_div]; exact div_le_div_of_nonneg_left zero_le_one two_pos hy
          linarith only [hw,hy,hv,norm_sub_norm_le (y i) (v i)]
        · rw [hX]; exact Cloud.clears _ _ (C.S.a_pos _) _ _ _ _ 0 (mem_singleton_self _)
        rw [hX,hX]; unfold p; rw [he]; exact fun h=> hj (Cloud.screened _ _ (C.S.a_pos _) _ (fun _ _=>0) d h)
    let Y i:= if h':Seated Q C (D i) (X' i) H then fun j=> Classical.choose ((h'.provenance hh j).inh ((D i).mono Q ((Q.timeBirth hh j).trans (Q.bounded j)) le_rfl)) else 0
    refine ⟨y,Y,?_⟩; filter_upwards [he] with i hi; refine ⟨hi.1,hi.2.1,hi.2.2,funext fun j=> ?_⟩; unfold Y; rw [dif_pos hi.2.2]; exact ( (hi.2.2.provenance hh j).inh ((D i).mono Q ((Q.timeBirth hh j).trans (Q.bounded j)) le_rfl)).choose_spec
end Oscars
end YM.OPE.Log.Trunk
