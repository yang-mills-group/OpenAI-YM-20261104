import YM.OPE.Compatible.Lake.Pointe
/-! Isolation lemma driving dichotomy. Price assumed only the EPS conclusion on same horizon! -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot ContinuousLinearMap
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}
variable {d:ℕ}{E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I" => Fin (d+1)
-- 
structure Road (C:Family G)(k D:ℕ)(P:ℕ→ Dock E ≃L[ℂ] Dock E):Prop where
    ratios j : k ≤ j→ ∃ U u η, Split (extent C j) η u (P j) U ∧ 16 ≤ extent C j ∧ 1 ≤ η ∧ η≤ 3/2∧u ≤ ice d∧ price d η u≤ Real.exp ((D:ℝ)*levy C j)
namespace Road
variable {k D e:ℕ}{P:ℕ→ Dock E≃L[ℂ] Dock E}{p:ℕ→ Dock E→L[ℂ]ℂ}
variable (R:Road C k D P) (h:∀ i:ℕ,k≤ i→ p (i+1)=(p i).comp (P i).toContinuousLinearMap) (hle:e ≤ d) (ht: RateLE atTop C.S.scale (fun i=>p i) (d-e:ℕ))
include h hle R
variable {i:ℕ}(hi:k ≤ i)
local notation "U" i:max=> courtyard (p i) e
local notation "Z" i:max=> shelf (p i) e
include hi
lemma above {m:ℕ}(hp: Z i < U i)(hm:i ≤ m): Z m < U m ∧ U i* Real.exp ((((d-e:ℕ):ℝ)+1/2)*(C.S.scale m-C.S.scale i)) ≤ U m:=by
   induction m,hm using Nat.le_induction with
   | base=>exact ⟨hp,by simp⟩
   | succ j hj ih=>
     obtain ⟨Y,v,a,g,hb,hg,hL,hM,_⟩:= R.ratios j (hi.trans hj); have he:= g.scrum hb hg hL hM (p j) hle ih.1; rw [← h j (hi.trans hj)] at he
     refine ⟨he.2, (le_trans ?_ he.1)⟩
     let x:=extent C j; have hx:0<x:=by dsimp only [x]; linarith
     let t:ℝ:= ((d-e:ℕ):ℝ)+1/2
     have hβ: Real.exp (t*Real.log x)= x^(d-e)*Real.sqrt x:=by unfold t; rw [add_mul,Real.exp_add,← Real.log_pow,Real.exp_log (pow_pos hx _), Real.sqrt_eq_rpow,Real.rpow_def_of_pos hx]; ring_nf
     have hh :t*(C.S.scale (j+1)-C.S.scale i)=t*(C.S.scale j-C.S.scale i)+t*Real.log x:=by rw [Schedule.scale_succ]; change t*((_+Real.log x)-_) = _;ring
     change U i*Real.exp (t*_) ≤ _; rw [hh, Real.exp_add,hβ,← mul_assoc]; exact mul_le_mul_of_nonneg_right ih.2 (show 0 ≤ x^(d-e)*Real.sqrt x by positivity)
include ht
lemma rests : U i ≤ Z i:=by
   by_contra! hv
   have hg:0< U i:= lt_of_le_of_lt (Finset.sum_nonneg (fun _ _=> norm_nonneg _)) hv
   let qqX (m):= U m
   let a:ℝ:= ((d-e:ℕ):ℝ)+1/2
   let F:= U i * Real.exp (-a*C.S.scale i); have hF:0<F:=mul_pos hg (Real.exp_pos _)
   let u(m) := F*Real.exp (a*C.S.scale m)
   have hT: RateLE atTop C.S.scale qqX (d-e:ℕ):=by
      have hu:= ht.norm
      have h:RateLE atTop C.S.scale (fun i=> ((d+1:ℕ):ℝ)*‖p i‖) (d-e:ℕ):=by simpa only [zero_add] using (RateLE.const ((d+1:ℕ):ℝ) C.S.divergent).mul hu
      apply h.transfer (Eventually.of_forall fun j=>?_); rw [Real.norm_of_nonneg (show 0≤ qqX j from Finset.sum_nonneg (fun _ _=> norm_nonneg _))]
      exact ((Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _=> norm_nonneg _)).trans (boardRowTicket (p j))).trans (Real.le_norm_self _)
   have hW:RateIs atTop C.S.scale (fun i=>(1/2:ℝ)*u i) a:=by simpa only [zero_add] using (RateIs.const C.S.divergent (by norm_num: (0:ℝ)<1/2)).mul ((RateIs.const C.S.divergent hF).mul (RateIs.exp a C.S.divergent))
   obtain ⟨m,hm,hq⟩:= ((eventually_ge_atTop i).and (hW.outweigh hT (by unfold a; linarith) C.S.divergent)).exists
   have heq : u m ≤ U m:=by
       apply le_trans _ (R.above h hle hi hv hm).2; unfold u F; change _ ≤ U i * Real.exp (a*_); rw [mul_assoc,← Real.exp_add]; ring_nf; exact le_rfl
   have hx:=Real.le_norm_self (qqX m); have hZ:0< u m:=mul_pos hF (Real.exp_pos _); linarith only [hZ,hq,hx,heq]
lemma highBill : shelf (p i) e * C.S.a i^(d-e) * β C k ^ D ≤ shelf (p k) e * C.S.a k^(d-e) * β C i ^ D:=by
   induction i,hi using Nat.le_induction with
   | base=>rfl
   | succ j hj ih=>
     obtain ⟨Y,u,a,g,hb,hg,hL,hM,hV⟩:= R.ratios j hj
     let n:= d-e; let x:=extent C j; have hx:0<x:=by unfold x;linarith
     let b:= Real.exp ((D:ℝ)*levy C j); have hh: β C (j+1)^D=b*β C j^D:= reap D j
     have hs:= g.spikes hb hg e _ (R.rests h hle ht hj); rw [← h j hj] at hs
     have hu: 0 ≤ Z j:=Finset.sum_nonneg (fun _ _=>norm_nonneg _); have heq: x^n * C.S.a (j+1)^n=C.S.a j^n:= by rw [← mul_pow, Schedule.a_step]; congr 1; field_simp; exact mul_comm .. 
     have hs' :Z (j+1) ≤ Z j*(x^n*b):= hs.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hV (pow_nonneg hx.le n)) hu)
     have hi := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs' (pow_nonneg (C.S.a_pos (j+1)).le n)) (pow_nonneg (β_pos C k).le D)
     apply hi.trans; rw [hh]; have hh:= Real.exp_pos ((D:ℝ)*levy C j)
     change _ ≤ _; calc
       _ = b*(Z j*C.S.a j ^ n*β C k ^ D):=by rw [← heq]; ring
       _ ≤ b*(Z k*C.S.a k ^ n*β C j ^ D):=mul_le_mul_of_nonneg_left ih hh.le
       _ = _:=by unfold n; ring
omit h hle ht
lemma flight (v:ℕ→Dock E) (hv:∀ j:ℕ,k ≤ j→ v (j+1)=(P j).symm (v j)): berth (v i)*β C k^D ≤ berth (v k)* β C i^D:=by
   induction i,hi using Nat.le_induction with
   | base=>rfl
   | succ j hj ih=>
     obtain ⟨Y,u,a,g,hb,hg,hL,hM,hV⟩:= R.ratios j hj
     have he:0≤ berth (v j):=Finset.sum_nonneg (fun _ _=> norm_nonneg _); have hn:= (g.purchases hb hg (v j)).trans (mul_le_mul_of_nonneg_left hV he); rw [← hv j hj] at hn
     let b:= Real.exp ((D:ℝ)*levy C j); rw [reap D j]; have hk:0≤ β C k^D:=pow_nonneg (β_pos C k).le _; linarith only [mul_le_mul_of_nonneg_right hn hk,mul_le_mul_of_nonneg_left ih (show 0≤ b from (Real.exp_pos _).le)] -- b
end Road
end YM.OPE.Lake
