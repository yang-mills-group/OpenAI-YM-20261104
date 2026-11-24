import YM.MSbar.Sage.Sailing
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V' :Config G n}{x: Site n}{R: Rep G n}{σ C T a v δ w β:ℝ}
open Finset RG.PathData
variable {Y X: Support n}{k M:ℕ}{p:BudgetPoint}(A:Activities G n) (j:Site n) (P: Support n)
open AnalyticBridge.VerifiedReset Next.Scheduling Precision
-- compare the regular exponent TOO (R.path including loops+activity). Cut contributions.
def deepCopy (p:BudgetPoint)(k:ℕ):= (4*p.B+2)*(k+100)
lemma shoots (Z : Support n) (a b : Site n) (ha : a∈inspected Z)(hb:b∈inspected Z) (B:BudgetPoint) : separation a b ≤ deepCopy B (coverNumber B.B Z):=by
    obtain ⟨x,hx,H⟩:=halo_spec.mp (Next.Scheduling.flag_layer _ ha); obtain ⟨z,hz,hH⟩:= halo_spec.mp (Next.Scheduling.flag_layer _ hb); have ht:= Corona.extent Z B.B hx hz; rw [separation_comm x] at H; refine (separation_triangle a x b).trans ((Nat.add_le_add H ((separation_triangle x z b).trans (Nat.add_le_add ht hH))).trans ?_); unfold deepCopy; ring_nf; omega
lemma masked_out (h:A.Valid p δ w) i W W' : Agrees (inspected (A.reg i).support) W W' → A.regularOccurrence p i W=A.regularOccurrence p i W':=by
    apply UsesFinal.allReads
    rintro U V hx hp; have he:Healthy p.threshold (A.reg i).support U ↔ Healthy p.threshold (A.reg i).support V:=by unfold Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty,hp];
    by_cases hh:Healthy p.threshold (A.reg i).support U
    · rw [Activities.regularOccurrence,masked_eq _ _ _ _ hh,masked_eq _ _ _ _ (he.mp hh),(h.regular.smooth i).sites U V hx]
    rw [Activities.regularOccurrence,masked_ne _ _ _ _ hh,masked_ne _ _ _ _ (he.not.mp hh)]
def merino (p:BudgetPoint)(δ:ℝ)(Y n:ℕ) :=
      let d:=4*p.B+2; let a:=p.supportExponent/2
      (4*Real.exp (100*a)*Real.exp (-a*n))*Y*((2*(d:ℝ)+1)^4*meter a)*δ

lemma wool (h:A.Valid p δ w)(f:Place Y M U U' V V' p.threshold)(hp:deepCopy p k ≤ M) : |(A.additive p U-A.additive p V)-(A.additive p U'-A.additive p V')| ≤ merino p δ Y.card k :=by
    let d:=4*p.B+2; let a:=p.supportExponent/2; have hA:0 < a:= half_pos p.exponent_pos; have hd:0<d:=by dsimp only [d]; omega
    obtain ⟨b,hb,hP⟩:= h.boundE; let F i U:= A.regularOccurrence p i U; let g i:= (F i U-F i V)-(F i U'-F i V'); let m(j:Site n):=∑ i∈Y,Heath.wick d a i j
    let t:= 4*Real.exp (100*a)*Real.exp (-a*k); have hT:0≤ t:=by unfold t; positivity
    let u(j:Site n):= m j*t; have hu(j:Site n):0 ≤ u j:= by unfold u; apply mul_nonneg _ hT; exact sum_nonneg fun _ _=> (Real.exp_pos _).le
    let r(j:Site n)(i:ℕ):= u j*(if (A.reg i).site=j then p.mass (A.reg i).support (b i) else 0); have hh:= budget_over Finset.univ r (fun j=> u j*δ) (fun j _=> budget_scale (hu j) (hP j)); have hK(i)(V): |F i V|≤ b i:=by
        unfold F Activities.regularOccurrence; by_cases he: Healthy p.threshold (A.reg i).support V
        · exact (congr_arg abs (masked_eq _ _ _ _ he)).trans_le ((hb i).2 _ he [] (Nat.zero_le _) (by simp))
        rw [masked_ne _ _ _ _ he,abs_zero]; exact (hb i).1
    have he(i): |g i| ≤ ∑ j,r j i:=by
        by_cases h₀:g i=0; rw [h₀,abs_zero]; exact hh.1 _
        let P:= A.reg i; let W:=P.support; let S:=inspected W; let c:=coverNumber p.B W
        by_cases hx:Disjoint S Y
        · refine (h₀ ?_).elim; unfold g F; rw [masked_out A h i _ _ (f.old _ hx),masked_out A h i _ _ (f.afterX _ hx)]; abel
        obtain ⟨x,hx,hX⟩:=Finset.not_disjoint_iff.mp hx
        have hp' : k ≤ c:=by
          by_contra hb; refine h₀ ?_
          have hg : S⊆ halo (2*M) Y:=by
              intro j hj; apply halo_spec.mpr; have hs:= shoots _ x j hx hj p; have hk:c ≤ k:= (le_of_not_ge hb); have hh: deepCopy p c≤ M:= (Nat.mul_le_mul_left d (Nat.add_le_add_right hk 100)).trans hp; exact ⟨x,hX, (hs.trans hh).trans (by omega)⟩
          unfold g F; rw [masked_out A h _ _ _ (agrees_mono f.source (coe_subset.mpr hg)),masked_out A h _ _ _ (agrees_mono f.sinks (coe_subset.mpr hg))]; abel
        let y:= P.site; let s:=deepCopy p c
        have hk:separation x y≤ s:= shoots _ _ _ hx (show y∈ _ from mem_union_left _ P.anchor) _
        have hz:separation x y/d ≤ c+100:=by
            have ht: d*(c+100)=s:=rfl; exact (Nat.div_le_div_right hk).trans_eq (ht ▸ Nat.mul_div_cancel_left _ hd)
        have hZ(p':Site n): 0 ≤ Heath.wick d a p' y:= (Real.exp_pos _).le
        have hm := single_le_sum (s:=Y) (fun j _=> hZ j) hX; have ht : 4 ≤ Heath.wick d a x y*t*Real.exp (p.supportExponent*c):=by
            unfold t Heath.wick; rw [mul_assoc 4, mul_left_comm _ 4, mul_assoc 4,←Real.exp_add,←Real.exp_add,←Real.exp_add]; apply le_mul_of_one_le_right (by norm_num); apply Real.one_le_exp; have hz' : (((separation x y /d:ℕ):ℝ)) ≤ (c:ℝ)+100:=by exact_mod_cast hz
            have h : (k:ℝ) ≤ c:=by exact_mod_cast hp'
            unfold a at *; linarith only [mul_le_mul_of_nonneg_left h p.exponent_pos.le,mul_le_mul_of_nonneg_left hz' p.exponent_pos.le]
        change |g i| ≤_; apply le_trans _ (single_le_sum (f:= fun j=> r j i) (fun j _=> (budget_scale (hu j) (hP j)|>.1 i)) (mem_univ y))
        suffices hh' : 4* b i ≤ r y i from le_trans (by unfold g; linarith only [abs_sub (F i U-F i V) (F i U'-F i V'),abs_sub (F i U) (F i V),abs_sub (F i U') (F i V'),hK i U,hK i V,hK i U',hK i V']) hh'
        unfold r; rw [if_pos (show (A.reg i).site=y from rfl)]; unfold BudgetPoint.mass; rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hm hT) (Real.exp_pos _).le)) (hb i).1
    have hM(U): HasSum (fun i=> F i U) (A.additive p U):= ((Activities.ESeries h).summable U).hasSum
    have hs: HasSum g _:= ((hM U).sub (hM V)).sub ((hM U').sub (hM V'))
    rw [← hs.tsum_eq]; have hx:= hh.2.1.of_nonneg_of_le (fun i=>abs_nonneg _) he
    apply (norm_tsum_le_tsum_norm (f:=g) hx).trans ((hx.tsum_le_tsum he hh.2.1).trans (hh.2.2.trans ?_))
    unfold u m; rw [← sum_mul,← sum_mul,sum_comm]
    have hp₀ : 0 ≤ δ:= budget_nonneg (hP 0)
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (sum_le_sum (fun j _=> wick_pays hA d hd j)) hT) hp₀).trans_eq; rw [Finset.sum_const,nsmul_eq_mul]; unfold t d merino a; ring
end YM.MSbar.Heath.Cottage
namespace YM.MSbar.Heath.Cottage
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup Finset Precision
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V' :Config G n}{x:Site n}{R: Rep G n}{σ C T a v δ w β:ℝ}
variable {Y X: Support n}{k M:ℕ}{p:BudgetPoint}
variable (h:R.Lawful σ C T δ w)(f:Place Y M U U' V V' R.p.threshold)(hp:deepCopy R.p k ≤ M)(hu:Place Y M U' U' V' V' R.p.threshold)(hq:R.p.B≤M)(ht:Decent R.clip R.p)(hz:0≤ R.beta)
def silkRoad (C σ δ T β:ℝ)(y M:ℕ)(p:BudgetPoint)(k:ℕ) := 2*craft C σ β y M+2*T*crownAtom σ 2* cape y σ M+merino p δ y k
include h f hp hu hq ht hz
lemma copied : |(R.exponent U-R.exponent V)-(R.exponent U'-R.exponent V')| ≤ silkRoad C σ δ T R.beta Y.card M R.p k :=by
    let P : Config G n→ℝ:= R.path.principal R.clip R.p R.beta; let A:=R.activities.additive R.p;let q : Config G n→ℝ:=R.path.inChannels R.clip R.p R.beta; let v W:=(∑ i:Site n, PathData.atomSeries R.path.loop R.p W i)
    let D:=craft C σ R.beta Y.card M; let t:= T*crownAtom σ 2* cape Y.card σ M
    have hb(i:Signed): let w:=P ∘ pull i (0:Site n); |w U-w V-(w U'- w V')| ≤ 2*D+2*t:= by
       let p:Config G n→ Config G n:= (pull i (0:Site n)); have h₀ := bud (place_oriented f i) h.paths hq ht hz; have h₁:=bud (place_oriented hu i) h.paths hq ht hz
       have hY : (harp i Y).card= Y.card:=Finset.card_image_of_injective _ (Equiv.injective _); rw [hY] at h₀ h₁
       have hp:=gassed R.path.loop (place_oriented f i) h.paths.width h.paths.two
       have hh:=gassed R.path.loop (place_oriented hu i) h.paths.width h.paths.two
       rw [hY] at hp hh; let u:=uncut R.path.loop (p U')-uncut R.path.loop (p V')
       let a:=R.beta*(regularP (p U') R.path R.clip -regularP (p V') R.path R.clip); let b(W W' :Config G n):= P (p W)-P (p W')-(v (p W)-v (p W'))-a; -- check blanks
       have hZ(W W':Config G n): b W W'= P (p W)-v (p W)-(P (p W')-v (p W'))-a:=by unfold b; ring
       have hU(V W:Config G n): v V-v W-u=v V-uncut R.path.loop (p U')-(v W-uncut R.path.loop (p V')):=by unfold u; abel
       have hg(V W:Config G n): P (p V)-P (p W) = b V W+a+u+(v (p V)-v (p W)-u):=by unfold b; ring
       intro w'; change |P (p U)-P (p V) - (P (p U')-P (p V'))|≤_; rw [hg,hg]; have hh': |v (p U)-v (p V)-u| ≤ t := by rw [hU]; exact hp
       have hζ : |v (p U')-v (p V')-u| ≤ t:=by rw [hU]; exact hh
       apply abs_le.mpr; constructor
       all_goals have hy: |b U V| ≤ D:= by rw [hZ]; exact h₀
       all_goals have hj: |b U' V'| ≤ D:= by rw [hZ]; exact h₁
       all_goals linarith only [(abs_le.mp hy).1,(abs_le.mp hy).2,(abs_le.mp hj).1,(abs_le.mp hj).2,(abs_le.mp hh').1,(abs_le.mp hh').2,(abs_le.mp hζ).1,(abs_le.mp hζ).2]
    let c:=(Fintype.card Signed:ℝ); have hc:0<c:=by unfold c; positivity
    have hc' : |q U-q V-(q U'-q V')|≤ 2*D+2*t:= by
       unfold q PathData.inChannels
       rw [← mul_sub,← mul_sub _ (∑ _,_),← mul_sub, ←sum_sub_distrib (s:=univ),←sum_sub_distrib (s:=univ),←sum_sub_distrib (s:=univ),abs_mul,abs_of_nonneg (inv_nonneg.mpr hc.le)]
       refine (mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=> hb i)) (inv_nonneg.mpr hc.le)).trans_eq ?_
       rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; exact inv_mul_cancel_left₀ hc.ne' _
    have hA:= wool R.activities h.labels f hp; unfold Rep.exponent; rw [show _ - _ - _= -((q U-q V-(q U'-q V'))+(A U-A V-(A U'-A V'))) from ?_,abs_neg] -- likely pattern
    · exact ((abs_add_le ..).trans (add_le_add hc' hA)).trans_eq (by unfold t D silkRoad; ring)
    unfold q A; abel
end YM.MSbar.Heath.Cottage
