import YM.FormalBulk08.Kemp.Pouch

noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05
open Lotus Shore Mesa Gorge City Cork Rift
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {X V I : Type*} {m n r : ℕ} {D : Reach V} {R : Reach I}{η θ A B C : ℝ}{o:V}

lemma fund_stare {q : V→V→ℝ}{T : Tile V (n+1+1)}(h: Knoxville D η o T C)(he:0≤η)(hq:∀ a b,‖q a b‖≤B)(hb:0≤B): Allow D η o (telescopeTerm q T) ((1/2*(n+2)*(n+1))*(B*C)):= by
    let K:ℝ:=1/2*(n+2)*(n+1); have hk:0≤K:= by unfold K; positivity
    refine ⟨mul_nonneg hk (mul_nonneg hb h.1),?_⟩
    rw [←ENNReal.tsum_prod]; let f : chain V n×(V×V)→ chain V (n+1+1) := fun v=> Fin.cons v.2.2 (Fin.cons v.2.1 v.1)
    have hv : Injective f:= by
       rintro ⟨a,b,c⟩ ⟨w,r,s⟩ h; simp only [f,Fin.cons_inj] at h; simp [h.1,h.2.1,h.2.2]
    rw [ENNReal.ofReal_mul hk, ENNReal.ofReal_mul hb]; refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right ((ENNReal.tsum_comp_le_tsum_of_injective hv (penon D o η T)).trans h.2) _) _); rw [←ENNReal.tsum_mul_left,←ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum; intro v
    have ha:herb D o v.1 ≤ herb D o (f v) := by
        let g (i: Fin (n+1)) : Fin (n+1+1+1):= Fin.cases 0 (fun i=> i.succ.succ.succ) i
        have hh (i:Fin (n+1)):(Fin.cons o v.1:chain V (n+1)) i=(Fin.cons o (f v):chain V (n+1+1+1)) (g i):= by cases i using Fin.cases <;> simp [f,g]
        refine known_wide _ _ _ (fun i j=>?_); rw [hh,hh];exact reached _ _ (g i) (g j)
    have hp:telescopeTerm q T v.1 v.2=K*q v.2.1 v.2.2*T (f v):= by unfold telescopeTerm halve Lava.shed;unfold f K;push_cast; rw [map_div₀, map_one, map_ofNat];ring
    unfold penon;rw [hp,enorm_mul,enorm_mul,← ofReal_norm K,Real.norm_eq_abs,abs_of_nonneg hk]; calc
        _ ≤ Gorge.shine η (herb D o (f v))* (ENNReal.ofReal K * ENNReal.ofReal B * ‖T (f v)‖ₑ) := by gcongr; exacts [shine_le _ he ha,by rw [← ofReal_norm];exact ENNReal.ofReal_le_ofReal (hq ..)] -- gcongr
        _ = _ := by unfold herb; ring
lemma knox_stare {q : V→V→ℝ}{T : Tile V (n+1+1)}(h: Knoxville D η o T C)(he:0≤η)(hq:∀ a b,‖q a b‖≤B)(hb:0≤B): Knoxville D η o (stare q T) ((1/2*(n+2)*(n+1))*(B*C)) := (fund_stare h he hq hb).bill

lemma arch_step (u:chain V m)(v:chain V n)(a b:V): herb D o (castle V m n (u,v)) ≤ wide D (Fin.cons a u:chain V (m+1)) + D.d a b + herb D o (Fin.cons b v : chain V (n+1)) := by
    let X := wide D (Fin.cons a u : chain V (m+1)); let W : chain V (n+1+1):= Fin.cons o (Fin.cons b v); let Y:=wide D W
    have he (i : Fin m) (j : Fin (n+1+1)):D.d (u i) (W j) ≤ X+D.d a b + Y := by
       have hv := D.tri (u i) a b;have hz :=D.tri (u i) b (W j); have h' :D.d (u i) a≤ X:=reached D (Fin.cons a u : chain V (m+1)) i.succ 0
       have hu : D.d b (W j)≤Y := reached _ W (Fin.succ 0) j; omega
    refine known_wide _ _ _ (fun i j=>?_)
    cases i using Fin.cases with
    | zero=>
       cases j using Fin.cases with
       | zero=> rw [D.self];omega
       | succ j=> cases j using Fin.addCases with
                  | left j=> simp only [Fin.cons_zero,Fin.cons_succ,castle, Equiv.coe_fn_mk, Fin.append_left]; rw [D.turn]; exact he j 0
                  | right j=> simp only [Fin.cons_zero,Fin.cons_succ,castle,Equiv.coe_fn_mk,Fin.append_right];exact le_trans (b:=Y) (reached D W 0 j.succ.succ) (show Y ≤ X+D.d a b+Y by omega)
    | succ i=>
       cases j using Fin.cases with
       | zero=> cases i using Fin.addCases with
                | left i=> simp only [Fin.cons_zero,Fin.cons_succ,castle,Equiv.coe_fn_mk,Fin.append_left];exact he i 0
                | right i=> simp only [Fin.cons_zero,Fin.cons_succ,castle,Equiv.coe_fn_mk,Fin.append_right];exact le_trans (b:=Y) (reached D W i.succ.succ 0) (show Y ≤ X+D.d a b+Y by omega)
       | succ j=> cases i using Fin.addCases <;> cases j using Fin.addCases <;> rename_i i j <;> simp only [castle,Equiv.coe_fn_mk,Fin.cons_succ,Fin.append_left,Fin.append_right]
                  · exact le_trans (b:=X) (reached D (Fin.cons a u : chain V (m+1)) i.succ j.succ) (show X≤X+D.d a b+Y by omega)
                  · exact he i j.succ.succ
                  · rw [D.turn]; exact he j i.succ.succ
                  exact le_trans (b:=Y) (reached D W i.succ.succ j.succ.succ) (show Y ≤ X+D.d a b+Y by omega)
lemma funded_cross {q : V→V→ℝ}(h : Grate D η (fun i j=>q j i) C)(hp : 0≤η){T : Tile V (m+1)}{S : Tile V (n+1)}(he:Bail D η T A)(ht: Knoxville D η o S B) : Allow D η o (weld q T S) ((1/2*(m+1)*(n+1))*(A*C*B)):= by
   let K:ℝ:=1/2*(m+1)*(n+1); have hk:0≤K:= by unfold K; positivity
   let L (u:chain V m)(a:V):= glitter D η T (Fin.cons a u)
   let W (b:V)(a:V):= Gorge.shine η (D.d b a) * ‖q a b‖ₑ
   let U (b:V)(v:chain V n):= penon D o η S (Fin.cons b v)
   have H (u:chain V m)(v:chain V n)(a b:V):
        Gorge.shine η (herb D o (castle V m n (u,v)))*‖weld q T S (castle V m n (u,v)) (a,b)‖ₑ ≤ ENNReal.ofReal K*(L u a*W b a*U b v):= by
       have hx:=arch_step (D:=D) (o:=o) u v a b; rw [D.turn a b] at hx; apply (mul_le_mul_left (shine_le _ hp hx) _).trans_eq
       rw [show weld q T S (castle V m n (u,v)) (a,b)=K*q a b*(T (Fin.cons a u))*(S (Fin.cons b v)) from by unfold weld K halve clutch;simp [Lava.shed,castle,Function.comp_def];ring, shine_add,shine_add,enorm_mul,enorm_mul,enorm_mul,← ofReal_norm K,Real.norm_eq_abs, abs_of_nonneg hk]
       unfold L W U penon glitter; ring
   refine ⟨mul_nonneg hk (mul_nonneg (mul_nonneg he.1 h.1) ht.1),?_⟩
   rw [ENNReal.tsum_comm, ENNReal.tsum_prod', ENNReal.tsum_comm];refine le_trans (b:=∑' b,∑' a,∑' u: chain V m,∑' v:chain V n, ENNReal.ofReal K*(L u a*W b a*U b v)) ?_ ?_
   · refine ENNReal.tsum_le_tsum (fun b=> ENNReal.tsum_le_tsum fun a=>?_);rw [←Equiv.tsum_eq (castle V m n),ENNReal.tsum_prod']; exact ENNReal.tsum_le_tsum (fun u=> ENNReal.tsum_le_tsum (H u · a b))
   rw [ENNReal.ofReal_mul hk, ENNReal.ofReal_mul (mul_nonneg he.1 h.1),ENNReal.ofReal_mul he.1]; have he' : (∑' b,∑' v,U b v) ≤ ENNReal.ofReal B := by rw [←ENNReal.tsum_prod,show (∑' u: V × chain V n, U u.1 u.2) = ∑' t,penon D o η S t from Equiv.tsum_eq (Fin.consEquiv (fun _:Fin (n+1)=> V)) (penon D o η S)]; exact ht.2
   simp_rw [ENNReal.tsum_mul_left]; gcongr
   refine le_trans ?_ (mul_le_mul_right he' (ENNReal.ofReal A * ENNReal.ofReal C)); rw [←ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro b
   simp_rw [ENNReal.tsum_mul_right];gcongr
   apply le_trans ?_ (mul_le_mul_right (h.2 b) (ENNReal.ofReal A)); rw [←ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro u; exact mul_le_mul_left (rim_stud he u) _
lemma knox_bond {q : V→V→ℝ}(h : Grate D η (fun i j=>q j i) C)(hp : 0≤η){T : Tile V (m+1)}{S : Tile V (n+1)}(he:Bail D η T A)(ht: Knoxville D η o S B) : Knoxville D η o (bond q T S) ((1/2*(m+1)*(n+1))*(A*C*B)) := (funded_cross h hp he ht).bill
end YM.FormalBulk08.Kemp
