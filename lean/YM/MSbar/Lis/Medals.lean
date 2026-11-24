import YM.MSbar.Lis.Hubs
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{a b C D:ℝ}{k q p m:ℕ}
local notation "K"=>Primary n G
local notation "X"=>Positions (Primary n G)
variable (F: Positions (Primary n G)→ℝ) (x:Primary n G)(s: Strand G)
variable (he:ContDiffAt ℝ k F 0)(hq:m+2≤k)
local notation "Φ"=>buoy F 0
local notation "N"=>Measuring.chart n G
noncomputable def optics (k:ℕ)(F : Positions (Primary n G)→ℝ)(z:Site n→G.Color)(x:Positions (Primary n G)):= fderiv ℝ F x (choir k z x)
lemma rose (D:ℕ)(k n':ℕ)(he:ContDiffAt ℝ k F 0)(h:n'+1≤k)(z:Site n→G.Color): ContDiffAt ℝ n' (optics D F z) 0:= (he.fderiv_right (by exact_mod_cast h)).clm_apply ((diag_smooth (Tensor.coeff (speedsK z) D 0) n').contDiffAt)
noncomputable def virus (G:Gauge)(m:ℕ) (K':List Bool):ℝ:= if K'.head?=some false then (Fintype.card G.ColorIndex:ℝ)^parts true K'.tail else (Fintype.card G.ColorIndex:ℝ)^(parts true K'.tail+1)
noncomputable def medal (G:Gauge)(m p:ℕ):= Yarn (m+1) (fun i:List Bool=> 2*cup G p (parts true i)*virus G m i)
lemma mpos (G:Gauge)(p m:ℕ):0 ≤ medal G m p:=by apply luster; intro i hi; have hp:=cup_zero p (parts true i) G; unfold virus; split <;> positivity
local notation "U"=> Primary n G
variable (hb:∀ i:Primary n G,∀ l:ℕ,l≤ m+1→Yarn l (fun T:List (Primary n G)=>|buoy F 0 (i::T)| *swipe (Measuring.chart n G) b q (i::T))≤ C)(hp:2≤ q)(ha:0≤ b)
include he hq hp ha hb
-- Use Y in [0,R].P orientation as slide.G
lemma dots (l:ℕ) : Yarn m (fun T:List K=> tide (x::T)*|buoy (optics l F (ace x s)) 0 (x::T)|) ≤ medal G m l*C:=by
   let W:=optics l F (ace x s); let E(k:K)(y:X):= choir l (ace x s) y k; let p(k:K)(y:X):= fderiv ℝ F y (bolt k); let V(k):= E k*p k; let t(j:K)(T:List Bool)(J:List K):= buoy (E j) 0 (takeout true T (x::J))*Φ (j::takeout false T (x::J)); have h0:W=(fun x=>∑ i:K,V i x):=funext (fun i=>by unfold W optics; nth_rw 1 [spiral (choir l (ace x s) i)]; rw [map_sum]; simp_rw [map_smul]; rfl)
   have hP(i:K): ContDiffAt ℝ (↑(m+1:ℕ)) (p i) 0:= (he.fderiv_right (by exact_mod_cast hq)).clm_apply contDiffAt_const
   have hE(i:K): ContDiffAt ℝ (↑(m+1:ℕ)) (E i) 0:= (ContinuousLinearMap.proj i : X→L[ℝ]ℝ).contDiff.contDiffAt.comp _ ((Tensor.diag_smooth (Tensor.coeff (speedsK (ace x s)) l 0) (↑(m+1:ℕ))).contDiffAt)
   have he'(J:List K)(ht:J.length=m): buoy W 0 (x::J)=∑ j:K,Yarn (m+1) fun A:List Bool=>t j A J:=by
       have hx:(x::J).length=m+1:= by rw [List.length_cons,ht]
       unfold buoy; rw [h0,Lis.tot (m+1) _ _ V (fun i _=>(hE i).mul (hP i)) (by simp only [List.length_map,hx,le_refl])]
       refine Finset.sum_congr rfl fun j _=>?_ ; rw [show roc _ _ _= buoy (V j) _ _ from rfl, show V j = E j * p j from rfl,paisley (m+1) _ _ _ _ (hE j) (hP j) hx.le, hx]; apply stitch; intro A hA; unfold t; congr 1
       let L:=takeout false A (x::J); change roc (fun y=> fderiv ℝ F y (bolt j)) _ _= roc F (bolt j :: L.map (@bolt (Primary n G))) _; rw [takeG k he]; rw [List.length_map]; have hp:L.length ≤ m+1 := (sunset false A _ (hA.trans hx.symm)).le.trans (by rw [←hA]; exact part_le ..); omega
   let I(j:K)(L:List Bool)(J:List K):= tide (x::J)*|t j L J|
   let A(L:List Bool):=2*cup G l (parts true L)
   have hA(L):0≤ A L:=by unfold A; have ht:=cup_zero l (parts true L) G; positivity
   have hm(L:List Bool)(h:L.length=m+1): (∑ j:K,Yarn m (I j L)) ≤ A L*virus G m L*C:=by
       have hv(j:K)(T:List K)(hx:T.length=m): I j L T ≤ A L*display Φ x j L T:=by
          let F:= x::T; let J:=takeout true L F
          have ha :0≤ tide F:=by unfold tide; positivity
          have he: |buoy (E j) 0 J|≤ A L*(hits j J*tide [x,j]):=by
               have hv:J.length=parts true L:= sunset _ _ _ (by unfold F; simp only [List.length_cons,h,hx]); apply le_trans (pays l x j J s); unfold hits; split; next he=> rw [hv,one_mul]
               next he=>simp
          unfold I t; rw [abs_mul,display]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (abs_nonneg _)) ha).trans_eq (by unfold J F; ring)
       refine le_trans (Finset.sum_le_sum (g:=fun j:K=>Yarn m (fun T:List K=> A L*display Φ x j L T)) (fun j _=> shiny _ (hv _))) ?_; simp_rw [sheen,← Finset.mul_sum]; rw [mul_assoc (A L) (virus G m L)]; apply mul_le_mul_of_nonneg_left _ (hA L)
       cases L with
       | nil=> simp at h
       | cons v L=>
          have h:L.length=m:= by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h
          have hK:parts false L≤ m:= (part_le ..).trans_eq h
          cases v
          · rw [virus,if_pos (by simp)]; refine organ Φ x L (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h) hp ‹0≤ b› (hb _ _ (by omega)) ?_; intro j l hx; unfold buoy; apply Lis.reflect k [] (l.map Uniform.bolt) _ _ (by simp only [List.length_nil,zero_add,List.length_map]; omega) he
          rw [virus,if_neg (by simp)]; exact organS Φ x L (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using h) hp ‹0≤ b› (fun j=> hb _ _ (by omega))
   calc
      _ ≤ Yarn m (fun T:List K=>∑ j:K,Yarn (m+1) fun B:List Bool=>I j B T):=by
          apply shiny; intro i h; rw [he' i h]; have hx :0≤tide (x::i):=by unfold tide; positivity
          refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) hx).trans ?_; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; unfold I; rw [sheen]; exact mul_le_mul_of_nonneg_left (polished _ _) hx
      _ = Yarn (m+1) (fun i:List Bool=>∑ j:K,Yarn m (I j i)):=by rw [scarves,scarves]; refine Finset.sum_congr rfl fun j _=>?_ ; exact pool m (m+1) _
      _ ≤ _:=by unfold medal; rw [←poker]; apply shiny; intro j hj; exact hm j hj
end YM.MSbar.Lis
