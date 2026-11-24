import YM.MSbar.Aqua.Comb
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Aqua
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Native.Chart Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}
local notation "A"=>G.Color
local notation "K"=>Primary n G
local notation "X"=>Positions (Primary n G)
variable {F:Positions (Primary n G)→ℝ}{V:Positions (Primary n G)→Positions (Primary n G)}{x:Positions (Primary n G)}{k m p s:ℕ}{a b C D:ℝ}
variable (h:ContDiffAt ℝ k F x)(hk:m+1≤ k)(he:ContDiffAt ℝ m V x)
noncomputable def costP (F: Positions (Primary n G)→ℝ)(V: Positions (Primary n G) → Positions (Primary n G))(x:X):= fderiv ℝ F x (V x)
local notation "S"=> buoy F x
noncomputable def loan (F: Positions (Primary n G)→ℝ)(V:Positions (Primary n G)→ Positions (Primary n G))(x:Positions (Primary n G))(i:Primary n G)(L:List Bool)(z:List K):= buoy (fun y=> V y i) x (takeout true L z)*buoy F x (i::takeout false L z)
local notation "E"=> loan F V x
include h he hk
lemma lens (L:List K)(hl:L.length=m) : buoy (costP F V) x L=∑ j:K,Yarn m (fun i:List Bool=> loan F V x j i L):=by
       let E₁(i:K)(y:X):= V y i; let F₁(i:K)(y:X):= fderiv ℝ F y (bolt i); let T (i:K):= E₁ i * F₁ i; have hz: costP F V=(fun x=>∑ i:K,T i x):=funext (fun i=>by unfold costP; nth_rw 1 [spiral (V i)]; rw [map_sum]; simp_rw [map_smul]; rfl)
       have hP(i:K): ContDiffAt ℝ m (F₁ i) x:= (h.fderiv_right (by exact_mod_cast hk)).clm_apply contDiffAt_const
       have hE(i:K): ContDiffAt ℝ m (E₁ i) x:= (ContinuousLinearMap.proj i : X→L[ℝ]ℝ).contDiff.contDiffAt.comp _ he
       unfold buoy; rw [hz,Lis.tot m _ _ T (fun i _=>(hE i).mul (hP i)) (by simp only [List.length_map,hl,le_refl])]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [show roc _ _ _= buoy (T j) _ _ from rfl, show T j = E₁ j * F₁ j from rfl,paisley m _ _ _ _ (hE j) (hP j) hl.le, hl]; apply stitch; intro T hT; unfold loan; congr 1
       let L':=takeout false T L; change roc (fun y=> fderiv ℝ F y (bolt j)) _ _= roc F (bolt j :: L'.map (@bolt (Primary n G))) _; rw [takeG k h]; rw [List.length_map]; have hp:L'.length ≤ m := (sunset false T _ (hT.trans hl.symm)).le.trans (by rw [←hT]; exact part_le ..); omega
local notation "C!"=>Measuring.chart n G
noncomputable def solo (m:ℕ) (G:Gauge) := Yarn (m+1) (fun i:List Bool=> virus G m i)
omit hk he
variable (hp:p+2≤k)(hc:ContDiffAt ℝ (↑(p+1:ℕ)) V x)(b₀ : Primary n G)
include h hp hc
open Finset
lemma sole (hh :2≤ s)(ha:0≤ a)(hv:0≤D)(hb:∀ i:Primary n G,∀ l,l≤ p+1→Yarn l (fun T:List K=> |buoy F x (i::T)| * swipe (Measuring.chart n G) a s (i::T))≤ C) (hV:∀ i:Primary n G,∀ T:List (Primary n G),T.length ≤ p+1→|buoy (fun y=>V y i) x T| ≤ D*(Lis.hits i T*tide [b₀,i])) : Yarn p (fun T:List K=> tide (b₀::T)*|buoy (costP F V) x (b₀::T)|) ≤ D * solo p G*C:=by
   let b:=b₀
   let I(j:K)(L:List Bool)(J:List K):= tide (b::J)*|E j L (b::J)|
   have hX(L:List K):0≤tide L:=by unfold tide; positivity
   have hm(L:List Bool)(hk:L.length=p+1): (∑ j:K,Yarn p (I j L)) ≤ D*virus G p L*C:=by
       have hy(j:K)(T:List K)(hx:T.length=p): I j L T ≤ D*display S b j L T:=by
          let g:= b::T; let w:=takeout true L g
          have hh:L.length=g.length:=hk.trans (by unfold g; rw [List.length_cons,hx]); have hu:w.length ≤ p+1:=(sunset _ _ _ hh|>.le).trans (part_le ..|>.trans_eq hk)
          unfold I loan; rw [abs_mul,display]; exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hV _ w hu) (abs_nonneg _)) (hX (b::T))).trans_eq (by unfold w g b; ring)
       refine le_trans (Finset.sum_le_sum (g:=fun j:K=>Yarn p (fun T:List K=> D*display S b j L T)) (fun j _=> shiny _ (hy _))) ?_; simp_rw [sheen,← Finset.mul_sum]; rw [mul_assoc D]; apply mul_le_mul_of_nonneg_left _ hv
       cases L with
       | nil=> simp at hk
       | cons v L=>
          have ht:L.length=p:=by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hk
          have hK:parts false L≤ p:= (part_le ..).trans_eq ht
          cases v
          · rw [virus,if_pos (by simp)]; refine organ S b L ht hh ha (hb _ _ (by omega)) ?_; intro j l hx; unfold buoy; apply Lis.reflect k [] (l.map Uniform.bolt) _ _ (by simp only [List.length_nil,zero_add,List.length_map]; omega) h
          rw [virus,if_neg (by simp)]; exact organS S b L ht hh ha (fun j=> hb _ _ (by omega))
   calc
      _ ≤ Yarn p (fun T:List K=>∑ j:K,Yarn (p+1) fun B:List Bool=>I j B T):=by
          apply shiny; intro i he; rw [lens h hp hc _ (by rw [List.length_cons,he])]; refine (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (hX (b::i))).trans ?_; rw [Finset.mul_sum]; refine Finset.sum_le_sum fun j _=>?_ ; unfold I; rw [sheen]; exact mul_le_mul_of_nonneg_left (polished _ _) (hX (b::i))
      _ = Yarn (p+1) (fun i:List Bool=>∑ j:K,Yarn p (I j i)):=by rw [scarves,scarves]; refine Finset.sum_congr rfl fun j _=>?_ ; exact pool p (p+1) _
      _ ≤ _:=by unfold solo; rw [← sheen,←poker]; apply shiny; intro j hj; exact hm j hj
omit hp hc b₀
include hk he
lemma fife (W:Primary n G→ℝ) (hV:∀ j:Primary n G,∀ L:List K,L.length ≤ m→ |buoy (fun y:Positions (Primary n G)=>V y j) x L| ≤ W j) (hb:∀ j:Primary n G,∀ L:List K,L.length≤ m→ |buoy F x (j::L)| ≤ C) (L:List K)(hl:L.length=m) :
      |buoy (costP F V) x L| ≤ 2^m*(∑ j:Primary n G,W j)*C:=by
   have hW(j) : 0 ≤ W j:= le_trans (abs_nonneg _) (hV j [] (by simp))
   rw [lens h hk he L hl, mul_comm (2^m), Finset.sum_mul,sum_mul]; refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun j _=>?_))
   have hx: Yarn m (fun _:List Bool=> W j*C)= W j*2^m*C:=by
       have hh(n:ℕ):Yarn n (fun _:List Bool=> W j*C)=W j*2^n*C:=by induction n with |zero=>change W j*C= _; ring|succ k ih=>rw [twilled]; simp_rw [ih]; rw [sum_const,nsmul_eq_mul]; simp; ring
       exact hh m
   rw [← hx]; refine (polished ..).trans (shiny _ ?_); intro l hp; unfold loan; rw [abs_mul]; apply mul_le_mul; exact hV j _ ((sunset true l L (by omega)).trans_le ((part_le true l).trans_eq hp)); exact hb j _ ((sunset false l L (by omega)).trans_le ((part_le false l).trans_eq hp)); exact abs_nonneg _; exact hW j
end YM.MSbar.Aqua
