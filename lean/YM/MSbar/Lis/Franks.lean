import YM.MSbar.Lis.Fleet
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lis
open Function Filter Whisk Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Measuring Wave
open AnalyticBridge.VerifiedReset Native.Chart
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{n:Side}{σ:Type}[Fintype σ]
local notation "X"=>Positions (Primary n G)
local notation "K"=>Primary n G
variable (p m:ℕ)
noncomputable def frown (p:ℕ) (c:G.ColorIndex)(k:List G.Color): Native.Chart.Rail G →L[ℝ] ℝ:= LinearMap.toContinuousLinearMap ({
    toFun:= fun b=> roc (compassS p b c) k 0
    map_add':= fun x y=>by change roc (compassS p (x+y) c) k 0= _; rw [show compassS p (x+y) c= compassS p x c+compassS p y c from funext fun i=>congr_arg (fun z:G.Color=>z c) (grok p i x y)]; exact addedL _ _ _ _ ((compass_sm x c p|>.contDiffAt).of_le le_top) ((compass_sm y c p|>.contDiffAt).of_le le_top) le_rfl
    map_smul':=fun x i=>by rw [show compassS p (x • i) c= (fun z=> x*compassS p i c z) from funext fun z=> congr_arg (fun i:G.Color=> i c) (steeper p z i x)]; exact wed _ _ _ _ ((compass_sm i c p|>.contDiffAt).of_le le_top) le_rfl } : Native.Chart.Rail G→ₗ[ℝ]ℝ)
noncomputable def cup (G:Gauge)(p m:ℕ) := ∑ c:G.ColorIndex, Yarn m (fun l:List G.ColorIndex=> ‖frown p c (l.map (sun G))‖)
lemma lit (t:List σ)(f:List σ→ℝ)(h:∀ l:List σ,f l ≥ 0): f t ≤ Yarn t.length f:=by
    induction t generalizing f with
    | nil=>exact le_rfl
    | cons i t ih=>rw [List.length_cons,twilled]; refine (ih _ (fun j=> h (i::j))).trans (Finset.single_le_sum (fun x _=> luster t.length (fun l _=> h _)) (Finset.mem_univ i)) -- may infer
variable (x j:Primary n G)(i:G.ColorIndex)(t:List (Primary n G))(s: Strand G)
lemma windP(c:G.ColorIndex)(l:List G.ColorIndex): ‖frown p c (l.map (sun G))‖ ≤ cup G p l.length :=by
    apply le_trans (lit l (fun i=> ‖frown p c (i.map (sun G))‖) (fun _=> norm_nonneg _)); unfold cup; refine Finset.single_le_sum (fun x _ => luster l.length (fun (t:List G.ColorIndex) _=> norm_nonneg (frown p x (t.map (sun G))))) (Finset.mem_univ c)
lemma cup_zero (G:Gauge) : 0 ≤ cup G p m:= Finset.sum_nonneg (fun i _=> luster m (fun l _ => norm_nonneg _))
local notation "M"=>tide [x,j]
lemma raft : ‖Wave.ran (ace x s) j.1‖ ≤ 2* tide [x,j] :=by
   let k:=rope x; let v:=rope j; let b:=Exterior.axisEquiv.symm s.1; let B:=beadPad k.1 v.1 1; let γ:=1+(dim [x,j]:ℝ); have he: B ≤ γ:= by have ht: separation (Measuring.chart n G j) (Measuring.chart n G x) ≤ dim [x,j]:= curve (by simp [Whisk.zone]) (by simp [Whisk.zone]); unfold B γ beadPad; rw [pow_one]; exact_mod_cast Nat.add_le_add_left ht 1 -- semicolons
   have hx(t:Site n): ‖ace x s t‖= |Midpoint.zone k t b|:=by unfold ace; rw [norm_smul,sunny,mul_one]; rfl
   have hQ:‖ace x s v.1‖≤ B:= (hx _).trans_le (sofa ..)
   change max ‖ace x s v.1‖ ‖ace x s (v.1+step v.2)‖ ≤ 2*γ; refine max_le (by have h:0 ≤ γ:=by unfold γ; positivity
                                                                              linarith only [hQ,he,h]) ((hx _).trans_le (le_trans (sofB k v b) (mul_le_mul_of_nonneg_left he (by norm_num))))
lemma waltz (c:G.ColorIndex)(l:List G.ColorIndex)(b:Native.Chart.Rail G):|roc (compassS p b c) (l.map (sun G)) 0| ≤ cup G p l.length * ‖b‖:= by let h:=frown p c (l.map (sun G)); exact (h.le_opNorm b).trans (mul_le_mul_of_nonneg_right (windP p c l) (norm_nonneg _))
lemma pays : |buoy (fun v=> choir p (ace x s) v j) 0 t| ≤ if allot j t then (2*cup G p t.length)*tide [x,j] else 0:=by
    rw [pattern]; split; next h=>
       let l : List G.ColorIndex:=t.map Prod.snd; let f:= ran (ace x s) j.1
       have hh : l.length=t.length:=List.length_map _; have ht:t.map (fun s=>sun G s.2)=l.map (sun G):= by rw [show l=t.map _ from rfl,List.map_map]; rfl
       rw [ht,←hh]; exact (waltz p j.2 l f).trans ((mul_le_mul_of_nonneg_left (raft ..) (cup_zero ..)).trans_eq (by ring))
    rw [abs_zero]
end YM.MSbar.Lis
