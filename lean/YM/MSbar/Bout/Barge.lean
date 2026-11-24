import YM.MSbar.Bout.Twig
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bout
open Function Filter Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Set
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Parma Portal
variable {G:Gauge}{c f:Side}{S:StepData c f}(F:Forest S.ratio)(v:S.Choices)(x:Positions (Primary c G))(w:Positions (Key F G))(l:List (Primary c G))(i:Primary c G)(p:ℕ)
variable {t B K r:ℝ}
local notation "Y"=>Positions (Primary c G)
local notation "E"=>Positions (Joint F G)
local notation "X"=>meetVar x w
local notation "J"=> Lis.rope i
local notation "C"=> pushChart F G v
local notation "A₀"=> arch F v (Lis.rope i)
local notation "A"=>singularity (pushChart F G v) 2
open scoped ContDiff
open Analysis

variable (hc: ∀ i:Bond c, ContDiffAt ℝ ω (Parma.arch F v i) (0:Positions (Joint F G)))
variable (e:Bond c)
include hc
lemma groom : blockTaylor p (pushChart F G v)= fun x=> ∑ i:Bond c, blockTaylor p (arch F v i) x:=by
     funext x; let f(i:Bond c) := arch (G:=G) F v i; unfold blockTaylor; simp_rw [Finset.sum_apply]; rw [sum_comm]
     rw [funext (robe F v)] -- direction???
     refine Finset.sum_congr rfl fun i _=>?_ ; have hF : ∑ e':Bond c, f e'=fun x=>∑ e',f e' x:= funext fun i=>Finset.sum_apply ..; rw [←hF]; unfold Tensor.diagonal Tensor.coeff; rw [iteratedFDeriv_sum_apply (fun i _=> (hc i).of_le le_top),Finset.smul_sum,_root_.sum_apply] -- signature?
-- potter independent along hands of other.
lemma jetK (hh:e ≠ Lis.rope i) : D (hands F G i) (arch (G:=G) F v e)=ᶠ[𝓝 0] 0:=by
     let k:=Y; filter_upwards [(hc e|>.of_le (m:=↑(1:ℕ)) le_top).eventually (by simp)] with x hx
     let y:= partSpace (Primary c G) (Key F G) x; have he:x=meetVar y.1 y.2:=by unfold meetVar; rw [Prod.mk.eta]; symm; apply ContinuousLinearEquiv.symm_apply_apply
     change fderiv ℝ _ x _=0
     have hq : roc (arch F v e) [hands F G i] x=0:=by
          have h':ContDiffAt ℝ (↑(([]++[i]).length)) (arch F v e) ((1:ℝ) • meetVar y.1 y.2):=by rw [one_smul, ←he]; exact hx
          have hp:= select F v y.1 y.2 [] i 1 e h' hh; simp only [List.nil_append, List.map_cons,List.map_nil,one_smul,← he] at hp;exact hp
     exact hq
lemma scarce (hh:e ≠ Lis.rope i) (t:ℝ) (L:List (Primary c G)):roc (blockTaylor p (arch F v e)) ((L++[i]).map fun i=>t • hands F G i) (t • meetVar x w)=0:=by
     let f: E→ℝ:= arch F v e; let g:=blockTaylor p f; have he:D (hands F G i) g=0:=by
        unfold g; cases p with
        | zero=>
           have he:blockTaylor 0 f=fun _=>f 0:= by funext x; unfold blockTaylor; rw [Finset.sum_apply,sum_range_succ,sum_range_zero,zero_add]; exact Tensor.coeff_apply_zero ..
           rw [he]; funext i; change fderiv ℝ (fun _=> f 0) _ _=0; simp
        | succ n=> change D _ (blockTaylor (n+1) f)=0; rw [D_blockTaylor ((hc ..).of_le le_top)]; funext i'; unfold blockTaylor; rw [Finset.sum_apply]; apply sum_eq_zero; intro j hj; unfold Tensor.diagonal Tensor.coeff; rw [((jetK F v i hc e hh).iteratedFDeriv ℝ _).eq_of_nhds]; simp
     let L':=L.map fun i=> t •hands F G i; change roc g _ _=_; simp only [List.map_append,List.map_cons,List.map_nil]; have hp:ContDiffAt ℝ (↑(L'.length+1:ℕ)) g (t• X):= (blockTaylor_contDiff ..).contDiffAt; rw [fore (L'.length+1) hp (l:=L') (he:=Nat.lt_succ_self _), Lis.takeG (L'.length+1) hp _ _ (Nat.lt_succ_self _)]
     have hz(x:E): fderiv ℝ g x (t • hands F G i)=0:=by rw [_root_.map_smul, show fderiv ℝ g x (hands F G i)=0 from congr_fun he x,smul_zero]
     rw [funext hz]; have hp(T:List E) :roc (fun _:E=> (0:ℝ)) T=0:=by induction T with|nil=> rfl|cons a b ih=> funext x;rw [roc,ih,fderiv_zero];rfl
     rw [hp]; rfl
lemma chosen (u:ℝ) :roc (blockTaylor p (pushChart F G v)) ((l++[i]).map fun i=>u •hands F G i) (u•meetVar x w) = roc (blockTaylor p (arch F v (Lis.rope i))) ((l++[i]).map fun i=>u •hands F G i) (u•meetVar x w):=by
    let L':=(l++[i]).map fun i=>u •hands F G i; rw [groom F v p hc,Lis.tot L'.length L' Finset.univ (fun e:Bond c=> blockTaylor p (arch F v e)) (fun i _=>(blockTaylor_contDiff ..).contDiffAt) le_rfl]; exact sum_eq_single_of_mem J (mem_univ _) fun i _ hi=>scarce F v x w _ p hc i hi u l
end YM.MSbar.Bout
