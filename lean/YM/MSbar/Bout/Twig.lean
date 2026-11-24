import YM.MSbar.Bout.Eyre
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
local notation "L"=>l++[i]
local notation "J"=> Lis.rope i
local notation "C"=> pushChart F G v
local notation "A₀"=> arch F v (Lis.rope i)
local notation "A"=>singularity (pushChart F G v) 2
noncomputable def serve (F:Forest S.ratio) (G:Gauge):Positions (Primary c G)→L[ℝ] Positions (Joint F G):= (partSpace (Primary c G) _).symm.toContinuousLinearMap.comp ((ContinuousLinearMap.id ℝ _).prod 0)
lemma ground (t:ℝ)(g:E→ℝ) (h:ContDiffAt ℝ l.length g (t•meetVar x w)) : buoy (fun u:Y=>g (t • meetVar u w)) x l=roc g (l.map fun i => t • hands F G i) (t • meetVar x w):=by
    -- use more h for lower, translation.He
    let q:= (t • (meetVar (0:Y) w)); let f(y:E):=g (q+y); let H:Y→L[ℝ] E:= t • serve F G
    have he(u:Y) :q+H u=t • meetVar u w:=by change t • _+t • meetVar u 0=_; rw [←smul_add]; unfold meetVar; rw [← map_add,Prod.mk_add_mk,zero_add,add_zero]
    have hp(j:ℕ): ContDiffAt ℝ j g (t • X) → ∀ l':List E,l'.length=j → roc f l' (H x)=roc g l' (t • X):=by
        intro hh l' ht; rw [rod j _ _ _ ht.le,rod j _ _ hh ht.le]; · unfold f; rw [iteratedFDeriv_comp_add_left,he]
        exact (show ContDiffAt ℝ j g (q+H x) from he x|>.symm ▸ hh).comp (H x) (f:=fun x=>q+x) (contDiffAt_const.add contDiffAt_id)
    unfold buoy; rw [show (fun u:Y=>g _) = f∘H from (funext fun u=> congr_arg _ (he u).symm), toe H l.length (l.map bolt) _ (by simp),hp _ h _ (by simp),List.map_map];rfl
    exact (show ContDiffAt ℝ (↑l.length) g (q+H x) from he x|>.symm ▸ h).comp (H x) (f:=fun y=>q+y) (contDiffAt_const.add contDiffAt_id)
noncomputable def parmaM (F:Forest S.ratio)(w: Positions (Key F G))(t:ℝ) := mer F G (t • meetVar (0: Positions (Primary c G)) w)
lemma funds (t:ℝ) (e:Bond c) : (fun y:Y=>arch F v e (t • meetVar y w))=fun y=> S.kernel.penalty * rowS G 1 t e (wing S (parmaM F w t) v e) y:=by -- parmaM
    funext y; have he(y':Y): mer F G (t • meetVar y' w)=parmaM F w t:=by unfold parmaM mer; unfold Parma.cup; change fine G F (lowerCol ((pushG (G:=G) F) _))= fine G F (lowerCol ((pushG F) _)); rw [_root_.map_smul (pushG ..),_root_.map_smul (pushG ..)]; rfl
    unfold arch; rw [he]; have hp : outer G F (t • meetVar y w)= postcard G c t y:=by unfold outer postcard; rw [_root_.map_smul,_root_.map_smul];rfl
    rw [hp]; unfold Gauge.price rowS wing; rw [one_mul, G.mat_mul]
lemma select (t:ℝ)(e:Bond c)(h:ContDiffAt ℝ (l++[i]).length (arch F v e) (t•meetVar x w))(he:e ≠ Lis.rope i) : roc (arch (G:=G) F v e) ((l++[i]).map fun i=> t • hands F G i) (t •meetVar x w)=0:=by
    rw [← ground F x w (l++[i]) t _ h, funds]; unfold buoy; let R:=parmaM F w t; let k:=wing S R v e; rw [Lis.wed (l++[i]).length _ _ (rowS G 1 t e k) (by apply ContDiffAt.of_le (n:=ω) _ le_top; exact (((stage_Row ..).comp (f:=fun y:Y=>(y,k)) (contDiff_id.prodMk contDiff_const)).contDiffAt)) (by simp), show roc _ _ _= _ from (show buoy _ _ _=0 from rung t x e k l i he),mul_zero]
end YM.MSbar.Bout
