import YM.MSbar.Chord.Monte
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter
open AnalyticBridge.SectorAffine.Offset
open Lattice Wilson Gauge Work.F03 Push Push.Uniform RG Precision Exterior AnalyticBridge.VerifiedReset Planned.AtomRegular MSbar.Rolling MSbar.Wave Set
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{c : Side}{p:BudgetPoint}{X : Support c}{g : Config G c→ℝ} {U:Config G c}{x: Positions (Primary c G)}{k:ℕ}{d:RegularAddress c}{a W r:ℝ}
local notation "V"=>Config G c
local notation "E₀"=> Positions (Primary c G)
noncomputable def palace (x:Positions (Primary c G)):Config G c:= increment 1 (panel G c x)
variable (hf:p.Regular X g)(hp:p.supBounds d.site X g a)(he:Healthy p.threshold X (palace x))
def deed (k:ℕ) :ℝ:=1+∑ i∈ Finset.range (k+1),polarCost i
noncomputable def floorY (G:Gauge)(k:ℕ):ℝ:= (account k G).choose
noncomputable def earnE (p:BudgetPoint) (G:Gauge) (i:ℕ):= composeCost i (deed i/p.threshold^i) (floorY G i)
lemma floorP (G:Gauge)(p:BudgetPoint)(i:ℕ):0 ≤ earnE p G i:=by have hv: 0 ≤ deed i:= add_nonneg zero_le_one (Finset.sum_nonneg (fun i _=> zero_le_one.trans (polar_one i))); have hh := (account i G).choose_spec.1; unfold earnE floorY composeCost; have hp:= p.threshold_pos; positivity
noncomputable def Program (g:Config G c→ℝ)(x:Positions (Primary c G)):= g (palace x)
include hf hp he
lemma fluxP {k:ℕ}(hx:k≤ p.order)(hr:‖x‖≤1): Through k (Program g) x (earnE p G k*a):=by
   let u:=palace x; let f:=g ∘ increment u
   have hP:= hp.1; let P:=p.threshold; have hL:0<P:=p.threshold_pos; let d':= deed k/P^k; have hx' : Through k f 0 (d'*a):=by
       refine ⟨(hf.smooth u he).of_le (Nat.cast_le.mpr hx),fun i hi=>?_⟩; let Q:= p.threshold; apply (all_chart hf he hp (hi.trans hx)).trans
       have hv : 0 ≤ polarCost i:=zero_le_one.trans (polar_one i); have hX: P^k ≤ P^i := pow_le_pow_of_le_one hL.le p.threshold_le hi
       have hu:polarCost i ≤ deed k:= (Finset.single_le_sum (f:=polarCost) (fun i _=>zero_le_one.trans (polar_one i)) (Finset.mem_range.mpr (by omega))).trans (le_add_of_nonneg_left zero_le_one)
       exact (le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hP (pow_pos hL k) hX) hv) ((mul_le_mul_of_nonneg_right hu (div_nonneg hP (pow_pos hL k|>.le))).trans_eq (by unfold d'; change _*(a/P^k)=_; ring)))
   have hF:= (show Through k f (chartW x x) (d'*a) from (birthday x).symm ▸ hx').comp ((account k G).choose_spec.2 _ x hr)
   refine (hF.mono (show _ ≤ earnE p G k*a from (by unfold earnE composeCost d' floorY P; exact le_of_eq (by ring)))).germ ((bendUses x).mono (fun y he=>congr_arg g he))
end YM.MSbar.Midpoint
