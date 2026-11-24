import YM.OPE.Compatible.Glim.Pop
/-! # Wind budgets from horizon. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Variance
open Function Filter Set MeasureTheory Lattice Laurent Wilson RG Precision Metric Matrix Cascade Finset
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{P:ChartRatio G}
attribute [local instance] Gauge.frobInner
open Next.SectorChange Stationary
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion
open Flock Libra.Shell Next.Foundations Weir Score Exterior Bloch Next.Free Frequency Streamer AnalyticNext.QuarticMatch.Joint Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float
variable {u d s r l k m:ℕ}{W I:Type}{τ:Phase→ℕ}
variable (n:W→Side)(H: ∀ i,Even (n i).val)(T:∀ i,Plot (H i))(p: (i:W)→ Stand.Free (T i))(x: (i:W)→Site (n i))(h:Aware d τ)
local notation "E!" i:arg=>Libra.Keys G (Stand.Free (T i))
variable (S:W→solar G d τ)
abbrev PortS(m:ℕ):W→ℝ:= (fun i:W=>((n i).val:ℝ)⁻¹^m) * (fun i=>‖S i‖)
lemma soPaid (j:G.ColorIndex)(h:∀ i,m≤τ i)(K:ℝ)(hc:0≤K)(ht:∀ i,BeamNear (H i) (T i) (p i) (x i) K): WindT n 0 (d+2) (PortS n S m) fun i=> Pry (bop (H i) (T i) (p i) j) (Nyx (H i) (T i) (x i) (S i).val):=by
     intro z; have hc':0 ≤ LidFee d:= sq_nonneg _; let v(i:W):= Nyx (H i) (T i) (x i) (S i).val; refine ⟨⟨LidFee d*K^m,mul_nonneg hc' (pow_nonneg hc _),fun i y=>?_⟩,fun i=>pryB _ _ (Stand.composeWard _ (CloudH _ (S i) _)) z.val⟩
     let a:= bop (H i) (T i) (p i) j; have hp:= payNib (H i) (T i) (p i) (x i) j (S i).val z (h z) hc (ht i) y; let M:ℝ:= (n i).val; have ha:M ≠ 0:=(lt_of_lt_of_le zero_lt_one (W_le _)).ne'; rw [show (Pry a _ y).seq z.val= fderiv ℝ (fun t:E! i=>(v i t).seq z.val) y a from ?_]; swap; · fin_cases z<;>rfl
     rw [← mul_le_mul_iff_of_pos_left (show 0 < ((n i).val:ℝ)^m from by positivity)]; apply hp.trans_eq; unfold care PortS; rw [Pi.mul_apply,pow_zero,one_mul,inv_pow]; change LidFee d*K^m* ‖S i‖*(1+‖y‖)^(d+2)= M^m*(LidFee d*K^m*(( _ * _) * _)); field_simp;rfl
lemma crossBill (a:G.ColorIndex)(c:G.Color)(b:W→Bool): WindT n 0 2 1 fun i=> Mount (p i) c (b i) a :=by
     intro j; let f(w:Bool):= (Phone G).coord a ∘ Cast w c; let P(i:W): E! i→L[ℝ] G.Color:=ContinuousLinearMap.proj (p i); let v(e:Bool):= Pawn.mold (f e) 0; have hp(i:W):Mount (p i) c (b i) a= v (b i) ∘ P i:=moldC (P i) _ (((Phone G).coord a).toContinuousLinearMap.contDiff.contDiffAt.comp _ (cast_sm ..)) _
     let t(w:Bool)(k:ℕ):=Tensor.coeff (f w) k 0; have hV(i:Bool)(x:G.Color): (v i x).seq j.val = t i j.val (fun _=> x):=by fin_cases j<;>rfl
     let M:=‖t true j.val‖+‖t false j.val‖; have he(i):‖t i j.val‖≤M:=by unfold M; cases i<;>simp
     refine ⟨⟨M,(norm_nonneg _).trans (he false),fun i y=>?_⟩,fun i=> (tallJ 0 _ j.val)⟩
     dsimp only; rw [hp,Function.comp_apply,hV]; apply ((t _ _).le_opNorm _).trans; rw [prod_const,card_univ, Fintype.card_fin]; unfold care; rw [pow_zero,Pi.one_apply,one_mul,one_mul]; have hv: 0≤ M:=(norm_nonneg _).trans (he true); apply le_trans (mul_le_mul_of_nonneg_right (he _) (by positivity)); apply mul_le_mul_of_nonneg_left _ hv; exact (pow_le_pow_left₀ (by positivity) ((show ‖P i y‖≤ _ from norm_le_pi_norm y (p i)).trans (le_add_of_nonneg_left zero_le_one)) j.val).trans (pow_le_pow_right₀ (by simp) (Nat.le_of_lt_succ j.isLt))
lemma wtSum (p: I→ (i:W)→ ScriptJ (E! i)) (t:W→ℝ)(s:Finset I)(hp:∀ i∈s, WindT n r k t (p i)) : WindT n r k t (∑ i∈s,p i) :=by induction s using Finset.induction_on with
     | empty=> rw [Finset.sum_empty]; exact WindT.zero (C:=fun j:W=>Libra.Keys G (Stand.Free (T j))) n r k t
     | insert i s hi ih=> rw [sum_insert hi]; exact WindT.add (hp i (mem_insert_self ..)) (ih (fun i hi=> hp _ (mem_insert_of_mem hi)))
lemma AiryPaid (a:G.ColorIndex)(b:W→Bool)(h:∀ i,m≤τ i)(K:ℝ)(hc:0≤K)(ht:∀ i,BeamNear (H i) (T i) (p i) (x i) K): WindT n 0 (2+(d+2)) (PortS n S m) fun i=> Topper (p i) ((Phone G) a) (b i) (Nyx (H i) (T i) (x i) (S i).val):=by
     let Z(j:G.ColorIndex)(i:W):= Mount (p i) ((Phone G) a) (b i) j *Pry (An (p i) (Phone G) j) (Nyx (H i) (T i) (x i) (S i).val); have hh:(fun i:W=>Topper (p i) ((Phone G) a) (b i) (Nyx (H i) (T i) (x i) (S i).val)) = ∑ j,Z j:=funext fun v=> (Finset.sum_apply v _ Z).symm; rw [show (fun i=> Topper _ _ _ _)=_ from hh]; apply wtSum; intro i _; exact Eq.mp (by rw [one_mul]:WindT n _ _ ((1:W→ℝ)* PortS n S m) (Z i) = WindT n _ _ _ (Z i)) ((crossBill n H T p i ((Phone G) a) b).prod (soPaid n H T p x S i h K hc ht) zero_le_one)
end YM.OPE.Variance
