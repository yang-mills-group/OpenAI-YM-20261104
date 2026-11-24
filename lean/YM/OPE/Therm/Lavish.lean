import YM.OPE.Therm.Expanses
import Mathlib.Analysis.Convex.Integral
/-!
# One history exponential-DLG bound (program lands with pressures)

Room programs haven/t been integrated at this point, just parametrized
by finite-demand tests. Theta chosen twice. Protect one post-L.H not neighborhood.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Cradle
open Function Set Filter RG Lattice Wilson MeasureTheory Cells
open House (press tape bath edges press_add stills fence chilly countables)
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {n : Side} {G:Gauge} {t C e:ℝ}
local notation "𝒞" => Config G n
local notation "E"=>Edge (Site n)
local notation "η" => prior G n
local notation "Ex" => Real.exp
variable (T:Tiling n)(R:Rep G n)(r:ℕ)(τ t C :ℝ)
local notation "c"=> House.gx T (Stove.haloFee R r+1)
local notation "a"=> ((c:ℝ)^4*C)
local notation "ζ"=> touchW (G:=G) t (Finset.card (edges T 0))
local notation "U₀" => Fintype.card T.Cell
local notation "seamL"=> touchW (G:=G) t (Finset.card (House.seam T))
local notation "fᵣ"=> edgeLoss T R r C e
noncomputable def premium := 2*a+ζ
local notation "D"=> premium T R r t C
def order (F:T.Cell→𝒞→ℝ)(J:T.Cell) (U:𝒞) (p:ℝ) := if U∈ chilly (countables T J) τ then F J U else -p
def pend (F:T.Cell→𝒞→ℝ)(U:𝒞) (p:ℝ) := ∑ i, order T τ F i U p
def vigor (F:T.Cell→𝒞→ℝ) (i:T.Cell)(U:𝒞) := cell T R r τ i U * Ex (F i U)
def labor (F:T.Cell→𝒞→ℝ) (i:T.Cell)(U:𝒞):= vigor T R r τ F i U+ Ex (-a-ζ)
def graphRate (e:ℝ) (P:T.Cell→ℝ):= (∑ i,P i)+2*edgeLoss T R r C e+ U₀*Real.log 3 + seamL
structure Programs (F:T.Cell→𝒞→ℝ) (P:T.Cell→ℝ) : Prop where
   home i : fence (House.fullRoom T i) (F i)
   pos i :0 ≤ P i
   bill i : Envelope (F i)
   pays (i:T.Cell) (V:𝒞) : press (edges T i) (vigor T R r τ F i) V ≤ Ex (P i)*Z T R r τ i V

variable {R r t C} (hv:T.kind=.site)(h:Stove.Chart R r C e){F:T.Cell→ Config G n→ℝ}{P:T.Cell→ℝ}
local notation "p₀"=>Ex (graphRate T R r t C e P)
variable {τ}
lemma playEnv {h:T.Cell→ Config G n→ℝ} (hz:∀ i, Envelope (h i))(p τ:ℝ) : Envelope (fun U=>pend T τ h U p):= by
   apply Envelope.sum Finset.univ (fun i U=> order T τ h i U p); intro i; exact Envelope.piece (House.bath (countables T i)) (hz i) (Envelope.const _)
include hv h
set_option maxHeartbeats 400000 in
lemma pressure (he:Programs T R r τ F P) (hy:t>0)(ht:t≤1)(hx:4*t+τ≤ R.p.threshold)(hβ :4*t≤τ)(hb:2≤ T.side.val){σ A Λ δ w:ℝ}(H:R.Lawful σ A Λ δ w) (hw:w≤1)(hz:∀ U,0≤ R.eval U):
    (∫ U,R.eval U*Ex (pend T τ F U D)∂η) ≤ p₀*(∫ U,R.eval U∂η) := by
   obtain ⟨V,Hh,hV⟩:= central T τ h hy hβ ht
   have hL:= expanse T τ hv h hy ht hx hb H hz V
   let z:=Z T R r τ 0 V; let l:=labor T R r τ t C F; let d:= D; have hz':0≤ z:=integral_nonneg fun _=> cell_nonneg ..; have ht(i:T.Cell): Envelope (vigor T R r τ F i):= (cell_env T τ h i).mul (he.bill i).exp
   have heZ(i): Envelope (l i):= (ht i).add (Envelope.const _); have hf i U: 0≤ l i U:= add_nonneg (mul_nonneg (cell_nonneg ..) (Real.exp_pos _).le) (Real.exp_pos _).le
   let f i:= Ex (P i)*(3*z)
   have hp i V: press (edges T i) (l i) V ≤ f i:=by
      unfold l labor; rw [House.press_add _ (ht i) (Envelope.const _), show press _ (fun _ :𝒞=> Ex (-a-ζ)) V= _ from House.markSpaces (f:=fun _=>Ex (-a-ζ)) (X:=edges T i) (fun _ _ _=>rfl) V]; unfold f; apply le_trans (add_le_add (le_trans (he.pays i V) (mul_le_mul_of_nonneg_left (show Z T R r τ i V ≤ 2*z by rw [← Z_turn T τ hv h]; exact Hh _) (Real.exp_pos _).le)) hV); change Ex (P i) * (2*z)+z ≤ _; nlinarith only [mul_le_mul_of_nonneg_right (Real.one_le_exp (he.pos i)) hz']
   have hZ (i) : fence (House.fullRoom T i) (l i) := fun U V hx=> by unfold l labor vigor; rw [cell_feet T τ hv h i _ _ hx, he.home i _ _ hx]
   have ha: (∫ U,(∏ i, l i U)∂η) ≤ ∏ i, f i:=by
      simpa only [mul_one,integral_const,probReal_univ,one_smul] using towards (X:=edges T) (u:=f) (f:=l) Finset.univ (w:=fun _=>1) (Envelope.const _) (fun _=>zero_le_one) (fun _ _ _ _ _=> rfl) (fun i _=> heZ i) (fun i _=> hf i) (fun i _=>hp i) (fun i _ j _ hij => House.spares (hZ j) (Finset.disjoint_left.mpr (fun _ hx hy => hij (House.splits T hv hx hy |>.symm))))
   let D':=Ex (R.scalar+fᵣ); let a₀(V):= Ex (pend T τ F V D); let c₀ (i U):= Ex (cup T R r i U + order T τ F i U D)
   have ht' i U: c₀ i U ≤ l i U:= by
      unfold c₀ order; split_ifs with ha
      · unfold l labor vigor cell tape gaugeW; rw [if_pos ha,mul_one,Real.exp_add]; exact le_add_of_nonneg_right (Real.exp_pos _).le
      apply le_trans ?_ (show Ex (-a-ζ) ≤ l i U from le_add_of_nonneg_left (mul_nonneg (cell_nonneg ..) (Real.exp_pos _).le))
      have hu := (abs_le.mp (cup_bound T h i U)).2; change _≤ Ex _; apply Real.exp_monotone; unfold premium; linarith only [hu]
   have hu(U): R.eval U*a₀ U≤ D'*(∏ i,l i U):= by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _=> (Real.exp_pos (cup T R r i U+order T τ F i U D)).le) (fun i _=> ht' i U)) (Real.exp_pos _).le)
      have h₀: R.eval U≤ Ex (R.exponent U):= by refine le_trans (b:=Ex (R.exponent U)*1) (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le) ?_; exacts [(show R.activities.gas R.p U≤ 1 from (abs_le.mp (SectorNext.Vacuum.gas_le_one R.activities hw H.labels U)).2),(mul_one _).le]
      apply le_trans (mul_le_mul_of_nonneg_right h₀ (Real.exp_pos _).le)
      unfold D' pend; rw [← Real.exp_add, ← Real.exp_sum,Finset.sum_add_distrib,← Real.exp_add]; exact Real.exp_monotone (by linarith only [(abs_le.mp (surface T hv h U)).2])
   apply le_trans (integral_mono (((R.envelope H).mul (playEnv T he.bill D τ).exp).integrable η) (((House.branch Finset.univ l fun i _=> heZ i).integrable η).const_mul D') hu)
   rw [integral_const_mul]; apply le_trans (mul_le_mul_of_nonneg_left ha (Real.exp_pos _).le) (((le_of_eq ?_).trans (mul_le_mul_of_nonneg_left hL (Real.exp_pos _).le)))
   change D'*(∏ i, f i) = _
   unfold f z D' graphRate; rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.prod_const,Finset.card_univ, mul_pow,← mul_assoc,← mul_assoc, ← mul_assoc,← Real.exp_log (by norm_num : 0 < (3:ℝ)), ← Real.exp_nat_mul]; -- log in exponent rewrites 3! inspect
   repeat rw [← Real.exp_add]
   congr 2 <;> first|rw [Real.log_exp]; ring| ring
end YM.OPE.Therm.Cradle
