import YM.X.Gravity.Tunic
import YM.X.Gravity.Landing
/-!
# Aperture contour equation. Local FO ribbon harvest and CT purchase absorb. Does *not* give regulator matching yet. ∗No assumptions on ker beyond actual repaint∗. Correction bill budget at weight.; obtains ∗convergence under all released exterior directions, before coupling∗.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark Bare
open Stems hiding X
open Pert.RawLabels
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "Ψ"=> Book G
local notation "e"=>epsilon q
variable {F:Labels.Frames G}(s:Shop F)(P:Word G)(φ:Floor R)
local notation "D"=>P.d
local notation "E"=> Pert.Position.E F
variable {A:ℕ→Brush G}
lemma snap_cost (h:Tide q r A)(p:Curly G): Charged q (fun i=> snap (A i) p):= by
   induction p using MvPolynomial.induction_on with
   | C x=> simp only [snap,aeval_C]; exact Charged.constant _
   | add a b x y=>simp_rw [map_add];exact Charged.add x y
   | mul_X p i IH=>
       simp_rw [map_mul, show ∀ A:Brush G,snap A (MvPolynomial.X i)=Complex.ofReal (text A i) from fun A=> by rw [snap,MvPolynomial.aeval_X]]; apply Charged.mul IH; let f:Fan G:= Finsupp.single i 1; obtain ⟨c,hc,ht⟩:= h.amounts 0 f (by rw [grade0];simp); refine ⟨ -(1:ℕ), Ripe.eventual (B:=c) ?_⟩; filter_upwards [ht] with k hk; specialize hk 0 (by simp [Beamer.empty_road]); rw [leads_zero] at hk; rw [Complex.norm_real,ticket_neg,pow_one,← flat₁]; simpa only [Nat.zero_add,pow_one, pow_zero,mul_one,Real.norm_of_nonneg (epsilon_pos q _|>.le)] using! hk
lemma correction {T:Submodule ℂ (Curly G)} (h:Tide q r A){f:ℕ→Curly G}(hf:f∈ Badge (Curly G) (Vanished q) T): Vanished q (fun i=>snap (A i) (f i)):= by
   induction hf using Submodule.span_induction with
   | mem p he=> obtain ⟨a,z,ht,hz,rfl⟩:=he; simp_rw [map_smul]; exact Vanished.left ht (snap_cost h z)
   | zero=> simp only [Pi.zero_apply,map_zero]; exact Vanished.zero
   | add a b _ _ x y=> simp_rw [Pi.add_apply,map_add]; exact Vanished.add x y
   | smul a b _ x=> simp_rw [Pi.smul_apply,map_smul]; exact Vanished.right (Charged.constant a) x
lemma kills [AddCommGroup V][Module ℂ V] {f:ℕ→ V}(h:f∈Badge V (fun z=>z∈fades ℂ) ⊤)(H:ℕ→Module.Dual ℂ V)(he:∀ v,(fun i=>H i v)=O[L] (fun _=> (1:ℝ))) : Tendsto (fun i=> H i (f i)) L (𝓝 0):= by
   induction h using Submodule.span_induction with
   | mem g hg=>
       obtain ⟨a,v,ht,hp,rfl⟩:= hg; simp only [map_smul,smul_eq_mul]; let A(k:ℕ):= a k * (H k v)
       have hl: (A =O[L] (fun k=>‖a k‖)) := by
           have hx:= (he v); rw [← isBigO_norm_left] at hx; let c(k:ℕ):= ‖a k‖; apply isBigO_norm_left.mp; unfold A; simp_rw [norm_mul]; rw [← show c * (fun k:ℕ=> (1:ℝ)) = (fun k=> ‖a k‖) from funext (fun i=> by simp [c])]; exact (isBigO_refl c L).mul hx
       exact hl.trans_tendsto (by simpa using! (fading ht).norm)
   | zero=>simp_rw [Pi.zero_apply,map_zero];exact tendsto_const_nhds
   | add a b _ _ x y=>simp_rw [Pi.add_apply,map_add];simpa only [add_zero] using! x.add y
   | smul a b _ x=> simp_rw [Pi.smul_apply,map_smul];simpa only [smul_zero] using! x.const_smul a
include hq
lemma hush (hv:0≤R)(hr:R<r)(ha:Tide q r A){B:Rich G}(hp:Grasp B)(ht: Fill (gate q r) (fun i=>e i^(d+1)) d 0 A (emerge q B))(x:E d):
    (fun i=> e i ^ (-((d+1:ℕ):ℤ)) • (snap (A i) (matchP s q i d x)-shineP (emerge q B i) d (matchSelf s d x)))=O[L] (fun _=> (1:ℝ)):= by
   let f:=matchSelf s d x; let g(i):= matchP s q i d x - f; let z(i):= snap (A i); let v(i):= probeL (emerge q B i); let b:= ((d+1:ℕ):ℤ); let c(i):=e i ^ (-b); let r₁(i):= snap (A i) f-shineP (emerge q B i) d f
   have hr : r₁=O[L] (fun i=>e i ^ b):= motion (root_core hq hv ha hr hp ht (stead f)).2
   have he(i): c i * e i ^ b=1:= by unfold c; rw [zpow_neg,inv_mul_cancel₀ (zpow_pos (epsilon_pos q i) b|>.ne')]
   have HX : (fun i=> c i • r₁ i) =O[L] (fun _=> (1:ℝ)):= ((isBigO_refl c L).smul hr).congr_right he
   have hz : Vanished q (fun i=> c i • (z i (g i))):= eps_supp (correction ha (portion hq s x)); refine ((late hq hz).old.add HX).congr_left (fun i=>?_); unfold g r₁ z; rw [map_sub,←smul_add]; unfold f c b; congr 1; abel
end YM.PositionX.Gravity
