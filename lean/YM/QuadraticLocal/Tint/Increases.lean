import YM.QuadraticLocal.Travel
import YM.QuadraticLocal.Tint.Boost
/-!
 # Paying relative price on the registered log rows.
 Uses already compact root tests; boost carried with all Aura.B.Value intervals
 including opaque test bounds. F(point-of-origin) binding included for kernels.
 Two applications later: (1) all previous residual lamps, (2) riding long
 **model** occurrences. Both use actual stencil registrations and use no fake
 vacuum occupation. This receipt immediately controls optional *reading* in same
 stamped period for all sign pairs. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Pressure Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open PhysicalNext PhysicalNext.Repeat AnalyticBridge.VerifiedReset Progress.DirectedRecipe
open RemainderComparison
namespace Travel.Winter
open QuadraticLocal.Travel
variable {I V:Type}{G: Gauge}{n c L:Side}{x v e κ w a b d q z:ℝ}{α:Type*}
variable {A0:Teller G}{Q:ConnectedActivityE6.Target G A0}{Horizon:ConnectedActivityE6.Target.Order G w}
variable {S:StepData c n}{D:Pressure.Tube G S}{P:Rep G n}{P':Rep G c}
open ConnectedActivityE6
variable (H:Cash w x κ L Q Horizon z D P)
open Lyric Muse Serif Spire Push.SectorMeasure
variable {A B M : ℝ}
local notation "θ₀"=> P.p.supportExponent
open Merge Lotus Trigger Typeface
variable [DecidableEq V]{R:Marker.Census V}{o:V→Site n}
variable {Y Γ K : ℝ} {k k' : ℕ}
variable (Iris:Eyes H P' e Γ Y K k)
open scoped Classical BigOperators
variable (L0:Gallery α I o P R)(σw:V→ℝ)
local notation "L₀"=> L0.E
variable {b':ℝ}
variable (U:Seal L0 σw b b')
variable (hw:∀ i,0<σw i)(hx:HasSlots P.p P.activities)
variable [Countable I]
variable (u:α)
local notation "A*"=> listCosts L0 σw hw hx U.supE U.crown (sighting L0 σw U) U.looks
local notation "Yp"=> brand A* u
local notation "l₀"=> (fun _ : Trigger.Table L0 × Bool=> (1:ℝ))
local notation "φ₀"=> (Poly.toll σw)

variable (T : Set I)
def hot (T : Set I) : Set (Trigger.Table L0 × Bool) := {i| i.fst.elim (fun j=> j.val ∈ T) (fun _=>False)}
variable (ht : 0<d)
variable (hp : Hit L0.E.ground P.p.B (fun i=> if i∈T then Poly.toll σw (L0.E.mode i)* U.supE i else 0) P.p.supportExponent A)
include hw hx ht hp U
local notation "E"=> Trigger.Table L0 × Bool
local notation "f₁"=> Creek.rage (Winter.hot L0 T) d (fun _=> 1)
local notation "Π"=> (Y^k) -- reserve k not used in capacity there
local notation "ξ"=> (2*( b+b') + 2*d⁻¹*A :ℝ)
lemma scale : Lyric.Scale id (fun i=>(Yp i).crest) (Yp) f₁ (Fintype.card (Site S.ratio.count)) θ₀ ξ S := by
    let Ω:= Yp; let t : Set (Trigger.Table L0):= {x| x.elim (fun j=>j.val∈T) (fun _=>False)}; let f:=f₁; let g:= U.supE
    let Z i:=(Ω i).crest; let i:= id (α:=Site n); let m :=Palette.wages Ω l₀; let m':=Palette.wages Ω f
    have hv:= Trigger.earned L0 S σw hw hx U.supE U.crown (Travel.sighting L0 σw U) U.looks U.payment u
    have hz (j: Trigger.Table L0×Bool): f j=(if j.fst∈ t then d⁻¹ else 1):=mul_one _
    have he j: 0≤ f j:=by rw [hz]; split; exact (inv_pos.mpr ht).le; exact zero_le_one
    have hM j:0≤ m j:=mul_nonneg zero_le_one ((Ω j).profit); have hN j:m' j=f j*m j:=by unfold m' m Merge.Palette.wages; simp
    have hf': 0≤ A:= budget_nonneg (hp 0); have hz':0≤ξ:= add_nonneg hv.tolerance (mul_nonneg (mul_nonneg zero_le_two (inv_pos.mpr ht).le) hf')
    refine ⟨he, ?_, ?_, hz', hv.sizes⟩
    · intro j h; change 0< m' j at h; rw [hN] at h; exact hv.pin _ (pos_of_mul_pos_right h (he _))
    intro x; let Y : Trigger.Table L0→Support n := fun j=> Z (j,true); let g' j:=m (j,true)
    have hY j:Z j=Y j.1:= (Trigger.wingE L0 hx j.1 j.2).trans (Trigger.wingE L0 hx j.1 true).symm
    have hh(j:E):m j=g' j.1:=rfl
    let μ(j:E):=if x∈Z j then Real.exp (θ₀*(coverNumber P.p.B (Z j):ℝ))*m j else 0
    let z':Trigger.Table L0→ℝ:=fun i=>if x∈Y i then (if i∈t then Real.exp (θ₀*(coverNumber P.p.B (Y i):ℝ))*g' i else 0) else 0
    have hU : SumBudget μ (2*(b+b')):= by convert hv.crown x using 1; ext j; unfold μ; split<;> rfl
    have he' : SumBudget z' A:=by
       let f(j:Fires L0):= j.val; let W(j:Fires L0):= if x∈ (L₀).ground j.val then (if j.val∈T then φ₀ ((L₀).mode j.val)* g j.val else 0)* Real.exp (θ₀ * coverNumber P.p.B ((L₀).ground j.val)) else 0
       refine Progress.DirectedRecipe.transfer_budget (t:=⟨Sum.inl,Sum.inl_injective⟩) (g:=W) ?_ ?_ (budget_pull (b:=Subtype.val) Subtype.val_injective (hp x)) -- arg name
       · intro i; have h:Y (Sum.inl i)=(L₀).ground i.val:= Trigger.wingE L0 hx (Sum.inl i) true; change z' (Sum.inl i)=W i; unfold W z'; rw [h]; split; next=>
            split_ifs with h₀ ha ha <;> first | exact (ha h₀).elim | exact (h₀ ha).elim | skip
            · change _*( (1:ℝ)*_) = _; rw [one_mul]; exact mul_comm ..
            · rw [zero_mul]
         next=>rfl
       rintro (i|i) h; exact (h ⟨_,rfl⟩).elim; unfold z'; rw [if_neg (show _ ∉ t from (id : False→False))]; split<;>rfl
    have hB: SumBudget (fun j:E=> d⁻¹*z' j.fst) (2*d⁻¹*A):= by
       have hy:= budget_scale (inv_pos.mpr ht).le (budget_prod he' (show SumBudget (fun _ : Bool=> (1:ℝ)) 2 from budget_finite (fun _=>zero_le_one) (by simp))); simpa only [mul_one] using! budget_loosen hy (le_of_eq (show _ = 2*d⁻¹*A from (by ring)))
    refine budget_mono (budget_plus hU hB) ?_ fun i=>?_
    · intro i; split; next=> exact mul_nonneg (Real.exp_nonneg _) (mul_nonneg (he i) (Ω i|>.profit))
      next=> exact le_rfl
    dsimp only; split; next hp'=>
       change x∈ Z i at hp'; change Real.exp (θ₀*coverNumber (P.p.B) (Z i))*m' i≤ _
       by_cases hh':i.1∈ t; · have hx: x∈ Y i.1:= hY i ▸ hp'; refine le_trans (le_of_eq ?_) (le_add_of_nonneg_left (hU.1 i)); unfold z'; rw [if_pos hx,if_pos hh',hN,hz,if_pos hh',hY i,hh i]; ring
       exact le_trans (le_of_eq (show _= μ i from (by rw [hN,hz,if_neg hh',one_mul]; unfold μ; rw [if_pos hp']))) (le_add_of_nonneg_right (hB.1 i))
    next=> exact add_nonneg (hU.1 i) (hB.1 i)
-- Billing book occupancy.G proof not assuming BudgetLp._S.
include Iris
lemma hikes (he:2*(b+b') + 2*d⁻¹*A≤K): Motto (brand A* u) f₁ 0 H θ₀ K Y (Eyes.sight Iris):= by
    let M:= Travel.Winter.scale L0 σw U hw hx u T ht hp (S:=S)
    refine ⟨?_,Iris.grant,le_rfl,by simp,by simp⟩
    let q := brand A* u; exact ⟨Site n,inferInstance,id,(fun i=> (q i).crest), M.currency,M.pin, (fun i=>budget_loosen (M.crown i) he), M.tolerance.trans he, (fun j=> (parentCost S j).trans Iris.count)⟩
end Travel.Winter
end YM.QuadraticLocal
