import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionPassengerFiled
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShieldedPathAction

/-! The whole registered geometric and passenger action on a physical bond,
against the unmasked Wilson action on the same datum and coupling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local WilsonStartup
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{ι:Type*}
local notation "Fld" => Config G n

def fullPhysical (p:BudgetPoint)(c:Clip)(P:PathData G)(β:ℝ)
    (rank:ι→ℕ)(A:(v:ι)→ℕ→Atom G (rank v))(coef:ι→ℝ)(L:List ι)(W:Fld):ℝ:=
  P.inChannels c p β W+(L.map (fun v=>physicalPassenger (A v) p (coef v) W)).sum

def fullIndependent (c:Clip)(P:PathData G)(β:ℝ)
    (rank:ι→ℕ)(A:(v:ι)→ℕ→Atom G (rank v))(coef:ι→ℝ)(L:List ι)(W:Fld):ℝ:=
  β*mainTerm c P W+Precision.loop P W+(L.map (fun v=>coef v*wilsonOrbit (A v) W)).sum

def passengerCash (rank:ι→ℕ)(σ C:ℝ)(coef:ι→ℝ)(D:ℕ)(L:List ι):ℝ:=
  (L.map (fun v=>|coef v| *(2*atomCash (rank v) σ C D))).sum

private theorem folded_price {X:Type*}(f g M:X→ℝ)(L:List X)(paid:∀v∈L,|f v-g v|≤M v):
    |(L.map f).sum-(L.map g).sum|≤(L.map M).sum:=by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [show f v+(L.map f).sum-(g v+(L.map g).sum)=(f v-g v)+((L.map f).sum-(L.map g).sum) by ring]
    exact (abs_add_le ..).trans (add_le_add (paid v (List.mem_cons_self)) (ih (fun j h=>paid j (List.mem_cons_of_mem _ h))))

/-- No global flag exclusion or positive lower bound for any gas or partition.
All Wilson emissions are the uncontracted same-datum orbit, with the actual
signed coefficient supplied outside its physical guarded representation. -/
theorem complete_physical_mask_price (p:BudgetPoint)(c:Clip)(P:PathData G){σ C Λ σ' L₀:ℝ}
    (pay:P.Bounds c σ C Λ)(licensed:Decent c p)(β:ℝ)(rank:ι→ℕ)
    (A:(v:ι)→ℕ→Atom G (rank v))(coef:ι→ℝ)(L:List ι)(width:0<σ')
    (stock:∀v∈L,SumBudget (fun i=>(A v i).budget σ') L₀)
    (reset:∀v∈L,∀h:rank v=2,zeroContact (h ▸ A v))
    (e:Edge (Site n))(D:ℕ)(U V:Fld)(out:∀b:Edge (Site n),b≠e → U b=V b)
    (cold:Healthy p.threshold (halo (D+p.B) {e.1}) U)(after:e.1∉flags p.threshold V):
    |(fullPhysical p c P β rank A coef L U-fullIndependent c P β rank A coef L U)-
     (fullPhysical p c P β rank A coef L V-fullIndependent c P β rank A coef L V)|
    ≤pathCash σ C Λ β D+passengerCash rank σ' L₀ coef D L:=by
  let g:ι→Fld→ℝ:=fun v W=>physicalPassenger (A v) p (coef v) W-coef v*wilsonOrbit (A v) W
  have sum_eq(W:Fld)(L':List ι):fullPhysical p c P β rank A coef L' W-fullIndependent c P β rank A coef L' W=
    pathMask P c p β W+(L'.map (fun v=>g v W)).sum:=by
    unfold fullPhysical fullIndependent pathMask
    induction L' with
    | nil=>simp
    | cons a l ih=>
      simp only [List.map_cons,List.sum_cons]
      simp only [g] at *;linarith only [ih]
  have bank:Healthy p.threshold (halo D {e.1}) U:=by
    apply disjoint_left.mpr;intro x hx hot
    obtain ⟨y,hy,near⟩:=halo_spec.mp hx
    exact disjoint_left.mp cold (halo_spec.mpr ⟨y,hy,near.trans (Nat.le_add_right ..)⟩) hot
  have paths:=original_path_mask_price p c P pay licensed β e D U V out cold after
  have bills:=folded_price (fun v=>g v U) (fun v=>g v V)
    (fun v=>|coef v| *(2*atomCash (rank v) σ' L₀ D)) L
    (fun v hv=>physical_passenger_price (A v) width (stock v hv) (reset v hv) p (coef v) e D U V out bank after)
  rw [sum_eq,sum_eq,show ∀a b d f:ℝ,a+b-(d+f)=a-d+(b-f) from fun _ _ _ _=>by ring]
  exact (abs_add_le ..).trans (add_le_add paths bills)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
