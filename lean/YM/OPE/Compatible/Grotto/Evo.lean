import YM.OPE.Compatible.Grotto.Gad
/-!
# Angular phase spectra.Lifting station members multilinearly. erased.B.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap Asymptotics
open scoped Topology BigOperators Classical
variable {d k i j s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b r x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
variable {p:(∀ i:Fin s,E i) →L[ℝ] (∀ i:Fin s,E i)}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{W:Fin s→Type}{a w:H→ℝ}{f g:H→ℕ→ Mints E}
variable {X:Mints E→L[ℝ] Mints E}
lemma fixedT (A:Mints E→L[ℝ] Mints E)(a:H→ℝ): TameP 1 a 1 (fun _=> Ford A):=by
    refine ⟨fun _=>‖A‖,⟨‖A‖,norm_nonneg A,0,fun i=>by simp⟩,fun i j=>by simp [Ford]⟩
abbrev Vapor (X:Mints E→L[ℝ] Mints E)(x:H→ Mints E):=fun i:H=>tale X (x i)
lemma pureW (u:ℝ)(hu:0 ≤ u)(hz:r>u)(p:H→ Mints E)(hp:∀ i,p i∈Fruition X u)(ht:Wealth p a w): TameP r a w (Vapor X p):=by
    obtain ⟨c,hc,H⟩:= AltE X u s hu hz; refine ⟨_,scaleD (k:=c) (normW ht),fun i=>?_⟩; exact H _ (hp i)
-- Euler step
variable (hp:1 ≤ a)(hw:0 ≤ w)(ht: TameP u a 1 (fun i=> L i - Ford X))
variable (hb:∀ i,ShadeR (T i) k r)
variable (hR: Assist T X)
variable {θ:ℝ}
lemma filings (T:Mints E→L[ℝ] Mints E)(x y:H→Mints E): Vapor T (x+y)=Vapor T x+Vapor T y:=funext fun i=> funext fun n=>map_add (T^n) (x i) (y i)
include ht
lemma Trade (hp:0≤ u)(hx:0≤r)(hb:r*u≤θ)(hr:TameP r a w g):
   let D: H→ℕ→Mints E:= fun i n=> L i n (g i n)-X (g i n)
   TameP θ a w D:=by
        intro D; exact TameP.grows (show TameP (r*u) a w D from hr.byOp ht) (mul_nonneg hx hp) hb
omit ht in
lemma periodZ (h:∀ i,Run (L i) (g i) 0)(T:Mints E→L[ℝ] Mints E)(p:H→Mints E): ∀ i, Run (Ford T) ((g-Vapor T p) i) (fun n=> L i n (g i n)- T (g i n)):=by
     intro i n; rw [Pi.sub_apply,Pi.sub_apply,h,show Vapor T p i (n+1)= T (Vapor T p i n)+0 from TALE T (p i) n]; simp only [Pi.zero_apply,add_zero]; change _= T ((g i-Vapor T p i) n)+(L i n (g i n)-T (g i n)); rw [Pi.sub_apply,map_sub]; abel -- derivative
omit ht
end YM.OPE.Hark
