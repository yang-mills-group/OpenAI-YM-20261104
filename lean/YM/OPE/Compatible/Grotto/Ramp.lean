import YM.OPE.Compatible.Grotto.Erl
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
variable {P:ℕ→Mints E→L[ℝ] Mints E}{X:Mints E→L[ℝ] Mints E}
noncomputable def strut (R:ℕ→ Mints E→L[ℝ] Mints E)(n:ℕ) : Mints E→L[ℝ] Mints E:=Nat.rec 1 (fun i a=> (R i)*a) n
lemma startEq (p:S!)(R:ℕ→ Mints E→L[ℝ] Mints E):∀ i,(race R 0 p i)=strut R i p:=by
     intro i; induction i with| zero=>rfl| succ i ih=> rw [gait R 0 p,ih,Pi.zero_apply,add_zero];rfl
def Lingo (r:ℝ)(P:ℕ→ Mints E→L[ℝ] Mints E): Submodule ℝ (Mints E) where
    carrier:={v|∃ C,Hex r (race P 0 v) C}
    zero_mem':=⟨0,(show Hex r (race P 0 (0:Mints E)) 0 from by intro i; rw [startEq,map_zero,norm_zero,zero_mul])⟩ -- dots
    add_mem':=by
       rintro v w ⟨c,h⟩ ⟨b,hb⟩; refine ⟨c+b,?_⟩; rw [show race P 0 (v+w)=race P 0 v+race P 0 w from funext fun i=>by rw [Pi.add_apply,startEq,startEq,startEq,map_add]]; exact Hex.add h hb
    smul_mem':=by
       rintro a v ⟨c,h⟩; refine ⟨‖a‖*c,?_⟩; rw [show race P 0 (a • v)=a • race P 0 v from funext fun i=>by rw [Pi.smul_apply,startEq,startEq,map_smul]]; exact Hex.tint h _
lemma switchL {P:ℕ→ Mints E→L[ℝ] Mints E}(v:Lingo r P):∃ C,Hex r (race P 0 v.val) C:=v.property
-- departure duty
variable [∀ i,CompleteSpace (G i)]
lemma speed (h:∀ i n,Assist T (L i n))(ha:1 ≤ a)(hv:0≤w)(hp:TameP 1 a 1 L)(hr:∀ i,ShadeR (T i) k r)(f:H→Mints E)(he:Wealth f a w)(hi:∀ i,f i∈Lingo r (L i)) : TameP r a w (sprint L f):=Folk h hp ha hv hr (fun _=>propel _ _) (zeroP a w r) he hi hr le_rfl
lemma appendP {T0 F:Type}[NormedAddCommGroup T0]{q:H→ℕ→T0}(y:F→H)(h:TameP r a w q): TameP r (a∘y) (w∘y) (q ∘ y):=by obtain ⟨c,⟨b,hc,k,H⟩,hc'⟩:=h; exact ⟨c∘y,⟨b,hc,k,fun i=>H (y i)⟩,fun i=>hc' (y i)⟩ -- inference
lemma closedL (hp:1≤ a)(ht:∀ i n,Assist T (L i n))(hv:TameP 1 a 1 L)(hr:∀ j,ShadeR (T j) k r)(hr':0 ≤ r)(i:H):IsClosed ((Lingo r (L i)): Set (Mints E)):=by
    let V:=Lingo r (L i); let s:V→H:=fun _=>i; obtain ⟨c,⟨C,hC,k,H'⟩,hx⟩:=speed (L:=L ∘ s) (fun _ n=> ht i n) (fun _=>hp i) (show (0:V→ℝ) ≤ (fun v:V=>‖v‖) from fun x=>norm_nonneg _) (appendP s hv) hr (fun j:V=> j.val) (show Wealth _ (a∘s) _ from ⟨1,zero_le_one,0,fun v=>by simp⟩ ) (fun i:V=>i.property)
    let b:=C*a i^k; suffices hv: (V:Set (Mints E))= ⋂ n:ℕ,{x:Mints E| ‖strut (L i) n x‖ ≤ b*‖x‖*r^n} by change IsClosed (V:Set (Mints E)); rw [hv]; apply isClosed_iInter; intro j; exact isClosed_le ((strut (L i) j).continuous.norm) ((continuous_const.mul continuous_norm).mul continuous_const)
    ext x; rw [Set.mem_iInter]; constructor
    · intro h n; let p:V:=⟨x,h⟩; have hp :Hex r (race (L i) 0 x) (c p):=hx p; show ‖strut (L i) n x‖≤ _; rw [←startEq]; apply (hp n).trans; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr' n); rw [← Real.norm_of_nonneg hp.price]; exact H' p
    intro hx; refine ⟨b*‖x‖,fun i=>?_⟩; rw [startEq]; exact hx i
end YM.OPE.Hark
