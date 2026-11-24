import YM.QuadraticLocal.Tariff.Warranty
import YM.QuadraticLocal.Relative.Ginger
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Tariff
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Annuncia RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V W : Type} [DecidableEq V] [Fintype V][DecidableEq W][Fintype W]
variable (u:W→ V) (R: Census V) (o : V→Site n)
local notation "S"=> (Annuncia.Replica u R)
local notation "ϕ"=> ( Annuncia.Replica.bill u R )
variable (γ:(Replica u R).Mode→ℂ)
variable (w:V→ℝ)(hw:∀ i,0<w i)
variable {T J η : Type*} {a b c δ ε :ℝ}{B B' :ℕ}
local notation "ν"=> ( w ∘ u )
open Next.Foundations
variable (g:W→ℂ) (C:W→ℝ)(hC:∀ i, ‖g i‖ ≤ C i)(hP:∀ i,C i≤1)
local notation "ψ"=> ( Replica.sign u R g )
local notation "Ψ"=> ( Tariff.exposes u R g )
local notation "κ"=> ( Tariff.levy u R C )
local notation "s!" s:max=> (Tariff.factor C s)
include hC
variable (U:Set (Replica u R).Mode)(V₀: Finset W) (Δ:T→η)
variable (L:Lamps η J G p (o∘u) (Replica u R))
variable {P : ℕ→ ForcedAddress G n} {F : Code G n} (H: Hard η p P F (o∘u) (Replica u R))
variable (hU:∀ i∈U, V₀ ⊆ i.val)(hE:∀ i∈U,∀ j∈i.val, j∉V₀→ C j ≤ 1)
include hU hE
-- any amplitudes marked, paying all masses at LARGE COST. Cost only at other declared stencil points. No assuming processing with estimates weakened because amplitude huge; the projections reuse a common Witness Frame across all amplitudes.Banks vectors.Sem.E
lemma localPay (i:(S).Mode): κ U i ≤ s! V₀:=by
    unfold Tariff.levy; split; next h=>
       rw [← Finset.prod_sdiff (hU i h)]; apply mul_le_of_le_one_left (purse g C hC _); exact Finset.prod_le_one (fun i _=> (norm_nonneg _).trans (hC i)) (fun j hv=>hE i h j (mem_sdiff.mp hv).1 (mem_sdiff.mp hv).2)
    next=> exact purse g C hC _
local notation "M!"=> (emit u R o (Ψ U) Δ L)
include hw
lemma earnsE (h:L.Paid (w∘u) B a b): (M!).Paid w B a (( Tariff.factor C V₀ )*b):= by exact Tariff.energy u R o (Ψ U) w hw Δ L (κ U) (supports u R g C hC U) (localPay u R g C hC U V₀ hU hE) (purse g C hC _) h
lemma earnsK (h:H.Paid (w∘u) B a b): (Tariff.grains u R o (Ψ U) Δ H).Paid w B a (( Tariff.factor C V₀ )*b):= by exact Tariff.token u R o (Ψ U) w hw Δ (κ U) (supports u R g C hC U) (localPay u R g C hC U V₀ hU hE) (purse g C hC _) H h
-- Authentic old-Mark factors. ξPad.`keeping other Marker selected Op.O separate.
-- When deallocating on Θ valuations, Price can for all unainted-only interactions including Boot from semantic entitlement be determined solely from *Clean-energy* stamp. No uniqueness assum.
variable (Z:Set W)
def attentive (Z:Set W) : Set (Replica u R).Mode:= { i | Deletion.preserve i.val Z }
lemma repair (h: (Deletion.sink Z L).Paid (w∘u) B a b) (hz:U ⊆ Tariff.attentive u R Z): (M!).Paid w B a (( Tariff.factor C V₀ )*b):= by
    rw [show (M!)= emit u R o (Ψ U) Δ ( Deletion.sink Z L ) from ?_]; exact earnsE u R o w hw g C hC U V₀ Δ (Deletion.sink Z L) hU hE h
    unfold emit Deletion.sink; congr 1; funext t i; dsimp only; split; exact rfl; next h=> simp_rw [exposes,if_neg (show L.mode i∉U from fun v=> h (hz v : _))]; rw [zero_smul,zero_smul]
omit hU hE
include hP
lemma away (h:∀ i∉Z, C i≤ ε)(V:(Set (Replica u R).Mode))(he:V ⊆ (Tariff.attentive u R Z)ᶜ) (hp:0≤ ε)(i:(Replica u R).Mode) : κ V i ≤ ε:= by
    by_cases hI:i∈V; swap; · rw [Tariff.levy,if_neg hI]; exact hp
    have hF:= he hI; simp only [Set.mem_compl_iff, Tariff.attentive,Set.mem_setOf_eq, Deletion.preserve, Classical.not_forall] at hF; -- yields exist j, not _
    obtain ⟨j,hF⟩:= hF;  -- into ∧? check
    obtain ⟨hv,hj⟩:=hF;
    apply le_trans (b:= Tariff.factor C {j}) _ (?_: Tariff.factor C ({j})≤ ε );
    · rw [Tariff.levy,if_pos hI,← Finset.mul_prod_erase _ C hv]; have hE: factor C {j}=C j:=by simp [factor]
      rw [hE]; exact mul_le_of_le_one_right ((norm_nonneg _).trans (hC j)) ( Finset.prod_le_one (fun i _=> (norm_nonneg _).trans (hC i)) (fun i _=> hP i) )
    simpa only [Tariff.factor, prod_singleton] using h _ hj
-- Full cost in representation with true amplitudes (if reattaching old Marketing discrepancies wanting qelt). E regular projected at ONCE for all monomials, no dropping partners.Y.S;
-- if all leaders outside Z with small price, use Clean witness + hOld. Keep same G'}
open Next.Foundations
omit hC hP -- deterministic.
lemma add_bill (hb: (Tariff.emit u R o (Ψ U) Δ L).Paid w B a b) (hc: (Tariff.emit u R o (Ψ (Uᶜ)) Δ L).Paid w B a c): (Tariff.emit u R o ψ Δ L).Paid w B a (b+c):= by
    obtain ⟨f,hf,hF,hB⟩:= hb.budget; obtain ⟨h,hT,hθ,hH⟩:= hc.budget; let A:= emit u R o ψ Δ L; let A1:= emit u R o (Ψ U) Δ L; let A2:= emit u R o (Ψ (Uᶜ)) Δ L; let F i:= f i+h i; refine ⟨F,fun i=> add_nonneg (hf _) (hT _), ?_,fun i=> ?_⟩; ·
       intro i t v hv; rw [Tariff.publication u R o g U Δ L i t]; exact bound_add (A1.legal t i) (A2.legal t i) (hF i t v hv) (hθ i t v hv)
    -- Sum across modes. Budget.Health
    have hp (j:J): (if i∈A.ground j then (Poly.toll w (A.mode j)*F j)*Real.exp (a*coverNumber B (A.ground j)) else 0)=(if i∈A.ground j then (Poly.toll w (A.mode j)*f j)*Real.exp (a*coverNumber B (A.ground j)) else 0)+(if i∈A.ground j then (Poly.toll w (A.mode j)*h j)*Real.exp (a*coverNumber B (A.ground j)) else 0):= by unfold F; split; ring; rw [add_zero]
    convert budget_plus (hB i) (hH i) using 1; exact funext hp
include hC hP
lemma enhanced (h:∀ i∉Z,C i≤ε)(hp:0≤ε)(h1 :L.Paid (w∘u) B a b) (h2:(Deletion.sink Z L).Paid (w∘u) B a c): ( Tariff.emit u R o ψ Δ L ).Paid w B a (c + ε*b):= by
    let HZ:= (Tariff.attentive u R Z); let F1:= repair u R o w hw g C hC HZ ∅ Δ L (fun i _=> Finset.empty_subset _) (fun i h j _ _=>hP j) Z h2 (fun i hi=>hi); -- orientation
    have hv: ( Tariff.emit u R o (Ψ HZ) Δ L ).Paid w B a c:=by simpa only [factor, prod_empty, one_mul] using! F1
    exact Tariff.add_bill u R o w hw g HZ Δ L hv (Tariff.energy u R o ( Ψ HZᶜ ) w hw Δ L (κ HZᶜ) (supports u R g C hC HZᶜ) (away u R w hw g C hC hP Z h HZᶜ (fun i hi=>hi) hp) hp h1)
end YM.QuadraticLocal.Tariff
