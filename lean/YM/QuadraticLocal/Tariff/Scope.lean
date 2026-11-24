import YM.QuadraticLocal.Earn.Passport
import YM.QuadraticLocal.Tariff.Grain
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
open Affinity
variable {Y':V→Type} [∀ i,AddCommGroup (Y' i)] {𝕜:Type} [RCLike 𝕜] [NormedAlgebra 𝕜 ℂ] [∀ i,Module 𝕜 (Y' i)]
variable (A:∀ i,Set (Y' i))(K:∀ i,Submodule 𝕜 (Y' i))
local notation "Up"=> ( fun i=> A (u i) )
local notation "Ew"=> ( fun i=> K (u i) )
local notation "Aw"=> Wallet (fun i=> A (u i))
-- tie projected Θ questions to test protocol.Mark read transactions require width.Value.Cl.Clock.Energy.
-- General algebra ℝ,ℂ. maybe issues with ISScalarTower 𝕜 arbitrary: Attn.K • over [NormedAlgebra], implies.
def draw (t:Wallet A): Wallet (fun i => A ( u i )):= fun i=> t (u i)
local notation "Δ"=> Tariff.draw u A
lemma respects {α:Type*} [NormedAddCommGroup α] [NormedSpace 𝕜 α] {g:Wallet ( fun i=>A (u i) )→α}(s:(Replica u R).Mode)(h: Affinity.Attn (fun i=>K (u i)) (fun i=>A (u i)) s.val g): Affinity.Attn K A (ϕ s).val (fun t=> g (Δ t)):= by
   refine ⟨ fun t t' he=> h.sit _ _ (fun i hi=> he (u i) (( Tariff.transfers u R s _ ).2 ⟨i,hi,rfl⟩)), ?_, fun i hi t he=>?_⟩
   · intro i hi; obtain ⟨j,hj,rfl⟩:= ( Tariff.transfers u R s _ ).1 hi; intro t x y z a b ht; have he(x:A (u j)): g (Δ (update t (u j) x))=g (update (Δ t) j x):=by
        apply h.sit; intro i hi; by_cases hb:i=j
        · subst i; simp [draw]
        have hh:u i≠u j:=fun hV=> hb ((Replica.admit u R s|>.separate) hi hj hV); rw [update_of_ne hb]; exact update_of_ne hh ..
     rw [he,he,he]; exact h.turns j hj (Δ t) x y z a b ht
   obtain ⟨j,hj,rfl⟩:= ( Tariff.transfers u R s _ ).1 hi; exact h.idle j hj (Δ t) he
lemma by_c (c:ℂ){g:Wallet A→ℂ}{s:Finset V}(h: Attn K A s g): Attn K A s (fun i=>c*g i):=by
   refine ⟨fun t t' he=> congr_arg (c*·) (h.sit _ _ he),fun i hi t x y z a b ht=>?_,fun i hi t ht=>?_⟩
   · rw [h.turns i hi t x y z a b ht, mul_add,mul_smul_comm,mul_smul_comm]
   rw [h.idle i hi t ht,mul_zero]
variable (D: V→ Support n) {P: ℕ→ ForcedAddress G n}{F:Code G n}
local notation "D'"=> (D ∘ u )
lemma taut {L:Lamps (Wallet (fun i=>A (u i))) J G p (o∘u) (Replica u R)}(h: Taut D' Up Ew L): Taut D A K (emit u R o γ ( Δ ) L):= by
    refine ⟨fun i v he=> ?_, fun i U=>by exact ( Tariff.by_c A K _ ( respects u R A K ( L.mode i ) ( h.adv i U ) ) )⟩
    obtain ⟨j,hj,rfl⟩:= (Tariff.transfers u R ( L.mode i) _).mp he; exact h.house _ _ hj
lemma crown {H: Hard (Wallet (fun i=>A (u i))) p P F (o∘u) (Replica u R)}(h: Crown D' Up Ew H): ∀ i U, Stencil D A K (P i).support fun t₀=> (Tariff.grains u R o γ (Tariff.draw u A) H ).forced t₀ i U:=by
    intro i U'; refine ⟨fun t=> ?_⟩; change Addressable D A K _ _ fun x=> (Tariff.pay u R γ _).part _; simp_rw [Tariff.quota]; apply Addressable.total; intro j hj; split
    next hh=>
        let he:= (h.lesson i U').each j; subst t; refine ⟨ Tariff.by_c A K (γ j) (Tariff.respects u R A K j he.advice),fun i' hτ v hv=>?_⟩
        obtain ⟨k,hk,rfl⟩:=(Tariff.transfers u R j _).1 hv; exact he.announces (Δ i') (right_ne_zero_of_mul hτ) k hk
    next=> exact Addressable.gone
-- clone passports. No deleting old alternatives of tests at this expansion.W.L. FRAME geometry Art.Actor T.Up
variable (X: Earn.Passport n V)
def clone : Earn.Passport n W where
    origin:= X.origin ∘ u
    support:= X.support ∘ u
    wire:= X.wire ∘ u
    height:= X.height ∘ u
    born i:= X.born (u i)
    visits i:= X.visits (u i)
    room i:= X.room (u i)
variable {c':Side}
lemma coarser (L:Ratio c' n): (clone u X).coarser L= clone u (X.coarser L):= rfl
end YM.QuadraticLocal.Tariff
