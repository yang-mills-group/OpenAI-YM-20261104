import YM.QuadraticLocal.Tariff.Pins
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
lemma transfers (s:(S).Mode)(x:V): x∈(ϕ s).val ↔ ∃ i∈s.val,u i=x:= Finset.mem_image
-- -- redeclare γ? use explicit.
variable (Δ:T→η) -- fix
-- Ψ.Tint Gamma height priori.M.Entry labels unchanged (addresses), Root location step requires clone equality). Scale by arbitrary ℂ; here not requiring Poly pass for selective parts.
def emit (L:Lamps η J G p (o∘u) ( Replica u R )): Lamps T J G p o R where
   mode i:= Replica.bill u R ( L.mode i )
   live i:= fun hi=> L.live i (( Replica.hot u R _ ).mp hi)
   address:= L.address
   roots i v h:=by obtain ⟨j,hj,rfl⟩:= (Tariff.transfers u R _ _).mp h; exact L.roots i _ hj
   nominal x i:= γ (L.mode i) • L.nominal (Δ x) i
   legal x i:= regular_smul _ (L.legal _ _)
   clear:= L.clear
   pure t i U he:= by simp only [Pi.smul_apply]; rw [L.pure _ i U he]
variable (L:Lamps η J G p (o∘u) ( Replica u R ))
local notation "M"=> ( Tariff.emit u R o γ Δ L )
lemma transform (i)(t:T)(U:Config G n): ( M ).light t i U=γ (L.mode i)* L.light (Δ t) i U:= by
    unfold Lamps.light; dsimp only [emit,Lamps.ground,smul_eq_mul]; split; rfl; unfold masked; simp only [Set.indicator]; split; rfl; exact (mul_zero _).symm
lemma spray (s:(S).Mode) (x:ℂ): pay u R γ (Poly.send s x )= Poly.send (ϕ s) (γ s*x):= by
    ext1 i; rw [quota,sum_eq_single_of_mem s (mem_univ _), Poly.part_send, Poly.part_send]; rotate_left
    · intro b hb hh; split; rw [Poly.part_send,if_neg hh,mul_zero]; rfl
    simp only [if_true, ↓reduceIte]; by_cases h: i=ϕ s <;> simp_all only [ne_eq, eq_comm (a:=ϕ s) (b:=i), not_false_eq_true, ↓reduceIte] -- syntax
lemma frame (i)(t:T)(U:Config G n): (M).frame i t U= pay u R γ ( L.frame i (Δ t) U):= by unfold Lamps.frame; rw [transform,spray]; rfl
noncomputable def cable := LinearMap.toContinuousLinearMap ( pay u R γ )
local notation "ψ"=> ( Tariff.pay u R γ )
@[simp] lemma running (x:Poly (Replica u R)): Tariff.cable u R γ x= pay u R γ x:= rfl
include hw
lemma lightshow (h:L.Paid (w∘u) B a b) (ha:0≤a) (t:T)(U:Config G n) : ( M ).log t U= ψ (L.log (Δ t) U):= by
    rw [← running]; unfold Lamps.log; rw [(Tariff.cable u R γ).map_tsum (h.sums ha (fun i=> hw (u i)) ..)]; exact tsum_congr (fun i=> frame u R o γ Δ L _ _ _) -- hw omitted
-- EXPERT ♯ uniform budgets even if asking η quoted in advance. γ variation.Layer.Clock supported.Common allocation.Engine.*
variable (C: (Replica u R).Mode→ℝ)(hC:∀ i, ‖γ i‖ ≤ C i)
variable (hCL:∀ i, C i ≤ ε)(he:0≤ε)
include hC hCL he
lemma energy (h:L.Paid (w∘u) B a b): (M).Paid w B a (ε*b):= by
    obtain ⟨f,hf,hP,hV⟩:= h.budget; let g i:=C (L.mode i)*f i; have hg i:0≤g i:= mul_nonneg ( (norm_nonneg _).trans (hC _) ) (hf i); refine ⟨g,hg,fun i t v hv=> bound_weaken (bound_smul (γ (L.mode i)) ( hP i (Δ t) v hv )) (mul_le_mul_of_nonneg_right (hC _) (hf i)), fun i=> budget_mono (budget_scale he (hV i)) (fun j=> ?_) (fun j=> ?_) ⟩
    · split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hg _)) (Real.exp_pos _).le; exact le_rfl
    change ( if i∈L.ground j then Poly.toll w (ϕ (L.mode j))*g j*Real.exp (a*coverNumber B (L.ground j)) else 0) ≤ ε* _
    split; next h=> rw [← mul_assoc ε]; rw [← toll u R w]; let x := Poly.toll ν (L.mode j); let v:= Real.exp (a*coverNumber B (L.ground j)); exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hCL _) (hf j)) (show 0≤x from (Poly.worth (fun j=>hw (u j)) _).le)).trans_eq (mul_left_comm ..)) (Real.exp_pos _).le
    next=> rw [mul_zero]
-- Hard K bits, including each color.G separately.` portion leader. Π λ may be multiplied only for used gear. Returning by `.form` identity across weights amounts. Pay *all* basis terms, not after valuation.
omit hw hC hCL he
variable {P : ℕ→ ForcedAddress G n} {F : Code G n}
structure Grains (T:Type*) (p:BudgetPoint) (P : ℕ→ForcedAddress G n) (o:V→Site n) (R:Census V) where
   forced : T→ℕ→ Config G n→ Poly R
   local_ t i : Width.LocalCharge p o (P i).support (forced t i)
   supports t i U: forced t i U≠0→ (P i).eligible p.threshold U
namespace Grains
variable {R o}
variable (H:Grains T p P o R)
structure Paid (w:V→ℝ) (B:ℕ)(a b:ℝ):Prop where
    cover : ∃ f:ℕ→ Poly R, (∀ i t U, Width.Covered ( H.forced t i U ) (f i)) ∧ Hit (fun i=>(P i).support) B (fun i=>Poly.price w (f i)) a b
def ofHard (L:Hard η p P F o R): Grains η p P o R:= ⟨L.hard,L.locality,L.charged⟩
def toHard (u:∀ t i U,(H.forced t i U).part R.quiet=(F i U:ℂ)): Hard T p P F o R:=⟨H.forced,H.local_,H.supports,u⟩
end Grains
variable (H: Hard η p P F (o∘u) (Replica u R))
def grains : Grains T p P o R where
    forced t i:= fun U => Tariff.pay u R γ ( H.hard (Δ t) i U )
    local_ t i:= by
       let hx:= H.locality (Δ t) i; refine ⟨fun θ U=>congr_arg (ψ) (hx.gauge θ U), (Tariff.cable u R γ).continuous.measurable.comp hx.borel,fun U Z ht he=>congr_arg (ψ) (hx.reads U Z ht he),fun U I he i' ht=>?_⟩; contrapose! he; rw [quota]; refine sum_eq_zero fun j hj=>?_; split; next h =>
         obtain ⟨k,hk,rfl⟩:= ( Tariff.transfers u R j _ ).mp ( h.symm ▸ ht ); rw [show ( H.hard (Δ t) i U ).part j =0 from by_contra fun hv=>he (hx.carry U j hv k hk),mul_zero]
       exact rfl
    supports t i U h:= H.charged _ i U (fun hi=> h ( by rw [hi, map_zero]))
local notation "H!"=> ( grains u R o γ Δ H )
include hC hCL he hw
lemma token (h:H.Paid (w∘u) B a b): (H!).Paid w B a (ε*b):= by
   obtain ⟨f,hP,hx⟩:= h.wages; refine ⟨ ( fun i=> Tariff.charge u R C (f i) ), fun i v U=> Tariff.cap u R γ C hC _ _ (hP i (Δ v) U), fun i=> budget_mono (budget_scale he (hx i)) (fun j => ?_) (fun j=>?_) ⟩
   · split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
   split; next h=> rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right ( Tariff.area u R γ w hw C hC _ hCL ) (Real.exp_pos _).le
   next=> rw [mul_zero]
-- Π true K. quiet of λ id(0).
omit hC hCL he hw
variable (h0: γ (Replica u R).quiet=1)
include h0
lemma quiet (t:T)(i:ℕ)(U:Config G n): ( ( H! ).forced t i U ).part R.quiet=(F i U:ℂ):= by
    rw [show (H!).forced t i U = ψ _ from rfl, Tariff.quota]
    simp_rw [Replica.hot u R]; rw [Fintype.sum_ite_eq' _ _]; rw [h0,one_mul,H.quiet] -- syntax inspect
end YM.QuadraticLocal.Tariff
