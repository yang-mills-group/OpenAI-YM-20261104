import YM.Frontier6.Bouquet.Anise.Coffer

/-! Multiset of slot steps; preserve other variables' steps when importing one
 operation on tests. This avoids needing to decompose into product tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q:Place}[FiniteDimensional ℝ P][FiniteDimensional ℝ Q]{f:Full Q}(h:P≤Q){s r R A B:ℝ}{X Y:Set Room}{i j k d:ℕ}
namespace Checks
variable (hC:Checks Q X f d A)
include hC
lemma lowerCost (h:d ≤ i)(h':Checks Q X f i B) : Checks Q X f d B:=fun s hs=> h' s (le_trans hs h)
lemma low (he:i≤d): Checks Q X f i A:=fun v hv=> hC v (le_trans hv he)
lemma dir_shrinks (he:Y ⊆ X): Checks Q Y f d A:=fun v hv hp=> hC v hv (fun i hi=> he (hp i hi))
lemma cost_mono (he:A≤B): Checks Q X f d B:= fun v hv hp x=> (hC v hv hp x).trans he
lemma bound_restrict (z:Q)(he:Y⊆ X)(hp:Y⊆ (P:Set Room)): Checks P Y (restrictS h z f) d A:=by
    intro v hv hf x; rw [←train_restricted, restrict_at]; exact hC v hv (fun j hj=> he (hf j hj)) _; exact fun j hj=> hp (hf j hj)
lemma flattened (u:Multiset Room)(hv:u.card+i≤d)(hP:∀ x∈u,x∈X) : Checks Q X (train Q u f) i A:=by
    intro v hk h x; rw [← trains_add]; exact hC _ (by rw [Multiset.card_add]; omega) (fun x hx=> (Multiset.mem_add.mp hx).elim (h x) (hP x)) _
omit hC
end Checks
set_option quotPrecheck false
local notation "M" => Loft Q P
def cylindrical (Q: Place)(P:Place)[FiniteDimensional ℝ P](D:Set P): Set Q := floorOf P Q ⁻¹' D
lemma silo {D:Set P}(he:tsupport f⊆ cylindrical Q P D)(z:M): tsupport (atLoft h z f) ⊆ D:= fun x hx=>floor_chart h z x ▸ he (restrict_support h _ f hx)
structure Elevator (h:P≤Q) (T: Full P →ₗ[ℂ] Full P)(U:Full Q →ₗ[ℂ] Full Q): Prop where
   moves : Mobile U M
   acts : ∀ f z, atLoft h z (U f)=T (atLoft h z f)
namespace Elevator
lemma panes (g:P→ℂ)(hg:Smooth g): Elevator h (screen g hg) (paneM g hg):= ⟨Mobile.pane h g hg, fun f z=> specializes h f z g hg⟩
lemma subtracts (s:ℝ)(n:ℕ): Elevator h (Normal.leftOut s n) (escape h s n):= ⟨pages_out h s n, fun f z=> mechanism_out h f s n z⟩
lemma mul {T T': Full P →ₗ[ℂ] Full P}{U U': Full Q →ₗ[ℂ] Full Q} (he: Elevator h T U)(hp: Elevator h T' U') : Elevator h (T ∘ₗ T') (U ∘ₗ U'):=by
   constructor; intro x hx f; simp_rw [LinearMap.comp_apply,hp.moves _ hx, he.moves _ hx];
   intro f z; rw [LinearMap.comp_apply,LinearMap.comp_apply, he.acts,hp.acts]
end Elevator
lemma msplit (x:Multiset Room)(he:∀ v∈x,v∈ X∪Y):∃ a b: Multiset Room, x=a+b∧(∀ i∈a,i∈ X)∧∀ i∈b,i∈ Y:=by
    induction x using Multiset.induction_on with
    | empty=> exact ⟨0,0,by simp⟩
    | cons i x ih=> obtain ⟨a,b,rfl,hh,h⟩:= ih (fun i hi=> he _ (Multiset.mem_cons_of_mem hi)); rcases he i (by simp) with hl|hl; exact ⟨i ::ₘ a,b,by simp,fun k hk=> (Multiset.mem_cons.mp hk).elim (fun hw=>hw ▸ hl) (hh k),h⟩; exact ⟨a,i ::ₘ b,by simp,hh, fun k hk=> (Multiset.mem_cons.mp hk).elim (fun hw=>hw ▸ hl) (h k)⟩
lemma Elevator.exports {T:Full P→ₗ[ℂ] Full P}{U:Full Q→ₗ[ℂ] Full Q}(he:Elevator h T U)
    (hm:0<r)(ht:0≤s)(hf:tsupport f ⊆ cylindrical Q P (closedBall 0 R))(hh:Checks Q (Accounts P r∪X) f (d+k) A)(hp:X ⊆ M) -- type Elaborate
    (H:∀ f: Full P, Fits R f→Charge k r (f:P→ℂ) A→ Charge d s (T f:P→ℂ) B):
    Checks Q (Accounts P s∪X) (U f) d B:=by
    intro v hv hx x; obtain ⟨a,b,rfl,hv',hb⟩:=msplit _ hx; rw [Multiset.card_add] at hv;
    let t: M:= floorOf M Q x; let g:= atLoft h t; let y:= floorOf P Q x; have hy:forward h (insideCL loft_le t) y=x:= (attendance h).symm.apart x
    have hr:Charge d s (T (g (train Q b f))) B:= H _ (silo h ((train_support b f).trans hf) t) (Checks.charges _ _ hm (Checks.bound_restrict h (Checks.flattened hh b (by omega) (fun j hj=> Or.inr (hb j hj))) (insideCL loft_le t) subset_union_left (fun x hx=> hx.1)))
    rw [trains_add, Mobile.train_paths U _ he.moves (fun i hi=> hp (hb i hi))]
    nth_rw 1 [← hy]; -- ref x issue y definition let
    change ‖g (train Q a (U (train Q b f))) y‖ ≤ _
    have hW:g (train Q a (U (train Q b f)))= train P a (T (g (train Q b f))):= (train_restricted h _ _ _ (fun j hj=> (hv' j hj).1)).trans (congr_arg (train P a) (he.acts _ t))
    rw [hW]; exact charges_path _ _ ht hr (fun x hx=>hx.2) a (by omega) hv' y
end YM.Frontier6.Bouquet
