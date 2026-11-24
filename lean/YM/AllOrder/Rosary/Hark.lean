import YM.AllOrder.Rosary.Avalon
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Rosary
open Function Filter Set Lattice Wilson RG Ovens
open AnalyticBridge VerifiedReset Collection Quotes Residual WilsonStartup UVNext.PricedKernels Averaging Geo Progress.DirectedRecipe Extra.Iteration Push.BetaTransport
open Till Burn
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {R : PathData G} {c : Clip} {p : BudgetPoint} {σ C Λ H w : ℝ}
    {X : Listing G n} {v : Collection.Source G n} {ι κ : Type}
/- Seed & regular masked model before; Candor prices survive H1 fusion `finish` including moves with this partition. -/
namespace Devotion
variable (p) (M:Burn.Locale G)
local notation "S"=> Site n
-- dawn model (and error ∆Δ change uses as Herb.L.Difference price)
def basil : Herb G n S:= ⟨spine p,M n⟩
local notation "XΘ"=> basil (n:=n) p M -- no stage
local notation "T"=> Burn.keys n
variable {p M}{A:Pipes G n}{t:Tap G n}{W' C' K a b δ μ:ℝ}
section
variable (h:Ensemble p A t a b δ)
    (hm:∀ i:Site n,Till.Fairness p i (court i p.B) (M n i) C) (hW:PhysicalNext.Repeat.Trio.Mirrors (M n)) -- orient
local notation "Dξ"=>Herb.pumps (XΘ) T A
local notation "dξ"=>Herb.fluid (XΘ) T t
local notation "Hξ"=>Pipes.pours Dξ dξ
local notation "Ω"=> Real.exp p.supportExponent * C
local notation "R₀"=> Set.range (pivot n)
include hm hW
lemma lives : (XΘ).Knows p Ω := by
 refine ⟨fun s b=> ⟨Push.Local.turnSites s b,fun i=> ⟨rfl,?_, funext fun x=>(hW ..).symm⟩ ⟩,fun _=> C,hm,?_⟩
 · let e:= Push.Local.turnSites s b; change halo p.B {e i}= _; rw [← Finset.image_singleton]; exact Push.Local.halo_map e (Push.Local.turn_sep s b) ..
 intro x;
 change SumBudget (fun i:S=> if i=x then p.mass (court i p.B) C else 0) _; refine ⟨fun i=>?_,Summable.of_finite,?_⟩
 · dsimp only; split_ifs; exact mul_nonneg (Real.exp_pos _).le (hm x|>.cap.1); exact le_rfl
 rw [tsum_fintype]; simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]; exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_of_le_one_right p.exponent_pos.le (by exact_mod_cast shell p x))) ((hm x).cap.1)
include h
lemma plant : Ensemble p (Dξ) (dξ) (Ω+a) b δ ∧ (Hξ)=press p (A.pours t) M ∧ Candor p (Hξ) (Set.range (pivot n)) (Ω) a :=
    ⟨Herb.sprout h (lives hm hW) _,rfl,(Burn.remit p _ M h.bills hm hW).2⟩
lemma turn (U:Config G n): (Hξ).additive p U= (∑ i:S, masked p.threshold (court i p.B) (M n i) U)+(A.pours t).additive p U:= by
 rw [Herb.sundial h (lives hm hW) T U|>.1, Herb.teller,tsum_fintype]; rfl
end
namespace Fusion
local notation "Y"=> Pipes.fused (Progress.DirectedRecipe.folio G n) p (Rack.widen A t)
local notation "U"=> Pipes.pours A t
local notation "Y★"=>Pipes.pours (drawer G n) (Rack.widen A t)
-- all cutters follow.Agreements for E slots, true K labels from Ledger. Sym preserving partition.
include n
local notation "u"=> Rack.upE A
variable (M:Set ℕ)(W:Ingredients A t p a μ)
lemma decid (i:ℕ) : u i ∈ (u) '' M ↔ i∈M:= by simp -- decid name
include W
lemma paid (R:PathData G)(c:Clip) (h:Candor p (U) M b δ) : Candor p (Y) ((u) '' M) b δ:= by
 let he:= Rack.preserves A t p; obtain ⟨⟨v₀,hα,hE⟩,hM⟩:=h; let v:=stuff (u) v₀
 have hV(i): p.supBounds ((Y★).reg i|>.site) ((Y★).reg i|>.support) ((Y★).E i) (v i):= by
    by_cases hi : i∈Set.range (u); · obtain ⟨i,rfl⟩:= hi; unfold v; rw [he.same_reg,he.emits,stuffed]; exact hα i
    unfold v; rw [he.restE i hi, Progress.DirectedRecipe.blank _ _ hi]; exact no_cost .. -- prefix
 refine ⟨⟨v,hV,fun i=>?_⟩,fun x y=> ?_⟩
 · have he'(j:ℕ) : wallet p (Y★) v i (u j)= wallet p (U) v₀ i j:= by unfold wallet v; rw [he.same_reg,stuffed]
   have hh (j:ℕ)(hj:j ∉ range (u)): wallet p (Y★) v i j=0:=by unfold wallet v; rw [Progress.DirectedRecipe.blank _ _ hj]; simp [BudgetPoint.mass]
   change SumBudget (fun x=> if x∈ (u) '' M then wallet p (Y★) v i x else 0) b ∧ SumBudget (fun x=> if x∈(u) '' M then 0 else wallet p (Y★) v i x) δ
   constructor
   · exact transfer_budget (u) (fun j=> by simp only [decid,he']) (fun j hj=>by simp [hh j hj]) ((hE i).1)
   exact transfer_budget (u) (fun j=> by simp only [decid,he']) (fun j hj=>by simp [hh j hj]) ((hE i).2)
 obtain ⟨l,hl⟩:= hM x y; let v:=on_shelves l; obtain ⟨K⟩:= ((W.gates R c a a).moves x y); -- don't need assumption if E.K.OK? use arguments R,c
 have heT i: v.ep (u i)=u (l.ep i):=move_stock _ (regMap (destination x y)) l.ep A.reg (fun i=> reg_ext (l.reg_site i).symm (l.reg_support i).symm) _
 refine ⟨⟨v.ep,K.kp,v.reg_site,v.reg_support,K.forced_support,K.forced_inventory,K.forced_tests,v.valuesE,K.valuesK⟩,fun i=>?_⟩; change v.ep i∈(u) '' M↔ i∈(u) '' M
 constructor; · rintro ⟨j,hj,hh⟩; obtain ⟨r,rfl⟩:= l.ep.surjective j; exact ⟨r, (hl r).mp hj, v.ep.injective ((heT r).trans hh)⟩
 rintro ⟨j,hj,rfl⟩; rw [heT,decid]; exact (hl j).mpr hj
variable (Y':Burn.Locale G)
variable (β α:ℝ)
omit W
lemma sharp (h:Burn.Seed (trunk R c p A t β α) Y') : ∃ t':Burn.Seed (finish R c p A t β α) Y', t'.model=h.model.trans (u):= by
 let Y0:= Rack.preserves A t p; let R' := trunk R c p A t β α
 refine ⟨⟨_,fun i=>?_,fun i=>?_, h.off⟩,rfl⟩
 · change ((Y★).reg (u (h.model i))).support = _ ∧ ((Y★).reg (u (h.model i))).site=_; rw [Y0.same_reg]; exact h.reg i
 change (Y★).E (u (h.model i))=_; rw [Y0.emits]; exact h.value i
end Fusion
end Devotion
end YM.AllOrder.Rosary
