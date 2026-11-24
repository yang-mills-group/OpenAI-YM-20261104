import YM.FormalOPE.RG10.Inherit.Sealed
import YM.Push.LOOP_COEFFICIENT.Tangent
/-!
 # noise cost and full top Wilson prescription before any re-expression.
 At every Fabric and any choice of strictly positive cost coefficients.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Inherit
open Function Filter Topology MeasureTheory PertExtension Series Precision
open BlockGauge Series.Radial Push.Loops Chart Lattice RG
open scoped Classical Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge}{E:Type}[Fintype E]

def sumCost : Spending G E:= fun u=> ∑ i,G.price (u i)
def costV (i:E) (u:Direction G E) := G.price (G.lieExp (u i))
lemma cost_rate : ContDiffAt ℝ ω (fun u=> G.price (G.lieExp u)) 0:= price_diff G.exp_jet.contDiffAt
lemma cost_view (i:E): ContDiffAt ℝ ω (costV (G:=G) i) 0:= ContDiffAt.comp (f:= (fun u:Direction G E=> u i)) (0:Direction G E) cost_rate (contDiffAt_apply ℝ G.Color i _)
lemma costJet (u:Direction G E): jet (sumCost ∘ expLinks G E) 2 u = ∑ i, ((2:ℝ)⁻¹ * ‖u i‖^2) := by
 unfold jet;
 have H α: (sumCost ∘ expLinks G E) α= ∑ i, costV (G:=G) i α:=rfl
 rw [funext H, iteratedFDeriv_fun_sum_apply (u:=Finset.univ) (fun i _=> (cost_view (G:=G) i).of_le le_top), show (Nat.factorial 2)=2 from rfl]; norm_num -- ∑ distribute
 -- via jet term
 rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
 let R : Direction G E →L[ℝ] G.Color := ContinuousLinearMap.proj i
 have h:= second (k:=R) R.contDiff.contDiffAt (map_zero _) cost_rate exp_price_rate.1 u
 change jet (costV i) 2 u = jet (fun u=> G.price (G.lieExp u)) 2 ((fderiv ℝ R 0) u) at h
 have hv : (fun _: Fin 2=> u i) = ![u i, u i] := by funext m; fin_cases m <;>rfl
 rw [R.fderiv,show R u=u i from rfl] at h; unfold jet at h; rw [hv,exp_price_rate.2,real_inner_self_eq_norm_sq] at h; norm_num [Nat.factorial] at h; rw [h]
lemma cost_positive {u:G.El}(h:u≠1) : 0<G.price u:= by
 have he:G.mat u - 1 ≠ 0:= fun e=> h (G.mat_injective ((sub_eq_zero.mp e).trans G.mat_one.symm))
 have hu:0<G.chord u:= div_pos (norm_pos_iff.mpr he) (Real.sqrt_pos.mpr (by exact_mod_cast G.dimPos))
 nlinarith [G.chord_price u]
omit [Fintype E] in
lemma pick {K:Type} {u v:E→K}(h:u≠v): ∃ i,u i≠v i:= by by_contra! H; exact h (funext H)
lemma firstCost : Strong (sumCost (G:=G) (E:=E)):= Strong.grant _
 (by simp [sumCost])
 (fun u hu=> let ⟨i,h⟩:= pick hu; Finset.sum_pos' (fun i _=> (G.price_range (u i)).1) ⟨i,Finset.mem_univ _, cost_positive h⟩)
 (by unfold sumCost; fun_prop)
 (ContDiffAt.sum (s:=Finset.univ) (fun i _=> cost_view i))
 (fun u hu=> by obtain ⟨i,h⟩:= pick hu; rw [costJet]; exact Finset.sum_pos' (fun i _=> by positivity) ⟨i,Finset.mem_univ _,mul_pos (by norm_num) (pow_pos (norm_pos_iff.mpr h) 2)⟩)

variable {c f n:Side}
lemma distanceCost (S:StepData c f): Strong (distance S (G:=G)):= firstCost.tune S.kernel.penalty_pos
lemma endcap (even:_root_.Even n.val) : Strong (Orb.account (G:=G) (n:=n)):= Strong.grant _
 (by rw [Orb.account,Orb.flat_at_zero]; ring)
 (fun u hu=> by
    apply div_pos _ two_pos; have he: 0≠ Wilson.energy (Orb.links 1 u):= fun e=>hu (Orb.flat_unique even e.symm)
    exact lt_of_le_of_ne (Wilson.energy_nonneg _) he)
 (Orb.continuous_account) Orb.fiscal_smooth.contDiffAt (fun u h=> by obtain ⟨c,hc,ha⟩:= Orb.coercion (G:=G) even; apply lt_of_lt_of_le (mul_pos hc (pow_pos (norm_pos_iff.mpr h) 2)) (ha u))

open Fabric
lemma reference {n}(L:Fabric G n){w:L.Cost→ℝ}(hw:∀ i,0<w i): Strong (L.production w) := by
 cases L with
 | endcap n h=> -- Empty; can apply direct empty case
      have ha:(Fabric.endcap n h).production (G:=G) w=0:= funext (fun i=> gone_zero h w i)
      rw [ha]; refine Strong.grant 0 rfl (fun u hu=> ?_) continuous_const contDiffAt_const (fun u hu=> ?_)<;> exact (hu (funext fun i=> Empty.elim i)).elim
 | layer S B t hf L=>
     rename_i c
     have he:= Strong.merge ((distanceCost (G:=G) S).tune (hw none)) (reference L (w:=fun i=> w (some i)) (fun i=> hw (some i)))
     change Strong (G:=G) (I:=L.Path) _
     convert he using 1 -- defEq
     ext1 e; exact sectional S B t hf L w e
termination_by structural L
lemma every_reference {n}(L:Fabric G n)(a:L.Cost): Component (fun u=>L.air u a):= by
 cases L with
 | endcap => exact Empty.elim a
 | layer S B t hf L=>
   change Option _ at a
   cases a with
   | none=> exact Strong.view (J:=L.Path) Sum.inl (distanceCost S).toComponent
   | some i=> exact Strong.view (J:=L.Path) Sum.inr (every_reference L i)
termination_by structural L
end YM.FormalOPE.RG10.Inherit
