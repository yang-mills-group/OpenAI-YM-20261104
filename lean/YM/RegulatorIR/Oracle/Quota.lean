import YM.RegulatorIR.Oracle.Owned
import YM.RegulatorIR.Clocks.Enough

/-! Primitive higher vertices: translation roots vs per-leg charge. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {G:Gauge} {X Y A B I V: Type} {α σ Ω Ω' δ δ' l s P:ℝ} {u p q k:ℕ} {n t:Side}

section cosmos
open Motion
variable [Fintype Y][Fintype V](D:Deck P X Y) (F:Parade I V) (K:Tariff X)
omit [Fintype Y] in
lemma axi_cost (L:I→Packet X p)(H:Prim.Rot D F L)(h:∀ (x:Tuple X p) d,K.diameter (D.wind d∘ x)=K.diameter x): localQ K (massive L) (∑ v:V,quota (L (F.bare v)) K.diameter):=by
 intro i x; let U:= Hold i x; let f(z:I × U):=‖L z.1 z.2.val‖ₑ*K.diameter z.2.val; let g(u:V × Tuple X p):=‖L (F.bare u.1) u.2‖ₑ*K.diameter u.2
 apply (inside_quota (fun (u:U) (t:I)=> L t u.val) (fun u=>K.diameter u.val)).trans
 unfold quota; rw [ENNReal.tsum_comm]
 let p'(u:I × U):= ((F.rolls.symm u.1).2,(D.wind (F.rolls.symm u.1).1).symm ∘ u.2.val)
 have he(u:I × U): D.wind (F.rolls.symm u.1).1∘(p' u).2=u.2.val:= by ext x;simp [p']
 have hx(u:I × U):f u=g (p' u):=by
    unfold f g; rw [← he u,h];
    have hp:=H (F.rolls.symm u.fst).1 (F.bare (p' u).1) (p' u).2; rw [show F.rips _ (F.bare _)=u.1 from (F.puts (F.rolls.symm u.1)).symm.trans (F.rolls.apply_symm_apply _)] at hp
    exact congr_arg₂ (· * ·) ((D.dyed_cost ..).symm.trans ((congr_arg (fun z:ℝ=>‖z‖ₑ) hp).trans (D.dyed_cost ..))) rfl
 have hi:Injective p':=by
    intro u v hf; let a:= (F.rolls.symm u.1).1; let b:=(F.rolls.symm v.1).1
    have hw i (d e:Motion)(h:D.wind d i=x)(he:D.wind e i=x) : d=e:=(D.edges i x (by rw [← h,D.projected])).unique h he
    have hg : a=b:=by
       apply hw ((p' v).2 i) a b
       · rw [← hf]; exact (congr_fun (he u) i).trans u.2.property
       exact (congr_fun (he v) i).trans v.2.property
    refine Prod.ext (F.rolls.symm.injective (Prod.ext hg (show _ from ?_))) (Subtype.ext ?_)
    · change (p' u).1=(p' v).1; rw [hf]
    unfold a b at hg;rw [← he u, ← he v,hf,hg]
 change (∑' v:I,∑' u:U,f (v,u))≤ _; rw [← ENNReal.tsum_prod,← tsum_fintype (L:=SummationFilter.unconditional V)]
 apply le_trans (b:=∑' i:V×Tuple X p,g i) ?_ (ENNReal.tsum_prod .. |>.le)
 simp_rw [hx]; exact ENNReal.tsum_comp_le_tsum_of_injective hi g
omit [Fintype Y] in
lemma capableM (h:0<l) (x:Tuple X p) d : ((Tariff.native l h u).uses D.pos).diameter (D.wind d∘ x)= ((Tariff.native l h u).uses D.pos).diameter x:=by
 unfold Tariff.diameter; apply congr_arg₂ (· ⊔ ·) _ rfl
 apply iSup_congr;intro i; apply iSup_congr; intro j; change Tariff.amount l u (dist (D.pos (D.wind _ _)) (D.pos (D.wind _ _)))= _
 rw [D.displaced,D.displaced,Motion.cost_loc];rfl
omit [Fintype Y] [Fintype V] in
lemma boundedC {M:Packet X p}(h:Prim.Bounded M){K:Tariff X}(hc:∀ x y,K.road x y≠⊤) : quota M K.diameter ≠⊤:=by rw [quota,tsum_eq_sum (s:=h.toFinset)]; exact ENNReal.sum_ne_top.mpr (fun i _=> ENNReal.mul_ne_top (by finiteness) (by apply ne_of_lt;exact sup_lt_iff.mpr ⟨lt_top_iff_ne_top.mpr (iSup_ne_top (fun k=> iSup_ne_top (fun j=>hc (i k) (i j)))),by simp⟩)); intro i hi; simp [show M i=0 from Function.notMem_support.mp fun ht=> hi (h.mem_toFinset.mpr ht)]
end cosmos

end YM.RegulatorIR.Oracle
