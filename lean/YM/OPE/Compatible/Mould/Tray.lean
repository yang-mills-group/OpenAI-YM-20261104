import YM.OPE.Compatible.Roost.Romance
/-! # abstract P(u) mould -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Lattice Laurent Matrix RG Drift Quit Quit.PriceZ
open scoped Topology BigOperators Classical
variable {E F M:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
noncomputable def Fate(p:E→L[ℝ] E)(A:Dice E)(k:ℕ): E→ₗ[ℝ] E→ₗ[ℝ] ℝ:= (LinearMap.mk₂ ℝ (fun x y:E=> pullD (p^k) A x y) (fun i j p=>by rw [map_add];rfl) (fun i j p=>by rw [map_smul];rfl) (fun i j p=>map_add ..) fun i j p=>map_smul ..)
variable {P:Patch}{G:Gauge}{K:Votive.Sponsor G}
-- helper.E!
def D₀t (Y:(n:Side)→Even n.val→Site n→Site n→ℕ→M→ E→ₗ[ℝ] E→ₗ[ℝ] ℝ)(b:ℕ)(P:Patch)(K:Votive.Sponsor G):Submodule ℝ E where
     carrier:={p|∀ (n:Side)(h:Even n.val)(x y:Site n),b ≤ n.val→Pins K P x y →∀ i t q,Y n h x y i t p q=0∧ Y n h x y i t q p=0}
     zero_mem':=by intro n h x y _ _ i j q; simp only [map_zero,LinearMap.zero_apply,and_self]
     add_mem':=by intro a b ha hb x h v w he ht t i q;obtain ⟨H,F⟩:= ha x h v w he ht t i q; obtain ⟨V,Q⟩:= hb x h v w he ht t i q; simp only [map_add,LinearMap.add_apply,V,Q,H,F,add_zero,and_self]
     smul_mem':=by intro c p hp x h v w he ht t i q;obtain ⟨H,F⟩:= hp x h v w he ht t i q; simp only [map_smul,LinearMap.smul_apply,H,F,smul_zero,and_self]
lemma antique (p:E→L[ℝ] E)(q:ℝ)(m i:ℕ)(A:Dice (KernP p q m)) : ∃ T: KernP p q m→ₗ[ℝ] KernP p q m→ₗ[ℝ] ℝ,∀ x y,T x y=A ((portC p q m^i) x) ((portC p q m^i) y):=⟨Fate (portC p q m) A i,fun _ _=>rfl⟩
end YM.OPE.Hark
