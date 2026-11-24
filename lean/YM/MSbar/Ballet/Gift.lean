import YM.MSbar.Ballet.Gates
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Ballet
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave Parma Tin Bronze Asymptotics Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Alto Mosaic Mosaic.Issue
variable {G:Gauge}
structure Asked (K:MapPrices)(O:ChartRatio G)(A:Stage)(j i:ℕ)(V:KernelChoices)(F:Patch)(s p:ℕ)(x:ℝ)(t:Uniform.Before G A.width A.paths j V (p+3)): Prop where
    E0 : let y:=countV G F.L x; let L:=F.L; let b:=cWidth x; let b':=cWidth y; let w:=flurry x; let w':=flurry y
         let a:=grain A.clip F t (K.α j); let B:= Alto.tango K j i s p F O t a (t.tables A.clip F)
            Ready B G Dean L s p b w w' ∧ b ≤ ceilα K j i ∧ b' ≤ K.α j/2 ∧ b/L.val ≤ b' ∧ b/L.val ≤ a

variable (χ:ChartRatio G)(p s j i:ℕ)(H:Stage)(P:Patch)(K:MapPrices){D: KernelChoices}(hp:G.Simple)
include hp
lemma need (h:Host G (seats K j i s) P.L p s (ceilα K j i))(he:P.J=j) (T:Uniform.Before G H.width H.paths j D (p+3)) : ∀ᶠ x:ℝ in atTop, Asked K χ H j i D P s p x T:=by
   let d:=grain H.clip P T (K.α j); have hd:= roundT p hp K j H P T he -- args
   let Z:= Alto.tango K j i s p P χ T d (T.tables H.clip P)
   have hV:= bureau G Z p s (ceilα K j i) P.L (largeJ _ _ _ _ _ P χ T d (T.tables _ _) h)
   have hw:Tendsto cWidth atTop (𝓝 0):=tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num)).comp broad)
   let f:= countV G P.L; have hX:Tendsto f atTop atTop:=tendsto_atTop_add_const_right atTop _ tendsto_id
   filter_upwards [(billU hp P.L).eventually hV, hw.eventually (ge_mem_nhds (zonepos ..)), (hw.comp hX).eventually (ge_mem_nhds (show 0<K.α j/2 from (by have he:=K.alpha_pos j;positivity))), drift_scale hp P.L, hw.eventually (ge_mem_nhds hd)] with x hx h₁ h₂ hh hb
   constructor; refine ⟨hx (cWidth x) (?_) h₁ _ hh.1 ?_ hh.2.1,h₁,h₂,?_,?_⟩
   · unfold cWidth; positivity
   · linarith only [hh.1,hh.2.2]
   · unfold cWidth; rw [div_div]; have he:=zero_lt_one.trans_le hh.1; have hX:=he.trans_le hh.2.1; apply one_div_le_one_div_of_le (by positivity); apply (pow_le_pow_left₀ hX.le hh.2.2 2).trans; nlinarith only [mul_le_mul_of_nonneg_right (show (3:ℝ) ≤ P.L.val by exact_mod_cast P.coarse) (sq_nonneg (flurry x)),sq_nonneg (flurry x)]
   exact (div_le_self (by unfold cWidth; positivity) (Nat.one_le_cast.mpr P.L.property)).trans hb

end YM.MSbar.Ballet
