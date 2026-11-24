import YM.RG05Readout.Velvet.Dinner
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge} {C:Family G} {i n m p N d:ℕ}{V:Type}[Fintype V][DecidableEq V]
    {F:E4→Wave V}{U:Set E4}(hw:Savors F)(hp:IsCompact U)(s:V→ℕ)(v:(i:V)→Palette C (s i))
local notation "S!"=> C.side N p
local notation "R"=> Config G (C.side N p)
local notation "X"=> multi C m N p s v
local notation "Σ"=> (i:V)→ Address.Mark C (s i)
open Finset
variable (r: Config G (C.side N p))
include hw hp
local notation "D"=> dine hw hp
lemma reader (p': V→Site S!) : (harpoon (C:=C) (N:=N) (p:=p) s v p' D) r= ∫ z in U, harpoon s v p' (F z) r:=by
   let P(i:Σ):=fun j:V=>(i j).1
   let Y(i:Σ):=∏ j:V,key C N p (s j) (v j) (i j) (p' j) r
   let f(i:Σ) (z):=((perform s (P i) (F z)).val 0)*Y i
   change ∑ i:Σ,((perform s (P i) D).val 0) * Y i=∫ z in U, ∑ i:Σ,f i z
   have hv(i:Σ): IntegrableOn (f i) U:=by let X':=livesX (moving hw s (P i) Finset.univ.toList) hp 0; exact X'.mul_const _
   rw [integral_finsetSum _ (fun i (_:i∈(Finset.univ:Finset Σ))=> hv _)]; refine Finset.sum_congr rfl (fun i _=> ?_); unfold f perform; rw [integral_mul_const,meals];rfl
omit hp
lemma rolling (p': V→Site S!) : Continuous (fun z=> harpoon s v p' (F z) r):=by
   apply continuous_finsetSum _ (fun i _=> Continuous.mul ?H (continuous_const)); exact ((moving hw s (fun j:V=>(i j).1) Finset.univ.toList).continuous.comp ((continuous_const (y:=(0:Cloud V))).prodMk continuous_id))
include hp
lemma ordering (m:ℕ) : multi C m N p s v D r= ∫ z in U, multi C m N p s v (F z) r:=by
   let Z:= multi C m N p s v D; unfold multi; simp_rw [LinearMap.smul_apply,LinearMap.sum_apply, Pi.smul_apply,LinearMap.comp_apply, Finset.sum_apply,integral_smul]; apply congr_arg; let K:= Finset.univ (α:=V→Site S!); let x(y:V→Site S!):= SmoothFork hw (fun i=>C.S.place (y i)) (C.S.a N); let P(y:V→Site S!) (z:E4):=harpoon s v y (fork (C.S.a N) (fun i=>C.S.place (y i)) (F z)) r; rw [integral_finsetSum K (fun i (_:i∈K)=> show Integrable (P i) (volume.restrict U) from ContinuousOn.integrableOn_compact hp (rolling (x i) s v r i).continuousOn)]; refine Finset.sum_congr rfl (fun i _=>?_); exact reader (x i) hp s v r _
section
variable (Ψ:Wave V)(q:ℝ) {g:Body} (hg:IsCompact (tsupport g.val))
omit [DecidableEq V] in
abbrev glow (g:Body)(q:ℝ)(Ψ:Wave V)(z:E4):=g.val z • rel q Ψ z
omit hw hp [DecidableEq V] in
lemma glows (g:Body) : Savors (glow g q Ψ):=by
    unfold Savors glow rel; change ContDiff ℝ ∞ (fun z:Cloud V×E4=>g.val z.2 • Ψ.val ((fun _=>q⁻¹ • -z.2)+ q⁻¹ • z.1));
    have ht:ContDiff ℝ ∞ (fun (z:Cloud V×E4) (_ : V)=>q⁻¹ • (-z.2)) := contDiff_pi.mpr (fun i=> ((contDiff_snd.neg).const_smul q⁻¹)) -- syntax
    exact ContDiff.smul ((show ContDiff ℝ ∞ g.val from g.property).comp contDiff_snd) ((show ContDiff ℝ ∞ Ψ.val from Ψ.property).comp (ht.add (contDiff_fst.const_smul q⁻¹)))
omit hw hp
abbrev molten (Ψ:Wave V)(q:ℝ) {g:Body} (hg:IsCompact (tsupport g.val)):Wave V:=dine (glows Ψ q g) hg
omit [DecidableEq V] in
lemma glow_point (x:Cloud V) : (molten Ψ q hg).val x=∫ z:E4, g.val z * (rel q Ψ z).val x:=by
   change (∫ z in _,g.val z *(rel q Ψ z).val x)=_; exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by rw [image_eq_zero_of_notMem_tsupport hx,zero_mul])
lemma waves (m:ℕ) : physicalEra q Ψ g C m p N s v=(∏ _i:V, (q:ℂ)⁻¹ ^4) • multi C m N p s v (molten Ψ q hg):=by
   funext u; change (∏ _i:V, _) * _ = _*multi C m N p s v (dine _ _) u; rw [ordering]; unfold glow; simp_rw [map_smul,Pi.smul_apply]; apply congr_arg
   change _ = (∫ z in tsupport g.val,g.val z * _); exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by rw [image_eq_zero_of_notMem_tsupport hx,zero_mul])).symm -- syntax
end
end YM.RG05Readout.Velvet
