import YM.OPE.Therm.Lavish
/-!
# Entropy recovery at history meshes
Keep cutoff/level quantifiers, and arbitrary torus p. All constants explicit wrt furnace sizes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm.Cradle
open Function Set Filter RG Lattice Wilson MeasureTheory Cells
open House (chilly countables fence)
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {A:History G}(H:A.Selected) {k N p r:ℕ} {t τ C e L Z₀:ℝ}
local notation "n"=> A.S.side k p
-- watch variable notation
local notation "𝒞"=> Config G n
local notation "β₀"=> A.β N p N
local notation "Q" => partition G (A.S.side N p) β₀
local notation "η"=> prior G n
local notation "R"=> A.rep N p k
local notation "D"=> scene A N p k
local notation "Ex"=> Real.exp
local notation "P$"=> PlaqAxes
variable (T:Tiling (A.S.side k p)) (hv:T.kind=.site)
local notation "ν"=> Fintype.card T.Cell
local notation "M"=> T.side.val
-- singular budget check
include H hv
lemma credit (hi:k ≤ N)(h:Stove.Chart R r C e){F:T.Cell→ Config G (A.S.side k p)→ℝ}{P:T.Cell→ℝ} (he:Programs T R r τ F P) (hy:t>0)(ht:t≤1)(hx:4*t+τ≤ (R).p.threshold)(hβ :4*t≤τ)(hb:2≤ M)
    (hz:0≤Z₀)(hP:∀ z: Face (Per n),(D).real (trigger z τ) ≤ Z₀)
    (hF:∀ i U,F i U ≤ L)(hm: 0 ≤ L+premium T R r t C):
    (∑ i,∫ U,F i U∂D) ≤ graphRate T R r t C e P + ν*(L+premium T R r t C)*((M+1)^4*Fintype.card PlaqAxes)*Z₀:= by
   let d:= premium T R r t C; let K(U):=pend T τ F U d; let c:=graphRate T R r t C e P
   letI:=probability (p:=p) H hi; have hi' := H.represents N p k hi
   have hk :Envelope K:= playEnv T he.bill _ _; have ht':= pressure T hv h he hy ht hx hβ hb hi'.good (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (Real.exp_pos _).le _))) (A.nonnegative H N p k hi)
   have hu : (∫ U,K U∂D) ≤ c:=by
      apply Real.exp_le_exp.mp; apply (convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall (fun _=> Set.mem_univ _)) (hk.integrable D) (hk.exp.integrable D)).trans
      rw [scenery H hi]; rw [div_le_iff₀ (partition_pos _)]; rw [← A.partition_eq H N p k hi]; exact ht'
   let w:ℝ:= ((M:ℝ)+1)^4*Fintype.card PlaqAxes* Z₀; have hL i: (∫ U,F i U∂D) ≤ (∫ U, order T τ F i U d∂D)+(L+d)*w := by
      let S:=chilly (G:=G) (countables T i) τ; have ht : (D).real Sᶜ ≤ w:=by
         apply (House.cool_miss Z₀ hP (countables T i)).trans; refine mul_le_mul_of_nonneg_right ?_ hz; exact_mod_cast House.halls_face_count T i
      let f(U):=order T τ F i U d; let g:𝒞→ℝ:= Sᶜ.indicator (fun _=>L+d)
      have hS: MeasurableSet Sᶜ:= (House.bath _).compl; have hh: Envelope f:= Envelope.piece (House.bath _) (he.bill _) (Envelope.const _)
      have hv: ∀ U,F i U ≤ f U+g U :=by
         intro U; unfold f order g; by_cases h: U∈S; · rw [if_pos h,indicator_of_notMem (notMem_compl_iff.mpr h),add_zero]
         rw [if_neg h,indicator_of_mem (mem_compl h)]; linarith only [hF i U]
      have hG: Integrable g D:=(integrable_const _).indicator hS; have he := integral_mono ((he.bill i).integrable D) ((hh.integrable D).add hG) (g:=fun U=>f U+g U) hv
      rw [integral_add (hh.integrable D) hG] at he; unfold g at he; rw [integral_indicator hS,setIntegral_const,smul_eq_mul,mul_comm _ (L+d)] at he
      exact he.trans (add_le_add_right (mul_le_mul_of_nonneg_left ht hm) _)
   apply (Finset.sum_le_sum (fun i _=> hL i)).trans; rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_univ]; refine le_trans (b:=c+ ν*((L+d)*w)) (add_le_add_left ?_ (ν*((L+d)*w))) ?_ -- wrong proof binder
   · apply le_trans ?_ hu; exact (integral_finsetSum _ (fun i (_:i∈Finset.univ)=> show Integrable (fun U=> order T τ F i U d) D from (show Envelope (fun U=>order T τ F i U d) from Envelope.piece (House.bath ..) (he.bill i) (Envelope.const _)).integrable D)).symm.le
   unfold c w d; linarith only
end YM.OPE.Therm.Cradle
