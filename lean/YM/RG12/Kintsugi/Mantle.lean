import YM.RG12.Kintsugi.Spoon
import YM.RG12.Kintsugi.Spot
/-! # Restricted matrix ticket (true)

Use full two-sided prices along the common observation filter on the
complex hull of the traceless gravitational pins, and on all the tensor-
covariant row functionals tested even on *full* unprojected quotients. No
positive-definite claim on redundant list. Costs & remaining horizons clear.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Kintsugi
open Filter Function Set Finset Analysis Extraction Lattice RG Org Spec Next.UVStress Climb Table Real UVNext.FreeStress
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}(U : Final C f S)(M:∀ d,ℕ→RepChart C d){ϕ:Filter UVIndex}[ϕ.NeBot]
variable {lit:ℕ→Prop}(P:Commission.Port C)(h : Alidade.Route P lit U.room.cutoff) (hs:Ranked P)
variable (he:Observing C U.room.cutoff ϕ M)(hf:ϕ≤f.fuse)(hG:G.Simple)(H:OPE.Facilities C f S)
local notation "χ"=>C.path.levels.clock.hatBeta
include h he hf hG H hs
-- product price arithmetic for ANY finite combo (cost exponent grows one at each linear span generation)
lemma hull_in (x:S.Field 4)(hx:x∈GrainSpace U):∃ p,∀ᶠ k in atTop,Worthy M x p k:=by
   let B(x:S.Field 4) := ∃ p:ℕ,∀ᶠ k in atTop,Worthy M x p k
   have hT:=(hat_grows (C:=C) hG)
   let A:Submodule ℂ (S.Field 4):={carrier:= setOf B,
                                    zero_mem':=?_,
                                    add_mem':=?_,
                                    smul_mem':=?_}
   · have ha i j:U.sector.energy i j ∈ A:=show B _ from ⟨11,stress_in U M P h.free hs H he hf hG i j⟩
     have hV: GrainSpace U ≤ A:= by
        refine Submodule.span_le.mpr ?_; rintro w ⟨i,rfl⟩
        unfold grain beamline; dsimp only; split
        · rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; exact A.sub_mem (ha ..) (A.smul_mem _ (Submodule.sum_mem A fun j _=>ha ..))
        exact A.sub_mem (ha ..) (zero_mem A)
     exact hV hx
   · rintro a b ⟨i,hi⟩ ⟨j,hj⟩; refine ⟨i+j+1,?_⟩
     filter_upwards [hi,hj,hT.eventually_ge_atTop 2] with k ha hb ht; obtain ⟨u,heu,hu⟩:=ha; obtain ⟨v,hev,hv⟩:=hb
     let t:=χ k; have hT:1 ≤ t:=one_le_two.trans ht
     refine ⟨u+v,by rw [map_add,map_add,heu,hev],(solid_mass ..).trans ((add_le_add hu hv).trans ?_)⟩
     rw [pow_succ,pow_add]; change t^i + t^j ≤ _
     have he := mul_le_mul_of_nonneg_left ht (show 0 ≤ t^i*t^j from mul_nonneg (pow_nonneg (zero_le_one.trans hT) _) (pow_nonneg (zero_le_one.trans hT) _))
     nlinarith only [he,one_le_pow₀ hT (n:=i),one_le_pow₀ hT (n:=j)]
   · exact ⟨0,Eventually.of_forall (fun k=>⟨0,by simp,by unfold mass Labels.Frame.coeffSize;simp⟩)⟩
   rintro c y ⟨i,hi⟩; refine ⟨i+1,?_⟩
   filter_upwards [hi,hT.eventually_ge_atTop (1+‖c‖)] with k hq ht
   obtain ⟨v,heq,hv⟩:=hq
   refine ⟨c • v,by rw [map_smul,map_smul,heq],?_⟩
   rw [supplies_mass,pow_succ]; rw [mul_comm _ (χ k)]
   exact mul_le_mul (by linarith only [ht]) hv (mass_nonneg ..) (le_trans (norm_nonneg c) (by linarith only [ht]))

lemma hull_out (Q:S.Field 4→ₗ[ℂ]ℂ): ∃ p,∀ᶠ k in atTop, ∀ v:C.label 4,S.project 4 (M 4 k v)∈GrainSpace U→
    ‖Q (S.project 4 (M 4 k v))‖ ≤ χ k^p *mass C 4 v:= by
   obtain ⟨T,hT⟩:=kiln U hG
   obtain ⟨L,hL,hV⟩:= heated U T hT
   have ha:=sectors_ship U M P h.free hs hG H he hf hL
   let I:=GrainSpace U; let E:= Axis×Axis
   let A:↑I→ₗ[ℂ](E→ℂ) := LinearMap.pi fun i:E=> ((L i.1 i.2).toLinearMap.comp I.subtype)
   have hv : A.ker=⊥:= by
      apply (LinearMap.ker_eq_bot' (f:=A)).mpr; intro m hm; apply Subtype.ext
      exact hV m.val m.property (fun i j=> congr_fun hm (i,j))
   obtain ⟨p,hp⟩:= @LinearMap.exists_leftInverse_of_injective ℂ ↥I (E→ℂ) _ _ _ _ _ A hv
   let X:(E→ℂ)→L[ℂ]ℂ:=LinearMap.toContinuousLinearMap (𝕜:=ℂ) (E:=E→ℂ) (F':=ℂ) ((Q.comp I.subtype).comp p)
   refine ⟨11,?_⟩
   filter_upwards [ha,(hat_grows (C:=C) hG).eventually_ge_atTop ‖X‖] with k hk hx v ht
   let u:I:=⟨S.project 4 (M 4 k v),ht⟩
   rw [show Q (S.project 4 (M 4 k v))=X (A u) from ?_]
   rotate_left
   · have hr : p (A u)=u:= LinearMap.congr_fun hp u
     change Q _= Q ((p (A u)).val); rw [hr]
   have he':‖A u‖ ≤ χ k ^10 * mass C 4 v:= (pi_norm_le_iff_of_nonneg (mul_nonneg (by positivity) (mass_nonneg ..))).mpr fun i=> by
      change ‖L i.1 i.2 _‖ ≤ _
      simpa only [pow_zero,Nat.sub_self,div_one] using! (hk i.1 i.2 v)
   exact (X.le_opNorm _).trans ((mul_le_mul hx he' (norm_nonneg _) (le_trans (norm_nonneg _) hx)).trans_eq (by ring))

-- verify that GrainSpace includes genuinely physical traceless evaluations. At
-- least diagonal or off (and in fact both separately, without using irreducibility).
def upright (C:Family G)(i j:Axis):Prop:=
   canonicalStress C.book.grid i j≠0
lemma grain_occupied (i j:Axis)(hU:upright C i j):grain U i j≠0:=by
   obtain ⟨T,hK,hT⟩:= oracle (C:=C) hG
   have hB:∃ᶠ k in atTop,True ∧ lit k:=by
      rw [frequently_atTop]
      intro k
      obtain ⟨i,hI,hV⟩:=(h.free.scope.and (h.free.covered.1.eventually_ge_atTop k)).exists
      exact ⟨P.rate i,hV,trivial,hI⟩
   obtain ⟨g,Z,hg,hA,X,hX⟩:= rooted U M P h.free hs T H he hf hG _ hB
   obtain ⟨R,hR⟩:=lines T.hT _ T.lit.edges T.lit.hers
   obtain ⟨K,He,Ha,Hs,Hk⟩:= zooms U M P T (fun i=>(hA i).2.2) hX R hR
   obtain ⟨w,hw⟩:= persistent U T K hT Ha Hs
   let ans:=canonicalStress (F:=C.book.grid) -- parameter check
   let c:=T.T.κ⁻¹
   have hv(a b:Axis): Tendsto (fun k=> (K.U (w k) 4).symm ((K.r (w k))^4 • centering S 4 (U.sector.energy a b))) atTop (𝓝 (c • ans a b)):=by
      rw [hK,torch,one_smul] at hw; exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hw a) b
   let Y(k:ℕ):= ((K.U (w k) 4).symm.toLinearMap.restrictScalars ℝ).comp ((centering S 4).restrictScalars ℝ)
   let q(k:ℕ):= (K.r (w k))^4 • Y k; let J:=U.sector.energy
   have ht(i j:Axis)(k:ℕ):(K.U (w k) 4).symm ((K.r (w k))^4 • centering S 4 (J i j))=q k (J i j):= ((K.U (w k) 4).symm.toLinearMap.restrictScalars ℝ).map_smul ..
   have hx: Tendsto (fun k=>q k (grain U i j)) atTop (𝓝 (c • ans i j)):=by
      have hy: Tendsto (fun k=> q k (J i j)) atTop (𝓝 (c • ans i j)):=(hv i j).congr (ht i j)
      unfold grain beamline; rw [← show J=U.sector.energy from rfl]; split_ifs with hB
      · have hZE:∑ i:Axis, ans i i=0:=by simpa only [torch,one_smul] using Trace.torch_traceless C.labels 1 -- check
        have hs: Tendsto (fun k=>∑ i:Axis,q k (J i i)) atTop (𝓝 0):= by
           have hh := tendsto_finsetSum Finset.univ (fun i _=> (hv i i).congr (ht i i)); rwa [← Finset.smul_sum,hZE,smul_zero] at hh
        simpa only [map_smul,map_sub,map_sum,smul_zero,sub_zero] using! hy.sub (hs.const_smul (1/4:ℝ))
      simpa using hy
   intro H';rw [H'] at hx; simp only [map_zero] at hx
   have hh:Tendsto (fun _ :ℕ=> (0 : (Climb.Bel C.book).Field 4)) atTop (𝓝 0):=tendsto_const_nhds
   exact (smul_ne_zero (inv_ne_zero T.T.hκ) hU) (tendsto_nhds_unique hx hh)
-- at least some: this and faithful quote independently indicate this is sharper than lower d
lemma nonvacancy : GrainSpace U ≠ ⊥:=by
   obtain ⟨T,hK,hT⟩:= oracle (C:=C) hG
   have hz:∃ i j,upright C i j:= by
       by_contra! e
       apply hT.sign
       rw [hK,torch,one_smul]; funext i j
       exact not_ne_iff.mp (e i j)
   obtain ⟨i,j,hj⟩:=hz
   intro h'
   apply grain_occupied U M P h hs he hf hG H i j hj
   have hp : grain U i j∈GrainSpace U:= Submodule.subset_span ⟨(i,j),rfl⟩; rwa [h',Submodule.mem_bot] at hp
end YM.RG12.Kintsugi
