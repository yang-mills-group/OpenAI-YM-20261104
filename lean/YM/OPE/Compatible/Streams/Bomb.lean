import YM.OPE.Compatible.Streams.Billow
/-! # pullback.Horn -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Hark
open Function Filter Set ContinuousLinearMap
open scoped Topology BigOperators Classical
variable {d k i j m s:ℕ}{E:Fin s→Type}{G:ℕ→Type}[∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)] [∀ i,NormedAddCommGroup (G i)] [∀ i,NormedSpace ℝ (G i)]
variable {b x v u:ℝ}{μ:ℕ→ℝ}
local notation "S!"=> Mints E
local notation "L!"=> S! →L[ℝ] S!
variable {T:∀ i: Fin s,Cuts d μ v b (E i) G}
open Drift
variable {H:Type}{L:H→ℕ→ Mints E→L[ℝ] Mints E}{a w:H→ℝ}
variable {X:Mints E→L[ℝ] Mints E}{V W:Type}{w':V→ℝ}{r t:ℕ→ℝ}{Y:V→(Mints E→L[ℝ] Mints E)}
-- same cost label composition via wealth relation later.bound caps.B.
namespace Aeon
variable (A:Aeon V T X w') (K:∀ i,i<d→ Eave L X T a (r i) (t i) u i)
structure March (T:(i:Fin s)→Cuts d μ v b (E i) G) (Y:V→ Mints E→L[ℝ] Mints E)(m:ℕ):Prop where
      march (i:V): Edgewise (Y i)
      flag (j:Fin s)(i:ℕ)(v:V)(ht:i≤d)(x:Mints E) (hx:trims j.val x) : (Y v x j)∈ (T j).flag i ↔ x j∈ (T j).flag i
      tapC (j:Fin s)(i:ℕ)(v:V)(ht:i<d)(x:Mints E)(hx:trims j.val x)(h:x j∈ (T j).flag i): (T j).Tap i ((Y v) x j)= μ i ^ m • (T j).Tap i (x j)
-- building pullback
noncomputable abbrev pre (A:Aeon V T X w')(i:ℕ)(Y:V→L!)(v:V):= Submodule.comap (Y v).toLinearMap (A.flag i v)
noncomputable def picture (k:ℕ)(Y:V→L!)(i:V): pre A k Y i→ₗ[ℝ] A.flag k i:= ((((Y i).toLinearMap)∘ₗ (pre A k Y i).subtype).codRestrict _ fun v=>v.property)
variable (P:∀ i:ℕ,i<d → 0<μ i)
noncomputable def recap (i:ℕ)(he:i<d)(Y:V→L!)(m:ℕ)(v:V) : pre A i Y v→ₗ[ℝ] Fruition X (μ i):= (Fleet X (μ i) s (P i he)^m).toLinearMap ∘ₗ ((A.read i he v)∘ₗ (A.picture i Y v))
variable [∀ i,CompleteSpace (E i)][∀ i,CompleteSpace (G i)][∀ i,FiniteDimensional ℝ (G i)]
include A K P
noncomputable def extensionV (costV: V→ℝ)(hT:1 ≤ costV)(C:Wealth (fun i=>w' i) costV 1)(h:Wealth Y costV 1)(he:March T Y m): Aeon V T X costV:=by
      refine ⟨fun i=> pre A i Y,fun i hi=> recap A P i hi Y m,fun i=>?_,fun i v hi x hx=>?_,fun i v hi p=>?_,fun i hi v p j ht=>?_,fun i hi=>?_,hT⟩
      · unfold pre; rw [A.first]; exact Submodule.comap_top _
      · exact A.moves i v hi hx
      · let p':= picture A i Y v p; let f:= A.read i hi v; let g:= Fleet X (μ i) s (P i hi)^m; change p'.val∈ A.flag (i+1) v ↔ g (f p')=0; rw [A.depth, ← map_zero g]; exact (timeK (X:=X) (P i hi)|>.eq_iff).symm -- h
      · let p':= picture A i Y v p; let f':=A.read i hi v; have hv' : trims j.val p'.val:= he.march v j.val p.val ht; obtain ⟨hh,hq,hx⟩:= A.quake i hi v p' j hv'; have hP:p.val j∈ (T j).flag i:= (he.flag j i v hi.le p.val ht).1 hh; let q:=f' p'; let p'' := recap A P i hi Y m v p; have hj:= PursBack (K i hi) (P i hi) q m (i:=j) hq
        refine ⟨hP,hj.1,?_⟩; apply smul_right_injective _ (pow_pos (P i hi) m|>.ne'); exact hj.2.trans (hx.trans (he.tapC j i _ hi p.val ht hP))
      obtain ⟨a,H,n,hq⟩:= A.price i hi; obtain ⟨b,hb,j,hb'⟩:=C; obtain ⟨c,hc,k,hF⟩:= h; let g:=Fleet X (μ i) s (P i hi)^m; refine ⟨‖g‖*a*b^n*c,(by positivity), j*n+k, fun v p=>?_⟩; let Y₀:= picture A i Y v p; let f:=A.read i hi v; have he := hT v; have ht : 0 ≤ costV v:=zero_le_one.trans he; have hz:0 ≤ w' v:= zero_le_one.trans (A.non v); have hv:=hb' v; rw [Real.norm_of_nonneg hz,Pi.one_apply,mul_one] at hv; have hXv:‖Y v‖≤ c*costV v^k:=by simpa only [Pi.one_apply,mul_one] using hF v
      apply (le_opNorm g (f Y₀)).trans; apply (mul_le_mul_of_nonneg_left (hq v Y₀) (norm_nonneg _)).trans; have hH:‖Y₀.val‖ ≤c*costV v^k*‖p.val‖:= (le_opNorm (Y v) p.val).trans (mul_le_mul_of_nonneg_right hXv (norm_nonneg _)); refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hv _) H) hH (norm_nonneg _) (by positivity)) (norm_nonneg _)) ?_; rw [mul_pow,pow_add,pow_mul]; exact le_of_eq (by ring)
end Aeon
end YM.OPE.Hark
