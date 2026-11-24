import YM.RG12.Common.Concourse
/-!
# Transport true k prices over the uncovered LOG gaps (deterministic bounds)

We use no summability claim over many k. Products used here are only laid through *one*
uncovered connector; they output poly-inverse-coupling costs, sufficient for the local
ReadingAt hypothesis. They cannot supply dyadic rotation/dilation estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Commission
open Function Filter Lattice Wilson RG RG.Supply Next.Rank Next.Rank.Tapes Next.Rank.Perch Next.Rank.Station Real Asymptotics Ship Peak
open PhysicalNext PhysicalNext.RankCovariance PhysicalNext.InteractingRank.Soft
open MergeProof MergeProof.East Next.Rank.Tapes.West MergeProof.Accent
open Pert.Dense
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}(hC:C.Makes)
variable {M:∀ d,ℕ→RepChart C d} {ϕ:Filter UVIndex} [ϕ.NeBot] (h : Observing C hC ϕ M)
set_option quotPrecheck false
local notation "A"=> C.path.levels
local notation "κ" k:max=> C.S.a k
lemma column_priced («A» : Levels G) (i:ℕ): (A.params (i+1)).columns ≤ ((A.S.block i).val:ℝ):=by
   let p:= A.params (i+1); let x : ℝ := 1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent
   let L:ℝ:= (A.S.block i).val; let t:ℝ:= A.clock.J (i+1)
   have ht: 4 ≤ t:=by unfold t; exact_mod_cast A.clock.adm _
   have hQ: 1<L:= lt_of_lt_of_le one_lt_two (by unfold L; have hb:=(A.S.block_large i); exact_mod_cast (show 2 ≤ (A.S.block i).val by omega))
   have hx:=p.width_pos; have hy:=p.paths_pos;have he:=p.price_pos
   have hC: p.columns ≤ x:=by unfold x; have hc:0<p.clip.relaxation:=p.clip.radius_pos; linarith [inv_nonneg.mpr hx.le]
   apply hC.trans
   have hL:= (div_le_iff₀ (Real.log_pos hQ)).mp (A.fits.logCost i)
   have hs: 1≤ t^2:=one_le_pow₀ (by linarith)
   apply (Real.log_le_log_iff (lt_of_lt_of_le (zero_lt_one.trans_le p.columns_ge) hC) (zero_lt_one.trans hQ)).mp
   exact hL.trans (mul_le_of_le_one_left (Real.log_nonneg hQ.le) (inv_le_one_of_one_le₀ hs))
-- line prices. choose uniform powers connector, not cumulative
variable {k t d:ℕ}{p:UVIndex}
include hC
lemma line (hr:C.ref d ≤ t)(hi:t≤k)(hk:k ≤ p.1)(x:C.label d):
    let r:= (C.S.a t)/(C.S.a k);
    mass C d (charts C hC d t p x) ≤ (r*r^d)*mass C d (charts C hC d k p x) ∧
    mass C d (charts C hC d k p x) ≤ r*mass C d (charts C hC d t p x):=by
   have hu m (he:C.ref d ≤ m)(hv:m≤p.1): charts C hC d m p x = ((C.factory d p.1 p.2).entries m ((C.factory d p.1 p.2).terminal.symm x)).x:=by unfold charts;rw [dif_pos ⟨he,hv⟩];rfl
   induction k,hi using Nat.le_induction with
   | base=> simp [ne_of_gt (C.S.a_pos t)]
   | succ i hi IH=>
     let r:= (κ t)/(κ i); let L:ℝ:= (C.S.block i).val; have hL:0 < L:=by unfold L; positivity
     intro v; have ht:0 < r:=div_pos (C.S.a_pos t) (C.S.a_pos i)
     have he:=hC.calibrated d p.1 p.2 (((hr.trans hi).trans (Nat.le_succ i)).trans hk)
     let V:=C.factory d p.1 p.2;let f:= (C.labels.level d).coeffSize
     let y:= V.terminal.symm x
     let X(i):= f (V.entries i y).x
     have hj: i ≤ p.1:= (Nat.le_succ i).trans hk
     obtain ⟨hf,hq⟩:= IH hj; let Q:=(A|>.params (i+1)).columns
     rw [hu t hr (hi.trans hj), hu i (hr.trans hi) hj] at hf hq
     change X t ≤ (r*r^d)*X i at hf;change X i ≤ r*X t at hq
     rw [hu t hr (hi.trans hj), hu _ ((hr.trans hi).trans (Nat.le_succ i)) hk]
     rw [show v=r*L from by unfold v r L; rw [Schedule.a_step]; field_simp]
     change X t ≤ r*L*(r*L)^d*X (i+1) ∧ X (i+1) ≤ (r*L)*X t
     have hu(i): 0 ≤ X i:= Work.G08.size_nonneg ..
     have hP:Q ≤ L:= column_priced (A) i
     refine ⟨hf.trans ((mul_le_mul_of_nonneg_left (show X i≤ L*L^d*X (i+1) from (he.front i (hr.trans hi) hk y).trans (by change Q*L^d*X _ ≤ _; gcongr; exact hu _)) (by positivity)).trans_eq ?_),?_⟩
     · rw [mul_pow]; ring
     exact (show X (i+1) ≤ Q*X i from he.back i (hr.trans hi) hk y).trans ((mul_le_mul hP hq (hu _) hL.le).trans_eq (by ring))

include h hC
structure Lamps (t k d:ℕ) (r:ℝ)(M:∀ d:ℕ,ℕ→RepChart C d)(f:Module.End ℂ (C.label d)) : Prop where
    norms v: mass C d (f v) ≤ r * mass C d v
    lower v: mass C d v ≤ r^(d+1)*mass C d (f v)
    pulls v: ((κ t :ℂ)^d) • M d t (f v) = ((κ k:ℂ)^d) • M d k v

lemma passage (hr:C.ref d ≤ t)(hi:t≤k): let r:= C.S.a t / C.S.a k
   ∃ f, Lamps (C:=C) t k d r M f:=by
   let z:= Ultrafilter.of ϕ; have hZ: (z:Filter UVIndex) ≤ ϕ:= Ultrafilter.of_le _
   intro r; let μ(i:ℕ):ℝ:= (C.S.a i); let a:=(μ k)^d/(μ t)^d; let c:=(a:ℂ)
   let W(i:UVIndex)(d:ℕ):=(charts C hC d t i).toLinearMap.comp (atK C hC d k i).toLinearMap
   let f(i:UVIndex):= LinearMap.toContinuousLinearMap (c • W i d)
   have he(i:UVIndex)(x:C.label d): f i x = c • charts C hC d t i (atK C hC d k i x):= rfl
   have hσ(x:ℕ): 0 < μ x:= C.S.a_pos x
   have hw:0<r:= div_pos (hσ _) (hσ _); have ha:0<a:= div_pos (pow_pos (hσ _) _) (pow_pos (hσ _) _); have hc: a*r^d=1:= by unfold r a; rw [div_pow]; unfold μ; field_simp [(C.S.a_pos _).ne']
   have age:∀ᶠ i in ϕ,k≤(i:UVIndex).1:=h.grows.eventually_ge_atTop _
   have hf:∀ᶠ i in ϕ,∀ x, mass C d (f i x) ≤ r*mass C d x ∧ mass C d x ≤ r^(d+1)*mass C d (f i x):=by
      filter_upwards [age] with i hk x
      obtain ⟨h1,h2⟩:= line hC hr hi hk (atK C hC d k i x)
      rw [show charts C hC _ k i (atK C hC _ k i x)=x from (charts C hC ..).apply_symm_apply _] at h1 h2
      let p:= charts C hC _ t i (atK C hC _ k i x)
      rw [he,show mass C d (c • p)=a*mass C d p from ?_]
      · constructor
        · calc
             _ ≤ a*(r*r^d*mass C d x):=mul_le_mul_of_nonneg_left h1 ha.le
             _ = _:=by linear_combination (norm:=ring_nf) r* mass C d x*hc -- r let
        apply h2.trans_eq
        change r*mass C d p= _; rw [pow_add,pow_one];linear_combination (norm:=ring_nf) -(r*mass C d p)*hc
      unfold mass Labels.Frame.coeffSize c; simp_rw [Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg ha.le]; exact (Finset.mul_sum ..).symm
   have hρ:∀ᶠ i in ϕ, ‖f i‖ ≤ r*(((C.labels.level d).extra+1:ℕ):ℝ):=by
      filter_upwards [hf] with i hi; apply ContinuousLinearMap.opNorm_le_bound _ (by positivity); intro x; exact (norm_le_mass C d _).trans ((hi x).1.trans ((mul_le_mul_of_nonneg_left (mass_le_norm ..) hw.le).trans_eq (by ring)))
   obtain ⟨V,hV⟩:= ultrafilter_converges z f (r*(_ :ℝ)) (hρ.filter_mono hZ)
   refine ⟨V.toLinearMap,?_⟩
   have hl x:Tendsto (fun i=>f i x) (z:Filter UVIndex) (𝓝 (V x)):=
     ((continuous_id.clm_apply continuous_const: Continuous fun i:RepChart C d=> i x).continuousAt).tendsto.comp hV
   have hY x:= (continuous_mass C d).continuousAt.tendsto.comp (hl x)
   refine ⟨fun v=> le_of_tendsto (hY v) ((hf.mono fun i hi=>(hi v).1).filter_mono hZ), fun v=> ge_of_tendsto ((hY v).const_mul (r^(d+1))) ((hf.mono fun i hi=> (hi v).2).filter_mono hZ),?_⟩
   intro v; have he (j : ℕ)(hj:C.ref d ≤ j)(x:UVIndex → C.label d)(y : C.label d)(ht:Tendsto x (z:Filter _) (𝓝 y)) := (continuous_fst.clm_apply continuous_snd: Continuous fun i:RepChart C d× C.label d=> i.1 i.2).continuousAt.tendsto.comp (((h.tends _ j hj).mono_left hZ).prodMk_nhds ht)
   have ht:= (tendsto_const_nhds (x:=(C.S.a t:ℂ)^d)).smul (he t hr _ (V v) (hl v))
   have hu:= (tendsto_const_nhds (x:=(C.S.a k:ℂ)^d)).smul (he k (hr.trans hi) _ v (tendsto_const_nhds (x:=v)))
   apply tendsto_nhds_unique_of_eventuallyEq ht hu
   refine Eventually.of_forall fun i : UVIndex=> ?_; change (C.S.a t:ℂ)^d • (atK C hC d t i (c • charts C hC d t i (atK C hC d k i v)))= _
   rw [map_smul, show atK C hC d t i ((charts C hC d t i) (atK C hC d k i v))= _ from (charts C hC ..).symm_apply_apply _, smul_smul, show (C.S.a t:ℂ)^d*c=(C.S.a k:ℂ)^d from ?_]
   · rfl
   unfold c a μ; push_cast; field_simp [(C.S.a_pos _).ne']
end YM.RG12.Commission
