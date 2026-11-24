import YM.RG17.Stairs
import YM.RG17.DiscreteExclude
import YM.SharpGram.Load.Watt

/-!
# Sparse anomaly and minimal report

Exact orthogonal/traceless pin brings cost even on the sparse path. Need
only an integrated mixed derivative PT reading on ONE diagnostic where
reference RHS tends positive (or nonzero). Phi slot uncentered in that
reading (don't discard singletons in diagram!). The centering supplied
for K is actual in Final. No claim between rungs of the sparse path for
this estimate, which needs no radiative input off that path.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}{u:Filter (ℕ×ℕ)}
   {B:Lenses.Mantle F u}{L:Layout F} (h : Services C f S) {s:Extraction.Sequence}
set_option quotPrecheck false
abbrev interval (B:Lenses.Mantle F u) (s:Extraction.Sequence) := Filter.map (offsetPath B s) atTop
local notation "b"=> interval B s
local notation "r!"=> offsetPath B s
local notation "A"=> portal L
local notation "U"=> UVNext.FreeStress.canonicalStress C.labels
local notation "φ"=> scalarRay A
include h
lemma focused {r a d:ℝ}{k:ℂ} (hp:StressRay F (A r) r a d k)(i j:Axis) : (A r).symm (((r^4:ℝ):ℂ) • (Load.wing F i j))= (-(a:ℂ)) • U i j:=by
   -- only delta
   let s:= (↑(r^4:ℝ):ℂ); let M:=A r; let D:=U; let J:=F.sector.energy
   let T:= d • M (φS C) + k • S.unit 4
   have he(i j:Axis): s • J i j=M ((-(a:ℂ)) • D i j)+(if i=j then T else 0):=by
       have hg:=hp.tensor i j
       rw [RCLike.real_smul_eq_coe_smul (K:=ℂ) (r^4)] at hg
       refine hg.trans (congr_arg₂ (·+·) ?_ (by rfl))
       unfold Trace.metric0; rw [map_neg,map_smul, RCLike.real_smul_eq_coe_smul (K:=ℂ)]; simp [M,D]
   have hz : s • Load.sumTrace J=(4:ℂ) • T:=by
      unfold Load.sumTrace; rw [Finset.smul_sum]
      simp_rw [he,if_true,Finset.sum_add_distrib,← map_sum,← Finset.smul_sum]
      rw [show ∑ x:Axis,D x x=0 from (Load.single (C:=C) h.simpleGate).trace]
      simp only [smul_zero,map_zero,zero_add,Finset.sum_const,Finset.card_univ,Fintype.card_fin]
      rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; try rfl -- to nat_smul
   change M.symm (s • (J i j-_))= _
   rw [smul_sub,he]
   split_ifs with hf; · rw [smul_comm s,hz,smul_smul]; norm_num; rfl
   simp [D]
lemma focusLimit (hk: Stands L B s) {a d:ℝ→ℝ}{k:ℝ→ℂ} (hs:∀ᶠ r in b,StressRay F (A r) r (a r) (d r) (k r)):
    Tendsto a b (𝓝 1):=by
   obtain ⟨p,q,H⟩:= Load.canView (C:=C) h.simpleGate; obtain ⟨v,hv⟩:= Module.Projective.exists_dual_ne_zero ℂ H
   let m:= UVNext.FreeStress.canonicalStress C.labels p q
   let V:=LinearMap.toContinuousLinearMap v
   have hx:= (V.continuous.continuousAt.tendsto.comp ((Load.leading_delta B h p q).comp s.cofinal)).div_const (-(v m))
   rw [map_neg, show V _=v m from rfl, div_self (neg_ne_zero.mpr hv)] at hx
   have ht:Tendsto (fun r:ℝ=>(↑(a r):ℂ)) b (𝓝 1):=by
      apply tendsto_map'_iff.mpr; apply hx.congr'
      filter_upwards [hs] with i hi -- eventually_reduce?
      change V ((Load.tent B (s i) 4).symm (((r! i^4:ℝ):ℂ) • Load.wing F p q)) / (-v m)=(a (r! i):ℂ)
      rw [← show A (r! i)=Load.tent B (s i) 4 from poised_here hk 4 i,focused h (show StressRay F (A (r! i)) (r! i) _ _ _ from hi),map_smul]
      rw [smul_eq_mul,neg_mul,neg_div_neg_eq]; exact mul_div_cancel_right₀ _ hv
   exact Complex.continuous_re.continuousAt.tendsto.comp ht
lemma selector (hk: Stands L B s) (ψ:Test 2): Tendsto (fun r=>force A ψ r (φ r)) b (𝓝 (refForce C ψ)):=by
   apply tendsto_map'_iff.mpr
   let w:= (![φS C,φS C] : Fin 2→ Free C 4)
   have hh: Tendsto (fun i=> plate (d:=fun _=>4) (fun j=> A (r! i) (w j)) (r! i) (direct timeAxis ψ)) atTop (𝓝 (plate (S:=Maxwell.freeTable C.labels) (d:=fun _=>4) w 1 (direct timeAxis ψ))) := flex h (d:=fun _=>4) (z:= w) hk _ -- flex signature
   rw [show refForce C ψ= _ from sift (S:=Maxwell.freeTable C.labels) (φS C) (φS C) (r:=1) one_pos timeAxis (Maxwell.Free.hierarchy C.labels) ψ]
   apply hh.neg.congr (fun i=> ?_)
   dsimp only [Function.comp_apply]; let r:= r! i; let t:=φ r
   change _= force A ψ r t
   rw [force,sift t _ (show 0<r from B.positive _) _ F.room.kernel] -- t defeq
   rw [show (fun j=> A _ (w j))= ![t,t] from funext fun j=>by fin_cases j <;> rfl]; try rfl

variable (Z:Ledger L)
include Z
omit h
private lemma scaleRatio {g:Filter ℝ}{ψ:Test 2}{a d:ℝ→ℝ}{k:ℝ→ℂ} (hg:g ≤ home)(he:refForce C ψ≠0)
   (ht:Tendsto (fun r=> force A ψ r (φ r)) g (𝓝 (refForce C ψ)))(ha:∀ᶠ r in g,StressRay F (A r) r (a r) (d r) (k r))
   (hp:Tendsto a g (𝓝 1))(hx:Tendsto (fun r=>shiftAll A ψ r (φ r)/(Z.g r:ℂ)^2) g (𝓝 ((anomalyCoefficient G/2) • refForce C ψ))):
      Tendsto (fun r=> d r/Z.g r^2) g (𝓝 (-(anomalyCoefficient G/2))):=by
   let A₀ r:= force A ψ r (φ r)
   have hk:Tendsto (fun r=> (↑(d r/Z.g r^2:ℝ):ℂ)) g (𝓝 (↑(-(anomalyCoefficient G/2):ℝ):ℂ)):=by
      rw [Complex.real_smul] at hx
      have he':= Complex.continuous_ofReal.continuousAt.tendsto.comp hp
      have hA:= (he'.neg.mul hx).div ht he
      rw [Complex.ofReal_one, neg_one_mul,neg_div, mul_div_cancel_right₀ _ he, ← Complex.ofReal_neg] at hA
      refine hA.congr' ?_; filter_upwards [ha,ht.eventually_ne he, positiveLength.filter_mono hg] with r hv hR hr
      have hh:= swept L ψ hr hv (φ r); simp only [Complex.real_smul] at hh
      change (-(a r:ℂ)*_) / force A ψ r (φ r)=_
      have hz : (↑(Z.g r):ℂ)≠0:=by exact_mod_cast (Z.positive r).ne'
      have he(Y:ℂ)(hY:Y≠0):(-(a r:ℂ)*(shiftAll A ψ r (φ r)/Y^2))/force A ψ r (φ r)=(↑(d r):ℂ)/Y^2:=by field_simp; linear_combination -hh
      rw [Complex.ofReal_div,Complex.ofReal_pow]; exact he _ hz
   exact Complex.continuous_re.continuousAt.tendsto.comp hk

include h
lemma towardsTrace {g:Filter ℝ}{a d:ℝ→ℝ}{k:ℝ→ℂ} (hg:g ≤ home)
    (hv : ∀ᶠ r in g, StressRay F (A r) r (a r) (d r) (k r)) (he:Tendsto (fun r=> d r / Z.g r^2) g (𝓝 (-(anomalyCoefficient G/2))))
    (ht : Tendsto (Kdiag A) g (𝓝 (↑(theoryDensity G):ℂ))) : SampleLog F g (theoryDensity G):=by
   let s : ℝ := Trace.anomalyCoefficient G
   have hu:Tendsto (fun r=> discount r • central F none (separated r)) g (𝓝 (↑(theoryDensity G):ℂ)) := by
      have h' : (4 * (-(s/2)) * (2*s)⁻¹)^2=(1:ℝ):=by field_simp [show s≠0 from (Trace.anomalyCoefficient_pos h.simpleGate).ne']; ring
      have hx:=((((he.const_mul 4).mul (Z.contour.mono_left hg)).pow 2).smul ht); rw [weighted Z.simple,h',one_smul] at hx
      refine hx.congr' ?_; filter_upwards [hv] with r hr
      rw [show 4*(d r / Z.g r^2)*(Z.g r^2 *_)= OPE.run r*(4*d r) from ?_]
      · rw [discount,mul_comm (r^8:ℝ),mul_pow,mul_smul,mul_smul,raw_focus_exact F,Trace.trace_ray_eval F A hr]; try rfl
      exact (fun (Y:ℝ) (hh:Y≠0)=> (show 4*(d r/Y^2)*(Y^2*OPE.run r)=OPE.run r*(4*d r) by field_simp)) _ (Z.positive r).ne'
   let w:= some F.α.atPoint
   have hp:Tendsto (fun r=> discount r • (central F w (separated r)-central F none (separated r))) home (𝓝 0):=by
       apply Metric.tendsto_nhds.mpr; intro t he; filter_upwards [log_agreement F h 1 1 t he zero_le_one zero_lt_one, positiveLength] with r hr hi
       rw [dist_zero_right,discount,OPE.run,←Real.log_inv]; exact hr _ _ (room_separated _ hi.le) w none
   have h:= (hp.mono_left hg).add hu; rw [zero_add] at h; exact h.congr (fun r=> by rw [smul_sub, sub_add_cancel, restTrace_origin])
lemma tracedOnce (hk: Stands L B s) (ψ:Test 2)(he:refForce C ψ≠0)
   (hx : Tendsto (fun r=>shiftAll A ψ r (φ r)/(Z.g r:ℂ)^2) b (𝓝 ((anomalyCoefficient G/2) • refForce C ψ))) : SampleLog F b (theoryDensity G) := by
   have hb : b ≤ home:= (homes B).comp s.cofinal
   have hh: ∀ᶠ r in b,∃ a d k,StressRay F (A r) r a d k:= ((commands B L h hk.pegs).aligned.mono fun i hi=> Trace.ray_of_alignment F A hi.some h.simpleGate).filter_mono hb
   rw [eventually_iff_exists_mem] at hh
   obtain ⟨V,hV,hU⟩:=hh; choose! a d k hA using hU
   have ha:∀ᶠ r in b,StressRay F (A r) r (a r) (d r) (k r):= mem_of_superset hV (fun x hx=>hA x hx)
   exact towardsTrace h Z hb ha (scaleRatio Z hb he (selector h hk ψ) ha (focusLimit h hk ha) hx) (tendsto_map'_iff.mpr (pieces h hk))
end YM.RG17
