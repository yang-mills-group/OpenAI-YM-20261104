import YM.OPE.Compatible.Lake.Rider
/-!
# Weighted reduction in throughput-of-Φ
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Lake
open Function Filter MeasureTheory Spec Lattice RG Word Cov Allot MergeProof
open Next.Rank Extraction ContinuousLinearMap Treaty
open scoped Topology Classical BigOperators
variable {G:Gauge}{C:Family G}
variable {d i:ℕ} {E: Fin (d+1)→Type} [∀ i,NormedAddCommGroup (E i)] [∀ i,NormedSpace ℂ (E i)]
local notation "I"=> Fin (d+1)
variable {δ η:ℝ}{U r:ℕ→ℝ}
structure Bridge (R:Dock E ≃L[ℂ]Dock E) (C:Family G)(η L r:ℝ)(i:ℕ):Prop where
     openLane : ∃ F,Treaty (extent C i) (Real.exp (η*levy C i)) L (F:Dock E≃L[ℂ]Dock E) ∧ ‖R.toContinuousLinearMap-F.toContinuousLinearMap‖≤ r ∧ ‖R.symm.toContinuousLinearMap-F.symm.toContinuousLinearMap‖≤ r
local notation "M"=> hill C
variable (hG:G.Simple) (H: RateLE atTop (hill C) U 0)(hη:0 ≤ η)(hs: RateLE atTop (hill C) r (-1-δ)) (ht:0<δ)
lemma radiator_rate {s:ℝ} (h:G.Simple): RateIs atTop (hill C) (radiator C s d) (d*s):=by
   have hp := ((taxes (C:=C) h).div_atTop (hill_high (C:=C) h)).add_const 1;rw [zero_add] at hp
   apply RateIs.exp'; have hp:= hp.const_mul ((d:ℝ)*s); rw [mul_one] at hp; apply hp.congr'; filter_upwards [] with j
   have hm:= hill_pos C j; field_simp;unfold levy; ring
section tube
include hG hη H hs
variable {s:ℝ}(he:0<s)(hL':(d:ℝ)*s<δ)
include hL' he
lemma sold : ∃ D:ℕ, ∀ᶠ i:ℕ in atTop, ∀ F:Dock E≃L[ℂ]Dock E, Bridge F C η (U i) (r i) i →
   ∃ a u P, Split (extent C i) a u (rescale F (cram C E s (i+1)) (cram C E s i)) P ∧1 ≤ a∧ a ≤3/2∧ u≤ ice d∧ price d a u ≤ Real.exp ((D:ℝ)*levy C i) := by
    let p:=η+(d:ℝ)*s; have hp:0 ≤ p:= add_nonneg hη (by positivity)
    obtain ⟨D,hD⟩:= exists_nat_ge (p+1)
    let a(i):=Real.exp (p*levy C i);let u(i):= radiator C s d i*r i
    have hv:= hill_high (C:=C) hG
    have hu:RateLE atTop M u ((d:ℝ)*s+(-1-δ)):= ((radiator_rate (C:=C) hG).pays hv).mul hs
    have hK: 0< ice d:=by unfold ice; positivity
    have he':Tendsto a atTop (𝓝 1):=by simpa only [a,mul_zero,Real.exp_zero] using! Real.continuous_exp.continuousAt.tendsto.comp ((taxes (C:=C) hG).const_mul p)
    let γ:=G.slopeConstant*Real.log 2/4; have hg: 0<γ:=by unfold γ; have := Gauge.slopeConstant_pos hG; have hz:0 < Real.log 2:=Real.log_pos one_lt_two; positivity
    let z:ℝ:=2*((d+1:ℕ):ℝ); have hz:0<z:=by unfold z; positivity
    have hl:Tendsto (fun i=> z*(u i*β C i)) atTop (𝓝 0):= RateLE.tends (a:=_) ((RateLE.const z hv).mul (hu.mul ((speck (C:=C)).pays hv))) (by linarith) hv
    let f i:= edgeWt C s d i* U i
    have hm:Tendsto f atTop (𝓝 0):=by
       have hb:= Real.continuous_exp.continuousAt.tendsto.comp ((taxes (C:=C) hG).const_mul ((d:ℝ)*s))
       rw [mul_zero,Real.exp_zero] at hb
       have hh:RateLE atTop M (fun i=>Real.exp ((d:ℝ)*s*levy C i)) 0:=RateLE.absBound 2 hv (hb.norm.eventually (ge_mem_nhds (by rw [norm_one]; linarith)))
       apply (hh.mul (RateLE.exp (-s) hv)|>.mul H).tends _ hv; linarith only [he]
    refine ⟨D,?_⟩; filter_upwards [he'.eventually (ge_mem_nhds (by linarith: (1:ℝ)<3/2)), (hu.tends (by linarith) hv).eventually (ge_mem_nhds hK),hm.eventually (ge_mem_nhds hK),hl.eventually (ge_mem_nhds hg), raises (C:=C) hG] with i hi hj hf hl hq F h
    obtain ⟨F',h,Hx,hV⟩:= h.openLane; let R:= rescale F' (cram C E s (i+1)) (cram C E s i)
    have hh:= diffWay (C:=C) hG he F F' _ Hx hV i
    have ht : Split (extent C i) (a i) (u i) (rescale F (cram C E s (i+1)) (cram C E s i)) R:= by
       refine ⟨fun i j hj=>(lowMark (s:=s) h i j hj).1,fun i j hj=>(lowMark (s:=s) h i j hj).2, fun i=>(h.pins hG he i).1,fun i=> (h.pins hG he i).2,fun j k hj=> ((h.spreadEq hG he j k hj).1).trans hf, fun j k hj=> ((h.spreadEq hG he j k hj).2).trans hf, hh.1,hh.2⟩
    let v:=levy C i; have hv : 0<v:= levy_pos hG _
    have hM:1 ≤ a i:=Real.one_le_exp (mul_nonneg hp hv.le)
    refine ⟨a i,u i,R,ht,hM,hi,hj,?_⟩
    have hi : z* u i≤v:=by apply le_of_mul_le_mul_right _ (β_pos C i); rw [mul_assoc]; exact hl.trans hq
    change a i+z*u i≤_; calc
       _ ≤ Real.exp (p*v) * (1+v):=by change _≤ a i*(1+v); linarith only [hi,mul_le_mul_of_nonneg_right hM hv.le]
       _ ≤ Real.exp (p*v)*Real.exp v:=mul_le_mul_of_nonneg_left (by linarith only [Real.add_one_le_exp v]) (Real.exp_nonneg _)
       _ ≤ _:=by rw [← Real.exp_add]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_right hD hv.le]
end tube
end YM.OPE.Lake
