import YM.RGComparison.Core16.Astage.Panel
import YM.PertExtension.Aspiration

/-!
# Uniformity of the running coupling prices

Projection at horizon in Continuum hierarchy F.fuse. Demand limit already supplied at fixed
period for actual data by `Upland.winding`. For period plus mesh, if using further common ordered
sub-limits, expose at least these persist on them: an Ultrafilter inside the agreed order; pick
BEFORE any test. Need not assert `rate` for any particular successive-limit data not yet produced.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Astage
open Filter Function Set Real OPE
open Pert.Asymptotics Next.UVStress
open Lattice RG Extraction
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{f:Extraction.Order}
    (h:C.Makes) (hG:G.Simple) {l: Filter (ℕ×ℕ)} (hl: l≤f.fuse) [l.NeBot]
local notation "q"=> C.path.levels
variable {p:ℕ→ℝ}

structure Eternal (C:Family G) (l:Filter (ℕ×ℕ)) (p:ℕ→ℝ) : Prop where
    limit (m:ℕ): Tendsto (fun i:ℕ×ℕ=>C.path.β i.1 i.2 m) l (𝓝 (p m))
include h
namespace Eternal
lemma selects (U:Ultrafilter (ℕ×ℕ))(H : (U:Filter _) ≤ f.fuse) : ∃ p:ℕ→ℝ,Eternal C U p:=by
    have hh(m:ℕ): ∃ x:ℝ, Tendsto (fun i:ℕ×ℕ=> C.path.β i.1 i.2 m) (U : Filter _) (𝓝 x):=by
       let f'(i:ℕ×ℕ):ℝ:= C.path.β i.1 i.2 m; let g':= Ultrafilter.map f' U; let b:= C.path.levels.clock.hatBeta m; let Y:= Set.Icc (b/2) (2*b); have hx:Y ∈ g':= Ultrafilter.mem_map.mpr (show ∀ᶠ i:ℕ×ℕ in (U:Filter _), f' i∈Y from (((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono H).mono (fun i hi=> (h.wilson.represents i.1 i.2 m hi).band)) -- `Cards.largeMesh`
       obtain ⟨x,hx,hF⟩:= isCompact_Icc.ultrafilter_le_nhds' g' hx
       exact ⟨x,hF⟩
    choose p hp using hh; exact ⟨p,⟨hp⟩⟩

variable (H:Eternal C l p)
include hl H
lemma bounds (m:ℕ): p m∈ Set.Icc ((q).clock.hatBeta m / 2) (2*(q).clock.hatBeta m):=
    isClosed_Icc.mem_of_tendsto (H.limit m) ((((OPE.Cards.largeMesh f).eventually_ge_atTop m).filter_mono hl).mono (fun i hi=> (h.wilson.represents i.1 i.2 m hi).band))
lemma positivity (m:ℕ): 0 < p m := lt_of_lt_of_le (div_pos (zero_lt_one.trans ((q).fits.delayed _)) zero_lt_two) ((bounds h hl H m).1)
lemma calibrated (m:ℕ) : Tendsto (fun i:ℕ×ℕ=> regulatorRun C i.1 i.2 m) l (𝓝 (sqrt (p m))⁻¹):= ((H.limit m).sqrt).inv₀ (sqrt_pos.mpr (positivity h hl H m)).ne'
variable {ι:Type*}{l':Filter ι} (m:ι→ℕ) (ht:Tendsto m l' atTop)
set_option quotPrecheck false
include hG ht
local notation "Λ"=> budgetLog C m
lemma real_pace : RateIs l' Λ (fun i=>(sqrt (p (m i)))⁻¹) (-(1/2:ℝ)):=by
    let x i:= rho C m m m i; have hp:= pace (p:=m) h hG ht (Eventually.of_forall fun _=> Nat.le_refl _) -- expected
    let v i:=(sqrt (p (m i)))⁻¹; let K:= budgetLog C m; have hΛ:= large_Λ C hG ht
    have hh(i):x i/ 2 ≤ v i∧v i≤2*x i:=by
       let a:= C.path.β (m i) (m i) (m i); let b:= p (m i); let T:= C.path.levels.clock.hatBeta (m i); have he:0 < a:= Overlay.beta_positive h.wilson (Nat.le_refl _); have hv:0<b:= positivity h hl H (m i); have hx:= h.wilson.represents (m i) (m i) (m i) le_rfl|>.band; have hw:=(bounds h hl H (m i)); have hE(u z:ℝ)(hu:0<u)(hz:0<z)(he:z ≤4*u): sqrt z ≤ 2*sqrt u :=by nlinarith only [he, Real.sq_sqrt hu.le,Real.sq_sqrt hz.le,sqrt_nonneg z,sqrt_nonneg u]
       change (sqrt a)⁻¹/2 ≤ (sqrt b)⁻¹ ∧ (sqrt b)⁻¹ ≤ 2* (sqrt a)⁻¹
       have hb:0<sqrt b:= sqrt_pos.mpr hv; have h_:0<sqrt a:=sqrt_pos.mpr he
       constructor
       · refine (div_le_iff₀ zero_lt_two).2 ?_; field_simp; linarith only [hE a b he hv (by linarith only [hx.1, hw.2])]
       field_simp; linarith only [hE b a hv he (by linarith only [hw.1,hx.2])]
    refine RateIs.of_sandwich (f:=fun i=> x i / 2) (hp.div (RateIs.const hΛ zero_lt_two)|>.swap (by ring)) (f':=fun i=> 2*x i) (((RateIs.const hΛ zero_lt_two).mul hp).swap (by ring)|>.pays hΛ) (Eventually.of_forall fun i=>(hh i).1) (Eventually.of_forall fun i=>(hh i).2) hΛ
end Eternal
end YM.RGComparison.Core16.Astage
