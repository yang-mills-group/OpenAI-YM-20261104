import YM.Integration.WilsonPositionSeparatedProfileFiniteMean
import YM.Integration.WilsonPositionSeparatedProfileTranslatedMass

/-! A signed compact experiment carried to the original translated coarse census.
Every fine term, coarse site, and source position is retained. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileTranslatedTest
open Function Filter Finset Set MeasureTheory Lattice Wilson RG OPE.Therm
open RG05Readout Address Native Pulse Harvest RG05Readout.Flatten MergeProof Accent
open scoped Classical BigOperators Topology
variable {G : Gauge} (C : Family G) (law : C.Makes) {N per n u : ℕ}
  (top : n+1≤N) (span : u≤n)

def field (X : C(Config G (C.side N per),ℂ)) (f : Body) (V : Config G (C.side u per)) : ℂ :=
  pulls C per N n 0 top (fun _=>X) u span f V/((C.path.rep N per u).eval V:ℂ)

include law
theorem mean (X : C(Config G (C.side N per),ℂ)) (f : Body) :
    (∫V,field C top span X f V ∂scene C.path N per u)=moment (C.beta N per) X :=
  WilsonPositionSeparatedProfileTranslatedMass.original C law N per top span X f

theorem integrable (X : C(Config G (C.side N per),ℂ)) (f : Body) :
    Integrable (field C top span X f) (scene C.path N per u) := by
  have date : u≤N := span.trans ((Nat.le_succ _).trans top)
  apply actualScene_integrable_of_weighted C law date
  let Y := pulls C per N n 0 top (fun _=>X) u span f
  have budget : Integrable Y (prior G _) :=
    beacons law top (fun _=>X) span (fun _=>X.continuous) f
  change Integrable (fun V=>(C.path.rep N per u).eval V • (Y V/((C.path.rep N per u).eval V:ℂ))) _
  have cancel (V : Config G (C.side u per)) :
      (C.path.rep N per u).eval V • (Y V/((C.path.rep N per u).eval V:ℂ))=Y V := by
    rw [Complex.real_smul,←mul_div_assoc,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr
      (Multi.AxisShift.chosen_positive law.wilson date V).ne')]
  simpa only [cancel] using budget

variable {I : Type} [DecidableEq I] [Fintype I] (s : I→ℕ) (v : (i : I)→Palette C (s i))
  (φ : Wave I) (r : ℝ) (m : ℕ) (g : Body)
local notation "Z" => Site (C.side (n+1) per)
local notation "raw" => constellation (C:=C) (p:=per) s v r φ top m
local notation "bud" => fun z : Z=>restricted C (n+1) per z g
local notation "a" => C.S.a (n+1)

theorem tested (live : ∀f : Body,Continuous (raw f)) {cap B fee : ℝ} (rp : 0<r)
    (enclosed : ∀y∈tsupport φ.val,∀i,‖y i‖≤cap)
    (places : r*cap+2*a<C.S.radius per) (period : B+r*cap<C.S.radius per)
    (space : B+a<C.S.radius per) (support : ∀y∈Function.support g.val,‖y‖≤B)
    (f : Body) (Y : Z → Config G (C.side u per)→ℂ) (finite : ∀z,Integrable (Y z) (scene C.path N per u))
    (price : ∀z,(∫V,‖field C top span ⟨raw (bud z),live (bud z)⟩ f V-Y z V‖ ∂scene C.path N per u)≤
      fee*(∫y in Native.box,‖(bud z).val y‖)) :
    ‖moment (C.beta N per) (physicalEra r φ g C m per N s v)-
      (a:ℂ)^4*(∑z:Z,∫V,Y z V ∂scene C.path N per u)‖≤fee*(∫y,‖g.val y‖) := by
  let W (z : Z) : C(Config G (C.side N per),ℂ) := ⟨raw (bud z),live (bud z)⟩
  let μ:=scene C.path N per u
  have cost (z : Z) : ‖moment (C.beta N per) (raw (bud z))-(∫V,Y z V ∂μ)‖≤fee*(∫y in Native.box,‖(bud z).val y‖) := by
    change ‖moment (C.beta N per) (W z)-(∫V,Y z V ∂μ)‖≤_
    rw [←mean C law top span (W z) f,←integral_sub (integrable C law top span (W z) f) (finite z)]
    exact (norm_integral_le_integral_norm _).trans (price z)
  rw [WilsonPositionSeparatedProfileFiniteMean.registry C s v φ r m top g live rp enclosed places period space support,
    ←mul_sub,←Finset.sum_sub_distrib,norm_mul,norm_pow,Complex.norm_real,
    Real.norm_of_nonneg (C.S.a_pos _).le,←WilsonPositionSeparatedProfileFiniteMean.volume C (b:=n+1) g space support]
  calc a^4*‖∑z:Z,(moment (C.beta N per) (raw (bud z))-(∫V,Y z V ∂μ))‖≤a^4*(∑z:Z,fee*(∫y in Native.box,‖(bud z).val y‖)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg (C.S.a_pos _).le _)
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun z _=>cost z))
       _ = _ := by rw [←Finset.mul_sum];ring

end YM.Integration.WilsonPositionSeparatedProfileTranslatedTest
