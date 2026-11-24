import YM.FVAAlt2.Booth.Uniforms
import YM.FVAAlt2.Retro.Earn
/-!
# Supply (unmasked only) complete analytic representative for curves GIVEN certified sheet from actual path

Supplies finite order holomorphic Ward and markers. This task not costing integration, so HUGE unfunded elongated paths allowed, no qlocal admission costs. Needed because a label through period borrow is not a proof of able to represent `Bulk.Fk` same data at next level. Each such representation usable at all orders up to that certificate. Real local kernel normalization conceived via actual charge gauges. Numerical error costs & {flags,Std.Height5} are not supplied by this germ proof!

Also avoid analytic at coupling away from origin requirements: build a finite sharp rep.Notebook accepts smooth real, ψ analytic not needed at radius.Fixed.Seal. Actual.Values remain in user R.reset, not replacing them.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Repop
open RG Wilson Tree Exterior Lattice Precision MeasureTheory
open Comparison.RG02 Symmetry Symmetry.Orbit Comparison.RG02.Moving Moving.Path Moving.Shift Valence Assembly Adjacent
open Filter Function Set Finset Push.SectorMeasure Gauge Integral ConnectedActivityE6
open PertExtension.Series PertExtension.Series.Tested
open Booth Booth.Uniforms YM.FVAAlt2.Block.Render
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G: Gauge} {n:Side} {V:Type}
variable {δ γ:ℝ}
local notation "X"=> fieldDir G n 1
local notation "A"=> Config G n
local notation "D"=> Display (fieldDir G n 1)
variable (C:UnitCost)(T:Display (fieldDir G n 1))(r m:ℕ)(h: Sheet r T)(H: Booth.Uniforms.Valid T r m)
variable (hc:Reliable G δ γ)(χ:Chi)
local notation "T₀"=> Adjacent.born T C.inverseCurve 0 r
def garment (δ:ℝ)(t:ℝ)(U:A):ℂ:= YM.FVAAlt2.Block.Render.gift χ (Adjacent.born T C.inverseCurve 0 r) m δ r t U
local notation "M"=> garment C T r m χ δ
local notation "φ"=> C.enter
local notation "τ"=> C.rating
variable (x:fieldDir G n 1)
include H
lemma ticketed (C':UnitCost): Adjacent.Charge r (fun i=> Booth.Uniforms.ceiling m i) (Adjacent.born T C' 0 r):= affordable 0 r H.heft C' (fun i j (hi:i≤j)=> by dsimp; omega)
include h
lemma sheeted : Symmetry.Orbit.Sheet r (T₀) := Call.certified 0 r H.heft _ h
include hc
lemma warm : Assembly.GradeAt m (Bulk.projected (garment C T r m χ δ)):= introduced χ hc (T₀) ( sheeted C T r m h H ) m
lemma gauged (s:ℝ): GaugeInvariant (garment C T r m χ δ s):= YM.FVAAlt2.Block.Render.gauged χ hc (T₀) (sheeted C T r m h H) m s
lemma earned_c (s:ℝ) : Continuous (garment C T r m χ δ s):= funded χ hc (T₀) (sheeted C T r m h H) m s
lemma invoice (i:ℕ)(hi:i≤r): Assembly.jet ( Bulk.projected (M) ) (m+i) (1,x)= T₀ i x := earned χ hc T₀ (sheeted C T r m h H) m (ticketed T r m H C.inverseCurve) x i hi
omit H h hc
-- radial product λ^m compensated transport; controls all grades up to m+r. proof at moving coarse contours, needed by grade-e Hessian read in Fk next.
def supplies (C:UnitCost)(m:ℕ)(U':ℝ→ Config G n →ℂ) (y:ℝ→ fieldDir G n 1)(t:ℝ):ℂ:= ((C.rating t)^m)⁻¹ • U' (C.enter t) (sample t (y t))
local notation:max "p_" f:max=> Comparison.RG02.Adjacent.cover f r
section degree
open scoped PowerSeries
private lemma shifts {p q:ℝ→ℂ}(h:Adjacent.Shadow r p q): Adjacent.Shadow (r+m) (fun t:ℝ=>(t:ℂ)^m*p t) (fun t:ℝ=>(t:ℂ)^m*q t):=by
    have ht:ContDiffAt ℝ ω (fun t:ℝ=>(t:ℂ)^m) 0:= Complex.ofRealCLM.contDiff.contDiffAt.pow _
    refine ⟨ht.mul h.left,ht.mul h.right,fun i hi=>?_⟩; rw [mono_price h.left,mono_price h.right]; split_ifs with he; · exact h.aligns (i-m) (by omega)
    rfl
end degree
include H h hc
lemma scopedAt (y:ℝ→ fieldDir G n 1) (hy : glows y): Adjacent.Shadow (r+m) (supplies C m (garment C T r m χ δ) y) (fun t:ℝ=>(t:ℂ)^m* cover T r t (y t)):=by
    let z : ℝ→X := Call.shuttle y C.inverseCurve
    have hz: glows z:= Call.lifts y C.inverseCurve hy
    let L:= T₀; let U:= garment C T r m χ δ
    have he:Adjacent.Shadow (r+m) (fun s:ℝ=> U s (sample s (z s))) (fun s=>(s:ℂ)^m*(cover L r s (z s))):= evaluate χ hc L (sheeted C T r m h H) m (ticketed T r m H C.inverseCurve) z hz
    have hp:= he.respite C; -- check order
    let a(t:ℝ):ℂ:= ↑(( (τ t)^m)⁻¹)
    have hA: ContDiffAt ℝ ω a 0:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ ((C.smooth.pow _).inv (by simp [C.origin]))
    let w:= ( Shadow.refl (r:=r+m) hA ).product hp
    suffices ha : Adjacent.Shadow r (fun t=> cover L r (C.enter t) (z (C.enter t))) (fun t=> cover T r t (y t)) by
       have h₁: supplies C m (M) y=ᶠ[𝓝 0] fun t=> a t*U (C.enter t) (sample (C.enter t) (z (C.enter t))) := by
          filter_upwards [Call.tag_returns y C.rightInverse,C.bright] with t ht hT
          change ( (τ t)^m)⁻¹ • U (C.enter t) (sample t (y t))=_
          rw [show z (C.enter t)=_ from ht, sample,sample,show (C.enter t) • _=t • y t from (show (C.enter t) • ((C.rating t)⁻¹ • y t)= t • y t by rw [smul_smul,UnitCost.enter,mul_assoc,mul_inv_cancel₀ hT.ne',mul_one]),Complex.real_smul]
       let W := fun t:ℝ=>(t:ℂ)^m*(cover L r (C.enter t) (z (C.enter t)))
       have h₂ :(fun t=> a t* ( (C.enter t:ℂ)^m*(cover L r (C.enter t) (z (C.enter t))) )) =ᶠ[𝓝 0] W:= by
          filter_upwards [C.bright] with t ht
          have hh:(↑(C.rating t):ℂ) ≠0:= Complex.ofReal_ne_zero.mpr ht.ne'
          unfold W a UnitCost.enter; push_cast; field_simp; ring
       change Adjacent.Shadow (r+m) (supplies C m U y) _; exact ( (Adjacent.Shadow.same (r:=r+m) h₁.symm w.left).symm.trans w ).trans ( (Shadow.same h₂ w.right).trans (shifts r m ha))
    have hm:= (curvedAt 0 r (U:=L) (ticketed T r m H C.inverseCurve) C y hy).symm; -- hm: shadow ages at t -> $
    have hu : (fun t=> cover L r (C.enter t) (z (C.enter t)))=ᶠ[𝓝 0] fun t=> ages L 0 r t (C.rating t) (y t):=by
        filter_upwards [Call.tag_returns y C.rightInverse] with t ht; change cover L r _ _=_; rw [show z (C.enter t)= _ from ht]; unfold ages; rw [zpow_zero,Complex.ofReal_one,one_mul];rfl
    have hw:          -- cost curves
        (fun t=>cover (born L C 0 r) r t (y t))=fun t=>cover T r t (y t):=by
        funext t; unfold cover; apply sum_congr rfl; intro i hi; rw [show born L C 0 r i=T i from reverse 0 r H.heft C.rightInverse.symm i ( Finset.mem_range_succ_iff.mp hi )]
    rw [ ← hw ]; exact ( Shadow.same hu.symm hm.left ).symm.trans hm
lemma entered (i:ℕ) (hi:i≤r): motion (supplies C m (garment C T r m χ δ) (fun _=>x)) (m+i)= T i x:=by
    have hv:= Call.escort (fun _=>x) contDiffAt_const r h.known; rw [ (scopedAt C T r m h H hc χ (fun _=>x) contDiffAt_const).aligns (m+i) (by omega), mono_price hv]; rw [if_pos (by omega),show m+i-m=i from by omega]; exact (by
      change motion (fun t:ℝ=> Adjacent.cover T r t x) i=_; rw [show (fun t:ℝ=> Adjacent.cover T r t x)= peval (fun i=>T i x) r from funext fun t=> by unfold peval cover Zone.eval; simp [Complex.real_smul], Adjacent.polary,if_pos hi])
end YM.RegulatorIR.FVAAlt2.Repop
