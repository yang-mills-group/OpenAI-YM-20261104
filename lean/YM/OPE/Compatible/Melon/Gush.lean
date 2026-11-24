import YM.OPE.Compatible.Melon.Mind
/-!
# Formal correction in stand, orphan β first germs, same alpha. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Glass
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer Terp
open PertExtension Series Asymptotics MSbar.Tree MSbar.Tree.Resolvent GaussianScore Radial
attribute [local instance] Gauge.frobInner
variable {i:ℕ}{l b:ℝ}{B:Sponsor G}{Q:Seasons B} {A:Alps B Q i l} {H: Even n.val}
local notation "Lf" => Tested.germ
local notation "TK" => Keys G (Limb H)
variable (T:Plot H) (X:Lit H A b) (R:Bor H A b)
local notation "DK" => Keys G T.Stable
local notation "FD" => Keys G T.Free
abbrev layerZ := (T.skews G).gradient
lemma path_rise : X.s.f ∘ layerZ (G:=G) T=ᶠ[𝓝 0] ((R.L T).f ∘ T.slab G)+(hippie H ∘ layerZ T):=by -- parentheses
     let L:=T.skews G; let Y:= L.gradient; let a:= T.rollX (G:=G); let P := a.toContinuousLinearMap.comp (T.slab G)
     have hp:Tendsto P (𝓝 0) (𝓝 0):= by simpa only [P.map_zero] using P.continuous.tendsto 0
     have he:Tendsto Y (𝓝 0) (𝓝 0):= by simpa only [L.grad0,Y] using L.gradC.continuousAt.tendsto
     filter_upwards [he.eventually X.uplift,hp.eventually R.u,T.trail (G:=G)] with x hv hx hT;
     have hh:= muralG H A _ _ _ hT; change X.s.f _=(R.L T).f _+hippie H _; rw [hv]; rw [R.acts]; change mural H A _- _+_= R.f (P x)+ _; rw [hx]; rw [show mural H A (P x)=mural H A (Y x) from hh.1]
lemma path_fall : X.s.w∘ layerZ T=ᶠ[𝓝 0] (R.L T).w ∘ T.slab G:=by
     let L:=T.skews G; let Y:= L.gradient; let P := (T.rollX (G:=G)).toContinuousLinearMap.comp (T.slab G)
     have hp:Tendsto P (𝓝 0) (𝓝 0):= by simpa only [P.map_zero] using P.continuous.tendsto 0
     have he:Tendsto Y (𝓝 0) (𝓝 0):= by simpa only [L.grad0,Y] using L.gradC.continuousAt.tendsto
     filter_upwards [he.eventually X.light,hp.eventually R.t,T.trail (G:=G)] with x hv hx hT; change X.s.w _=(R.L T).w _; rw [R.serves]; change X.s.w _=R.w (P x); rw [hv,hx]; have hk:=muralG H A _ _ _ hT; unfold tintT; rw [show mural H A (P x)= _ from hk.1, show gilt H A (P x)=_ from hk.2]
def ballow (h:4 ≤ i): Lid G (Limb H) := {
   f:= X.s.f∘ layerZ T
   F:= (T.skews G).chore X.s
   fmeas:= X.s.fmeas.comp (T.skews G).meas_grad
   bright:= mast H T X h
   w:= X.s.w ∘ layerZ T
   coat:= ((show ContDiffAt ℝ ∞ X.s.w (layerZ T 0) from by rw [layerZ,Dimes.grad0];exact X.s.coat).comp _ (T.skews G).gradC)
   charm:= by simp only [_root_.Function.comp_apply,layerZ,Dimes.grad0]; exact X.s.charm
   gleams:= X.s.gleams.comp (T.skews G).meas_grad }
def tall (T:Plot H)(x:TK):ℝ:= hippie H (layerZ T x)
lemma tall_sane: ContDiffAt ℝ ∞ (tall T (G:=G)) 0:= (hSm H).contDiffAt.of_le le_top|>.comp _ (T.skews G).gradC
lemma glowN (x:TK)(k:ℕ)(h:4 ≤ i): jet (ballow T X h).f k x= jet (R.L T).f k (T.slab G x)+ jet (tall T) k x:=by
     let D:= T.slab G; let L:= R.L T; have hh : ContDiffAt ℝ (↑k:WithTop ℕ∞) L.f 0:= L.F.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
     have hz: (ballow T X h).f=ᶠ[𝓝 0] (L.f ∘ D)+(tall T):= path_rise T X R
     unfold jet; rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_add_apply ((D.map_zero.symm ▸ hh : ContDiffAt ℝ _ _ _).comp _ D.contDiff.contDiffAt) ((tall_sane T).of_le (WithTop.coe_le_coe.mpr le_top)), Next.Foundations.jets_linear D hh,_root_.add_apply,mul_add]; rfl
lemma wornN (x:TK)(k:ℕ)(h:4 ≤ i): jet (ballow T X h).w k x= jet (R.L T).w k (T.slab G x):=by
     unfold jet; let P:= T.slab G; let L:= R.L T; have hz: (ballow T X h).w=ᶠ[𝓝 0] L.w∘ P:= path_fall T X R; rw [(hz.iteratedFDeriv ℝ k).eq_of_nhds,Next.Foundations.jets_linear P (L.coat.of_le (WithTop.coe_le_coe.mpr le_top))]; rfl
lemma flare (x:FD)(y:DK): jet (tall T) 2 (compass H T G (x,y))=(fond H T G).P y y/2:=by
     unfold jet; change _ * iteratedFDeriv ℝ 2 (hippie H ∘ layerZ T) 0 _=_; rw [slopeJet _ (T.skews G).gradC (T.skews G).grad0 _ (h_station H)]; change jet (hippie H) 2 (T.dtex G _)=_; rw [h_second]; unfold hippie; rw [compass_charge,fond_L];rfl
end YM.OPE.Cascade.Glass
