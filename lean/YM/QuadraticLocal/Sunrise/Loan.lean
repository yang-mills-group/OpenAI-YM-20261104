import YM.AllOrder.Floe.Guards
import YM.QuadraticLocal.Fk.Climate
import YM.Comparison.Density.Render.Valence
/-!
# Install insertions for an honest train

`Loan` spectral label. grades not necessarily shift by derivative-only. We will claim tall
power Mark analytically from any rank/p temporal finite through ceiling, with smoothness paid.
 On all Ad and all positions (illumination), still not crop of real coarser.Label. Stamp currency
 defined by g (same as vacuum) raised to ENOUGH through E+r+h; then heating shifted spectrum
 upstairs. Shift is paid cumulatively (`h` will be the *sum over mode of primitive Marker weights*,
 not added to any ages after traveling). Width posture still separate. Only for analytic pieces.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Sunrise
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open ConnectedActivityE6 Blaze
open AbsoluteSums Org
open Comparison.RG02 AllOrder AllOrder.Floe AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method Laurent
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet  Comparison.RG02 Assembly Bulk
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j p τ N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}

structure Loan where
 e : ℕ
 r : ℕ
 toll : ℕ
 higher : 0<toll
 crest : r≤ e+toll+1
 deriving DecidableEq
namespace Loan
variable (i:Loan)
abbrev power := i.toll+1
def lag : ℤ := ↑i.e-↑i.r
def stamp:= i.e+i.toll+1-i.r
lemma recovery : i.stamp+i.r=i.e+i.toll+1:= Nat.sub_add_cancel i.crest
lemma stamped : (i.stamp:ℤ)=i.power+i.lag:=by unfold lag power; have h:=i.recovery; omega
-- Inputs written into Colours.R; tree/g.t rescale with constant g
variable (u:Atom G i.r)(x:Site f)(t:ℝ)
def letter (t:ℝ): Config G f→ℝ:= fun U=> t^i.stamp * u.unmasked U x
lemma emission (ht:t≠0) (U:Config G f) : (t^i.power)⁻¹* letter i u x t U=t^i.lag*u.unmasked U x:=by
   unfold letter; rw [←zpow_natCast t i.stamp,i.stamped,zpow_add₀ ht,zpow_natCast,mul_assoc (t^i.power)] -- candidate
   exact inv_mul_cancel_left₀ (pow_ne_zero _ ht) _
-- eligibility
lemma natural (he:u.Invariant): GaugeInvariant (letter i u x t):= by intro z y; unfold letter Atom.unmasked; simp_rw [Work.F05.slot_gauge]; exact congr_arg (t^i.stamp*·) (he _ _)
lemma conti : Continuous (letter i u x t):= continuous_const.mul (Atom.unmasked_cont ..)
lemma bound : Envelope (letter i u x t):= ⟨(conti i u x t).measurable,isCompact_univ.exists_bound_of_continuousOn (conti i u x t).continuousOn|>.imp (fun B h U=> h U (Set.mem_univ _))⟩ -- name fn?
-- pole analytic in Wilson coupling convention (singular at actual due g^lag, yet the smoothed mark power handled by Lens). Requires flat derivatives only at grade r.
lemma mature (k:ℕ)(v:Atom G k)(x:Site f): GradeAt k (projected (fun _ (U:Config G f)=> v.unmasked U x)):= by
   let g(y:Directions G f):= v.unmasked (increment 1 y) x;
   have hh : ContDiffAt ℝ ω (fun z=> Work.F02.atomExt v x (Work.F02.physical (increment 1 z))) 0 := (Work.F02.atomExt_contDiff v x).restrict_scalars ℝ |>.contDiffAt.comp 0 (Work.F02.physical_contDiffAt (A:=increment 1) fun i=> by simp only [increment,G.mat_mul]; exact ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const).contDiffAt)
   have hg : GradeAt k g:= ⟨ by
      convert Complex.reCLM.contDiff.contDiffAt.comp _ hh using 1; ext1; simp only [g,Function.comp_apply, Work.F02.atomExt_physical,Complex.reCLM_apply,Complex.ofReal_re],fun i hi=> Comparison.Density.Render.valuation _ i hi _⟩
   let ℓ (z:ℝ × Exterior.fieldDir G f 1): Directions G f:= Exterior.collect _ (n:=f) z.2; exact GradeAt.coarse (g:=ℓ) hg ((by apply ContDiff.contDiffAt; unfold ℓ Exterior.collect; fun_prop) : ContDiffAt ℝ ω ℓ 0) rfl
lemma frame : GradeAt (i.power+i.e) (projected (letter i u x)):= by
   have hm:i.stamp+i.r=i.power+i.e:= i.recovery.trans (by unfold Loan.power; omega); rw [←hm]; exact (GradeAt.shifts Prod.fst contDiffAt_fst rfl i.stamp).mul (mature i.r u x)
variable (F:Forest S.ratio)
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "X"=> (Apex c G × Poll.Body (Precision.Key F G))
local notation "E"=> ℝ×(Apex c G × Poll.Body (Precision.Key F G))
abbrev leafMatter : (Apex c G × Poll.Body (Precision.Key F G)) → ℝ := fun y=> u.unmasked (fine G F (combineH F y)) x
lemma healthy : GradeAt i.r (leafMatter i u x F):= GradeAt.coarse («g»:=fun (z:Apex c G × Poll.Body (Precision.Key F G))=> ((0:ℝ), slidL F z)) (joint_receipt S F (mature i.r u x)) (contDiffAt_const.prodMk (show ContDiffAt ℝ ω (slidL (G:=G) F) 0 from ContinuousLinearEquiv.contDiff _|>.contDiffAt)) (by exact Prod.ext rfl (map_zero (slidL F)))
-- at a stationary coordinate radiation `(whole Fine,...)` already includes mean shift. Not heating yet.
def alloy (k:ℕ) : X→ℝ:= if i.e+i.toll ≤k then Radial.jet (leafMatter i u x F) (k-(i.e+i.toll)+i.r) else 0
lemma gone : alloy i u x F 0=0:= if_neg (by have := i.higher; omega)
lemma outline (k:ℕ): Rank (Apex c G × Poll.Body (Precision.Key F G)) (k+1) (alloy i u x F k):=by
   unfold alloy; split; · exact (Project.maturity (leafMatter i u x F) _).up (by have := i.crest; omega)
   exact Rank.nil _ 0
-- identify on Bulk.Kernel tree heat ruler. elementary power shift before Leg.P.N.
lemma alloyJ (d:ℕ)(y:X) : alloy i u x F d y= Assembly.jet (Bulk.posed S F (letter i u x)) (d+1) (QuadraticLocal.Fk.Dress.trim G F (1,y)):= by
   let X':=(Apex c G × Poll.Body (Precision.Key F G)); let η:= QuadraticLocal.Fk.Dress.trim G F; let f:=(posed S F (letter i u x)); have H := joint_receipt S F (frame i u x)
   change _ = Assembly.jet (posed S F (i.letter u x)) (d+1) (η.toContinuousLinearMap (1,y))
   rw [← Assembly.jet_continuous_right η.toContinuousLinearMap (H.smooth.of_le le_top)] -- may want show compose
   change alloy i u x F d y=Radial.jet (fun z:ℝ×X' => z.1^i.stamp * leafMatter i u x F z.2) (d+1) (1,y)
   unfold alloy; split
   next he=> rw [favor_exp (leafMatter i u x F) (healthy i u x F).smooth, if_pos (show i.stamp≤d+1 by have ht:=i.recovery; omega),one_pow,one_mul]; congr 2; have ht:=i.recovery; omega
   next he=> exact (favor_pocket _ (healthy i u x F).smooth (i.e+i.toll+1) _ _ _ (healthy i u x F).vanish 1 y i.recovery.symm (by omega)).symm
end Loan
end YM.QuadraticLocal.Sunrise
