import YM.Integration.WilsonOriginalPublicNodalOrbitShift
import YM.Integration.WilsonOriginalPublicNodalOrbitStops

/-! The prescribed inversion stays at its own safe center. Only the complete stopped cover is recentered. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalSafeCenter
open Function Lattice RG Source Labels PertExtension XSpace
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform
open RegulatorIR.Motion XSpace.Rose XSpace.Cirrus
open WilsonIndependentRawRosterOrbit (report)
open WilsonIndependentRawRosterWord (film)
open WilsonIndependentRawRosterBudget (span)
open WilsonOriginalPublicNodalOrbitShift (stride scalar)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{J I:Type}{M:J→ℕ}{n:Page M→Side}{S:Heir n G}{V:Reel S}{T:S.Accounts}
    {Γ:Flap M→Layer (Foot G) (Foot G)}{B:Flap M→Bride G}{p b u:ℕ}
    {D:Choice M}{L:Meter J}{cash:Flap M→ℝ≥0∞}{γ c₀:ℝ}
    (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I→Bool)(d:I→ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)

def moved (V:Reel S)(stop:Choice M)(t:J → Cover)(sites:J→I → Cover)(w:J)(i:I):Cover:=
  sites w i+stride V (stop.choose w) (t w)

def center (V:Reel S)(stop:Choice M)(t:J → Cover)(x:J→Room)(w:J):Room:=
  x w+slide 1 (stride V (stop.choose w) (t w))

theorem geometry (x:Room)(sites:I → Cover)(t:Cover):
    span (x+slide 1 t) (fun i=>sites i+t) arms=span x sites arms:=by
  induction arms with
  | atom i => simp [span,dist_add_right]
  | pair a b ha hb => change _+_=_+_;rw [ha,hb]

variable (sites:J→I → Cover)(A:Cylinder V T Γ B L cash p b u)(lantern:Lantern S D L cash γ)
    (ends:V.Endings L)(pass:Passage V)(common:Common V)
    (sample:J→Sample 2)(x:J→Room)(start:∀w,S.l (Page.opening M w)=1)
    (clock:∀w,V.clock (Page.opening M w)=Clocks.flat)(same:∀w,TopF n w=(sample w).F.p.side)
    (fare:∀w,ENNReal.ofReal (1+span (x w) (sites w) arms)≤L.val w)
    (clear:0<c₀)(safe:S.cushion c₀ x)
include A lantern ends pass common start clock same fare clear safe

theorem original (stop:Choice M)(old:D.age ≤ stop.age)(t:J → Cover)(q:ℕ)(hq:q≤p):
    ∃C H:ℝ,∃k l:ℕ,0≤C ∧ 0≤H ∧ ∀v:Page stop.after.spans,
      let w:=v.bindW
      ‖PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G
        (film R W σ d key (sample w) (sites w) arms))-
        (note ((report R W σ d key arms T (moved V stop t sites)).main (stop.after.page v) q 0):ℂ)‖ ≤
      C*(L.val w).toReal^k*S.modifyErr 0 b γ stop w+
      H*(L.val w).toReal^l*(S.l (stop.choose w)^γ)⁻¹:=by
  let homes:=moved V stop t sites
  let x':=center V stop t x
  have repay(w:J):ENNReal.ofReal (1+span (x' w) (homes w) arms)≤L.val w:=by
    change ENNReal.ofReal (1+span (x w+slide 1 (stride V (stop.choose w) (t w)))
      (fun i=>sites w i+stride V (stop.choose w) (t w)) arms)≤L.val w
    rw [geometry]
    exact fare w
  obtain ⟨C,k,hC,read⟩:=WilsonIndependentRawRosterOrbit.stopped R W σ d key arms sites A lantern ends sample x
    start clock same fare clear safe q hq stop old
  obtain ⟨H,l,hH,carry⟩:=WilsonOriginalPublicNodalOrbitStops.original R W σ d key arms homes A lantern x'
    start repay stop old q hq
  refine ⟨C,H,k,l,hC,hH,?_⟩
  intro v w
  let z:=report R W σ d key arms T sites
  let z':=report R W σ d key arms T homes
  have translate':note (z'.main (stop.choose w) q 0)=note (z.main (stop.choose w) q 0):=
    scalar V R W σ d key arms sites homes pass common A.port (stop.choose w) (t w) (fun _=>rfl) q
  let Y:=PowerSeries.coeff q (Bare.normalized (W.tree (sample w).F.p) G (film R W σ d key (sample w) (sites w) arms))
  have one:‖Y-(note (z'.main (stop.choose w) q 0):ℂ)‖≤C*(L.val w).toReal^k*S.modifyErr 0 b γ stop w:=by
    rw [translate']
    exact read w
  have two:‖(note (z'.main (stop.choose w) q 0):ℂ)-(note (z'.main (stop.after.page v) q 0):ℂ)‖ ≤
      H*(L.val w).toReal^l*(S.l (stop.choose w)^γ)⁻¹:=by
    rw [norm_sub_rev,←Complex.ofReal_sub,Complex.norm_real]
    exact carry v
  exact (norm_sub_le_norm_sub_add_norm_sub ..).trans (add_le_add one two)

end YM.Integration.WilsonOriginalPublicNodalSafeCenter
end
