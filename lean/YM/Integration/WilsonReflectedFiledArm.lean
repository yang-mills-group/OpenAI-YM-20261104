import YM.Integration.WilsonReflectedPlacedArm
/-! The actually funded earlier signed coefficient, heard with either
conjugation and its own physical origin/orientation. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedFiledArm
open Push Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonPositionProgramOriginalBlockedTrial WilsonAddressedRestartedColumn WilsonReflectedOriginalTwoDeposit
open WilsonReflectedPlacedArm
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N p f:ℕ}
local notation "C₀" => R.family
local notation "space" i:max => Config G ((C₀).side i p)
local notation "P₀" i:max => (C₀).path.rep N p i

def evaluated (d:ℕ)(z:store (C₀) d p f)(b:Bool)(s:Signed)(o:Site ((C₀).side f p))(W:space f):ℂ:=
  RelayDifference.hand b (z.density 0 ((C₀).localSection d) (P₀ f) (pull s o W))

theorem original (d n:ℕ)(upper:f+n≤N)(ready:(C₀).ref d≤f)(y w:(C₀).label d)
    {B:ℝ}{z:store (C₀) d p f}(file:WilsonAddressedRestartedFiled.Filed R d N p f 0
      (track R d N p (f+n) (numerator R d N p (f+n) 0 w) f-
        calValues (C:=C₀) d N p f (((C₀).factory d N p).terminal.symm y)) B z)
    (b:Bool)(s:Signed)(o:Site ((C₀).side f p))(W:space f):
    let step:=Nat.le_add_right f n
    let old:=WilsonReflectedPlacedArm.original R d (step.trans upper) y b s o
    let new₀:=trial R (N:=N) d step w b s o
    evaluated R (N:=N) d z b s o W=
      ((C₀).S.a f:ℂ)^d*((P₀ f).eval W:ℂ)*(actualTransport (C₀) (N:=N) new₀ step W-held R old f W):=by
  intro step old new₀
  let W':=pull s o W
  let I:=atZero R d N p (f+n) w
  let J:space N→ℂ:=(C₀).O N p y 0
  have pI:Envelope I:=paid R d N p (f+n) w
  have pJ:Envelope J:=Envelope.compactC ((C₀).continuousO ..)
  have ksrc:=WilsonReflectedTwoGridFields.restarted R d n upper 0 w W'
  have nsrc:=WilsonReflectedTwoGridFields.raw R d (step.trans upper) ready 0 y W'
  simp only [Motion.embed_origin] at ksrc nsrc
  have kpass:=WilsonReflectedMotionGrid.returned R upper step b s o I pI W
  have npass:=WilsonReflectedMotionGrid.returned R (le_refl N) (step.trans upper) b s o J pJ W
  have v:((P₀ f).eval W' : ℝ)=(P₀ f).eval W:=
    WardBin.Wheels.rep_spins (H:=(C₀).path) s R.makes.wilson (step.trans upper) W o
  have q:=congrFun file.field W'
  simp only [Function.comp_apply,Pi.sub_apply] at q
  rw [ksrc,nsrc,v] at q
  have pow:(((C₀).S.steps f n).val:ℂ)^d=((C₀).S.a f:ℂ)^d*(((C₀).S.a (f+n):ℂ)^d)⁻¹:=by
    have h:((C₀).S.a (f+n):ℂ)≠0:=by exact_mod_cast ((C₀).S.a_pos (f+n)).ne'
    apply (eq_mul_inv_iff_mul_eq₀ (pow_ne_zero d h)).2
    rw [←mul_pow];congr 1;exact_mod_cast spacing R f n
  have once:=linear R upper step _ (facing R I pI b s (((C₀).S.toDepth step p).embed o)) ((((C₀).S.a (f+n):ℂ)^d)⁻¹) W
  simp only [WilsonReflectedOriginalTwoDeposit.held,dif_pos (step.trans upper),new₀,trial,old,WilsonReflectedOriginalTwoDeposit.raw,WilsonReflectedPlacedArm.original]
  rw [once,kpass,npass]
  unfold evaluated
  change RelayDifference.hand b (z.density 0 ((C₀).localSection d) (P₀ f) W')=_
  rw [q,pow]
  change RelayDifference.hand b (_*_*_*actualTransport (C₀) (N:=N) I step W'-_*_*actualTransport (C₀) (N:=N) J (step.trans upper) W')=_
  cases b <;> simp [RelayDifference.hand,W'] <;> ring

end YM.Integration.WilsonReflectedFiledArm
end
