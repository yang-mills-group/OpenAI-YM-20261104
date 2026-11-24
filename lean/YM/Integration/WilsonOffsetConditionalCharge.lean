import YM.Integration.WilsonTwoOffsetTrace
import YM.MSbar.LocalSD.Expect
import YM.SectorNext.VACUUM_NORMALIZATION.Stripped

/-! The conditional actually acting on a displaced source, including both
old signed fields and the physical normalization. At birth the native
engineering factor cancels before its true finite site sections are read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetConditionalCharge
open Function MeasureTheory Lattice RG Wilson Source Extraction WilsonOffsetTraceHistory
open WilsonTranslatedFactory WilsonTwoOffsetTrace
open scoped Classical
variable {G:Gauge} {C:Family G} {N p m d:ℕ}

def conditional {c f:Side} (S:StepData c f) (P:Rep G f) (V:Config G c) (f:Config G f→ℂ) : ℂ :=
  S.push P.beta (fun U=>(P.eval U:ℂ)*f U) V / ((S.push P.beta P.eval V:ℝ):ℂ)

def forward (H:C.Makes) (hm:m<N) (z:Site (C.side (m+1) p)) (v:C.label d) : Config G (C.side (m+1) p)→ℂ :=
  let S:=C.path.levels.clock.op m p
  let e:=S.ratio.embed (S.ratio.parent z)
  fun U=>(material H hm z v U-material H hm e v U)/((C.path.rep N p (m+1)).eval U:ℂ)

private theorem push_sub {c f:Side} {S:StepData c f} {β:ℝ} (kernel:S.IsKernel β G)
    (X Y:Config G f→ℂ) (hx:Integrable X (prior G _)) (hy:Integrable Y (prior G _)) (V:Config G c) :
    S.push β (fun U=>X U-Y U) V=S.push β X V-S.push β Y V := by
  simp only [StepData.push,smul_sub]
  rw [integral_sub (StepData.push_slice kernel V X hx) (StepData.push_slice kernel V Y hy)]

theorem observed (H:C.Makes) (hr:C.ref d ≤ m) (hm:m<N) (z:Site (C.side (m+1) p))
    (v:C.label d) (V:Config G (C.side m p)) :
    saw H hm z v V / ((C.path.rep N p m).eval V:ℂ) =
      ((C.S.block m).val:ℂ)^d * conditional (C.path.levels.clock.op m p) (C.path.rep N p (m+1)) V
        (forward H hm z v) := by
  let S:=C.path.levels.clock.op m p
  let e:=S.ratio.embed (S.ratio.parent z)
  let P:=C.path.rep N p (m+1)
  let Q:=C.path.rep N p m
  let X:=material H hm z v; let Y:=material H hm e v
  have weight: (fun U=>(P.eval U:ℂ)*forward H hm z v U)=(fun U=>X U-Y U):=by
    funext U
    have pos:0<P.eval U:=SectorNext.Vacuum.strictly C.path H.wilson N p (m+1) hm U
    change (P.eval U:ℂ)*((X U-Y U)/(P.eval U:ℂ))=_
    rw [←mul_div_assoc,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr pos.ne')]
  have paid:=transfer H hr hm (S.ratio.parent z) v
  have pos:=integrable H hm (hr.trans m.le_succ) z v
  have neg:=integrable H hm (hr.trans m.le_succ) e v
  have inv : Q.eval V=S.push P.beta P.eval V :=congrFun (H.wilson.steps N p m hm).1 V
  have wave:=push_sub (C.path.levels.transition_mass m p P.beta) X Y pos neg V
  change (((C.S.block m).val:ℂ)^d*S.push P.beta X V-material H hm.le (S.ratio.parent z) v V)/
    (Q.eval V:ℂ)= _ * (S.push P.beta (fun U=>(P.eval U:ℂ)*forward H hm z v U) V/((S.push P.beta P.eval V:ℝ):ℂ))
  have aligned : material H hm.le (S.ratio.parent z) v V=((C.S.block m).val:ℂ)^d*S.push P.beta Y V :=
    congrFun paid V
  rw [aligned,weight,wave,inv]
  ring

theorem born_difference (H:C.Makes) (hr:C.ref d ≤ m+1) (z:Site (C.side (m+1) p)) (v:C.label d)
    (U:Config G (C.side (m+1) p)) :
    let S:=C.path.levels.clock.op m p
    let x:=(C.labels.level d).scaled (C.path.levels.clock.threshold (m+1))⁻¹ v
    forward H (N:=m+1) (Nat.lt_succ_self m) z v U =
      (C.localSection d).places x z U-(C.localSection d).places x (S.ratio.embed (S.ratio.parent z)) U := by
  let P:=C.path.rep (m+1) p (m+1)
  let x:=(C.labels.level d).scaled (C.path.levels.clock.threshold (m+1))⁻¹ v
  have hp:0<P.eval U:=SectorNext.Vacuum.strictly C.path H.wilson (m+1) p (m+1) le_rfl U
  have a: (C.S.a (m+1):ℂ)^d ≠ 0 :=pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
  have atSite (y:Site (C.side (m+1) p)) :
      material H (N:=m+1) le_rfl y v U=(P.eval U:ℂ)*(C.localSection d).places x y U:=by
    unfold material
    rw [born H hr y v U]
    change (C.S.a (m+1):ℂ)^d*(P.eval U:ℂ)*(((C.S.a (m+1):ℂ)^d)⁻¹*(C.localSection d).places x y U)=_
    field_simp
  dsimp only [forward]
  rw [atSite,atSite]
  change ((P.eval U:ℂ)*_-(P.eval U:ℂ)*_)/(P.eval U:ℂ)=_
  rw [←mul_sub,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hp.ne')]

end YM.Integration.WilsonOffsetConditionalCharge
