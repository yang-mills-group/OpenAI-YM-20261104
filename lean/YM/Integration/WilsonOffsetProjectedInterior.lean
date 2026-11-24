import YM.Integration.WilsonOffsetSourceBasis
import YM.Integration.WilsonPhysicalMarkedDefectStoredInterior

/-! The arbitrary-depth genuine incoming factory, split at its actual two
fine sites on the same positive physical conditional. The unsubtracted
signed remainder consists of the failed primary, every soft row and the full hard gas. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOffsetProjectedInterior
open Function MeasureTheory Lattice RG Wilson Source Labels Push.Local Extra.Histories
open WilsonTranslatedFactory WilsonOffsetTraceHistory WilsonOffsetConditionalCharge
open WilsonPhysicalMarkedDefect.StoredInterior
open scoped Classical BigOperators
variable {G:Gauge} {C:Family G} {N p d m:ℕ}
local notation "S" => C.path.levels.clock.op m p
local notation "P" => C.path.rep N p (m+1)
local notation "F" => C.labels.level d

def payload (v:C.label d) := (F).scaled (P).p.threshold⁻¹ ((F).core (((C.factory d N p).entries (m+1) v).x))

def primaryAt (v:C.label d) (y:Site (C.side (m+1) p)) :=
  (C.localSection d).places (payload (N:=N) (p:=p) (m:=m) v) y

def rest (v:C.label d) (y:Site (C.side (m+1) p)) (U:Config G (C.side (m+1) p)) : ℂ :=
  let Q:=(C.factory d N p).entries (m+1) v
  let X:=pull (1:Signed) y U
  failed C N p d (m+1) Q X + (∑' i, Q.maskedTerm P i X) + hard C N p d (m+1) Q X

def gap (W: Site (C.side (m+1) p) → Config G (C.side (m+1) p) → ℂ)
    (z:Site (C.side (m+1) p)) (U:Config G (C.side (m+1) p)):ℂ :=
  W z U-W ((S).ratio.embed ((S).ratio.parent z)) U

theorem registered (law:C.Makes) (hm:m<N) (v:C.label d) (y:Site (C.side (m+1) p))
    (U:Config G (C.side (m+1) p)) :
    material law hm y v U/((P).eval U:ℂ) = ((C.factory d N p).entries (m+1) v).x 0 +
      primaryAt (N:=N) (p:=p) (m:=m) v y U + rest (N:=N) (p:=p) (m:=m) v y U :=by
  let Q:=(C.factory d N p).entries (m+1) v
  let g:=((law.wilson.represents N p (m+1) hm).good.labels.moves (1:Signed) y).some
  have nat: ((P).eval (pull (1:Signed) y U):ℂ)=((P).eval U:ℂ):=congrArg Complex.ofReal (eval_pull g U)
  have hh:=resolved C N p d (m+1) law hm Q (pull (1:Signed) y U)
  have pos: fitted C N p d (m+1) Q (pull (1:Signed) y U)=primaryAt (N:=N) (m:=m) v y U:=by
    rw [←primary C N p d (m+1) law hm Q, pull_one,SectionData.places_trans,zero_add]
    rfl
  have both:=congrFun (density law hm y v) U
  change material law hm y v U / ((P).eval U:ℂ)=Q.x 0+_+_
  change material law hm y v U=Q.density 0 (C.localSection d) P (pull (1:Signed) y U) at both
  rw [nat,pos] at hh
  rw [both,hh]
  unfold rest
  ring

theorem differential (law:C.Makes) (hm:m<N) (v:C.label d) (z:Site (C.side (m+1) p))
    (U:Config G (C.side (m+1) p)) :
    forward law hm z v U =
      gap (primaryAt (N:=N) (p:=p) (m:=m) v) z U+gap (rest (N:=N) (p:=p) (m:=m) v) z U :=by
  dsimp only [forward,gap]
  rw [sub_div,registered law hm v,registered law hm v]
  ring

private theorem raw_paid (law:C.Makes) (hr:C.ref d ≤ m) (hm:m<N) (z:Site (C.side (m+1) p)) (v:C.label d) :
    Integrable (fun U=>((P).eval U:ℂ)*forward law hm z v U) (prior G (C.side (m+1) p)) :=by
  have b:(fun U=>((P).eval U:ℂ)*forward law hm z v U)=
      fun U=>material law hm z v U-material law hm ((S).ratio.embed ((S).ratio.parent z)) v U:=by
    funext U
    have nz:=SectorNext.Vacuum.strictly C.path law.wilson N p (m+1) hm U
    unfold forward;rw [←mul_div_assoc,mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr nz.ne')]
  rw [b]
  exact (integrable law hm (hr.trans m.le_succ) z v).sub (integrable law hm (hr.trans m.le_succ) _ v)

theorem subtract (law:C.Makes) (hr:C.ref d ≤ m) (hm:m<N) (z:Site (C.side (m+1) p)) (v:C.label d)
    (V:Config G (C.side m p)) :
    WilsonTwoOffsetTrace.saw law hm z v V/((C.path.rep N p m).eval V:ℂ) =
      ((C.S.block m).val:ℂ)^d*(conditional S P V (gap (primaryAt (N:=N) (m:=m) v) z) +
      conditional S P V (gap (rest (N:=N) (m:=m) v) z)) :=by
  let X:=gap (primaryAt (N:=N) (m:=m) v) z
  let Y:=gap (rest (N:=N) (m:=m) v) z
  let M:=fun U:Config G (C.side (m+1) p)=>((P).eval U:ℂ)
  have poly : Continuous X:=(C.localSection d).continuous_places _ z |>.sub ((C.localSection d).continuous_places _ _)
  have hx:Integrable (fun U=>M U*X U) (prior G _):=((Envelope.ofReal_env ((P).envelope
    (law.wilson.represents N p (m+1) hm).good)).mulC (Envelope.compactC poly)).integrableC _
  have all: (fun U=>M U*forward law hm z v U)=(fun U=>M U*X U+M U*Y U):=by
    funext U
    rw [differential law hm v z U,mul_add]
  have hy:Integrable (fun U=>M U*Y U) (prior G _):=by
    have raw:=raw_paid law hr hm z v
    have eq:(fun U=>M U*forward law hm z v U-M U*X U)=fun U=>M U*Y U:=by
      funext U
      rw [congrFun all U]
      ring
    rw [←eq]
    exact raw.sub hx
  rw [observed law hr hm z v V]
  congr 1
  simp only [conditional,←add_div]
  congr 1
  exact (congrArg (fun A=>(S).push (P).beta A V) all).trans (congrFun
    (StepData.push_add (C.path.levels.transition_mass m p (P).beta) _ _ hx hy) V)

end YM.Integration.WilsonOffsetProjectedInterior
