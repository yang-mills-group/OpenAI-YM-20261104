import YM.Integration.WilsonOriginalNullPlacedJointMeasured

/-! The sum of the measured coordinates of two live carriers is
determined by their joint physical credit, even when neither full
credit has been refiled as a single regular and hard inventory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedJointBalance
open Function Filter Lattice RG Wilson WardBin.Lies Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open ProjectorNext.Equivariance Next.Foundations Push.Local WilsonCapturedPrimaryReading
open scoped Classical Topology ContDiff
variable {G:Gauge} (C:Family G) (d N p i:ℕ) (o:Site (C.side i p))
local notation "F₀" => C.labels.level d
local notation "S₀" => C.localSection d
local notation "P₀" => C.path.rep N p i

structure Account (W:Rep G (C.side i p)) (h k:Coefficient F₀ (C.side i p)) : Prop where
  first : h.Format o C.params W
  second : k.Format o C.params P₀
  bought : ∃ κ a, h.remBound o W κ a
  funded : ∃ υ b, k.remBound o P₀ υ b

def coordinate (W:Rep G (C.side i p)) (h k:Coefficient F₀ (C.side i p)) : C.label d :=
  projection F₀ C.params W.p.threshold o h+projection F₀ C.params (P₀).p.threshold o k

theorem measured (H:C.Makes) (live:i ≤ N) (home:Opened C d i p) (W:Rep G (C.side i p))
    (same:W.p=(P₀).p) (quiet:∀ U,W.eval U=(P₀).eval U) (h k:Coefficient F₀ (C.side i p))
    (paid:Account C d N p i o W h k) (t:Probe G d) :
    runProbe F₀ t (coordinate C d N p i o W h k)=jet C.params t (P₀).p.threshold o
      (fun U=>(h.density o S₀ W U+k.density o S₀ P₀ U)/((P₀).eval U:ℂ)) := by
  obtain ⟨κ,a,hp⟩:=paid.bought;obtain ⟨υ,b,kp⟩:=paid.funded
  have dims:=dimensions d N p i H home.post live
  have so:=H.sections d
  have fit:=H.places d i p home.post
  have path:=sections_visit H home.post o
  have dW:d ≤ W.p.order:=same.symm ▸ dims.1
  have pW:d ≤ W.p.power:=same.symm ▸ dims.2
  have hd:=WilsonCapturedPrimarySmooth.original so dW path paid.first hp
  have kd:=WilsonCapturedPrimarySmooth.original so dims.1 path paid.second kp
  have raw:reading S₀ W o h+reading S₀ P₀ o k=
      (fun U=>(h.density o S₀ W U+k.density o S₀ P₀ U)/((P₀).eval U:ℂ)):=by
    funext U;simp only [Pi.add_apply,reading];rw [quiet U,add_div]
  unfold coordinate
  rw [map_add,WilsonCapturedPrimaryReading.probe so fit dW pW path paid.first hp hd,
    WilsonCapturedPrimaryReading.probe so fit dims.1 dims.2 path paid.second kp kd,same,←raw]
  exact (WilsonOriginalNullPlacedJointGerm.add hd kd t (P₀).p.threshold).symm

theorem original (H:C.Makes) (live:i ≤ N) (home:Opened C d i p) (W:Rep G (C.side i p))
    (same:W.p=(P₀).p) (quiet:∀ U,W.eval U=(P₀).eval U) (h k v w:Coefficient F₀ (C.side i p))
    (first:Account C d N p i o W h k) (second:Account C d N p i o W v w)
    (held:∀ U,h.density o S₀ W U+k.density o S₀ P₀ U=v.density o S₀ W U+w.density o S₀ P₀ U) :
    coordinate C d N p i o W h k=coordinate C d N p i o W v w := by
  apply probes_injective F₀;intro t
  rw [measured C d N p i o H live home W same quiet h k first t,
    measured C d N p i o H live home W same quiet v w second t]
  exact congrArg (jet C.params t (P₀).p.threshold o) (funext fun U=>congrArg (·/((P₀).eval U:ℂ)) (held U))

end YM.Integration.WilsonOriginalNullPlacedJointBalance
