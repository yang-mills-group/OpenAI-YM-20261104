import YM.Integration.WilsonLocalCompactLinearity

/-! The conditional linear expectations act on the original bounded
gauge-invariant observables. Centering a product removes the disconnected
means on either probability law. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalCompactProbability
open MeasureTheory Lattice RG Wilson
open scoped Classical Topology
variable (G:Gauge) (n:Side)

def observables:Subalgebra ℝ (Config G n→ℝ) where
  carrier:=fun f=>Envelope f ∧ GaugeInvariant f
  zero_mem':=⟨Envelope.const 0,fun _ _=>rfl⟩
  one_mem':=⟨Envelope.const 1,fun _ _=>rfl⟩
  add_mem' :=fun hf hh=>⟨hf.1.add hh.1,fun a U=>congrArg₂ (·+·) (hf.2 a U) (hh.2 a U)⟩
  mul_mem' :=fun hf hh=>⟨hf.1.mul hh.1,fun a U=>congrArg₂ (·*·) (hf.2 a U) (hh.2 a U)⟩
  algebraMap_mem' c:=⟨Envelope.const c,fun _ _=>rfl⟩

variable {G n}
abbrev Signal:=↥(observables G n)

def enrolled {f:Config G n→ℝ} (ef:Envelope f) (gf:GaugeInvariant f):Signal (G:=G) (n:=n):=⟨f,ef,gf⟩

def read {Y:Type} [MeasurableSpace Y] {K:(Config G n→ℝ)→Y→ℝ}
    (valid:WilsonLocalCompactLinearity.Laws K) (y:Y):Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ where
  toFun F:=K F y
  map_add' F H:=by
    have v:=congrFun (valid.mix F H F.2.1 H.2.1 1) y
    change K (fun x=>F.1 x+H.1 x) y=K F y+K H y
    simpa only [one_mul] using v
  map_smul' a F:=by
    have v:=congrFun (valid.mix (fun _=>0) F (Envelope.const 0) F.2.1 a) y
    change K (fun x=>a*F.1 x) y=a*K F y
    simpa only [zero_add,valid.constant] using v

theorem unit {Y:Type} [MeasurableSpace Y] {K:(Config G n→ℝ)→Y→ℝ}
    (valid:WilsonLocalCompactLinearity.Laws K) (y:Y):read valid y (1:Signal (G:=G) (n:=n))=1:=
  congrFun (valid.constant 1) y

def absolute (F:Signal (G:=G) (n:=n)):Signal (G:=G) (n:=n):=by
  refine enrolled (f:=fun x=>|F.1 x|) ⟨F.2.1.meas.abs,F.2.1.cost.choose,fun x=>?_⟩
    (fun a U=>congrArg abs (F.2.2 a U))
  simpa only [Real.norm_eq_abs,abs_abs] using F.2.1.cost.choose_spec x

variable (P:Signal (G:=G) (n:=n)→ₗ[ℝ]ℝ)
def center (F:Signal (G:=G) (n:=n)):Signal (G:=G) (n:=n):=F-P F • 1
def spread (F:Signal (G:=G) (n:=n)):ℝ:=P (absolute (center P F))

theorem zero (p:P 1=1) (F:Signal (G:=G) (n:=n)):P (center P F)=0:=by
  simp [center,p]

def covariance (F H:Signal (G:=G) (n:=n)):ℝ:=P (F*H)-P F*P H
def third (F H J:Signal (G:=G) (n:=n)):ℝ:=
  P (F*H*J)-P F*P (H*J)-P H*P (F*J)-P J*P (F*H)+2*P F*P H*P J

theorem translated (one:P 1=1) (F H:Signal (G:=G) (n:=n)) (a b:ℝ):
    covariance P (F-a•1) (H-b•1)=covariance P F H:=by
  simp only [covariance,mul_sub,sub_mul,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
    map_sub,map_smul,one,smul_eq_mul]
  ring

theorem translated_three (one:P 1=1) (F H J:Signal (G:=G) (n:=n)) (a b c:ℝ):
    third P (F-a•1) (H-b•1) (J-c•1)=third P F H J:=by
  simp only [third,mul_sub,sub_mul,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,
    map_sub,map_smul,one,smul_eq_mul]
  ring

end YM.Integration.WilsonLocalCompactProbability
