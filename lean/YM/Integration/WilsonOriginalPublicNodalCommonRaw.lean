import YM.Integration.WilsonOriginalPublicNodalSafeCenter
import YM.Integration.WilsonOriginalPublicNodalHelperShape

/-! Two complete, separately clocked cover runs use a single finite normalized bare observable. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicNodalCommonRaw
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Geometry RegulatorIR.Binding RegulatorIR.Budget RegulatorIR.Budget.Layer
open RegulatorIR.Budget.Packet RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Prim RegulatorIR.Gain
open RegulatorIR.Halo RegulatorIR.Taping RegulatorIR.Ledger RegulatorIR.Ledger.Sky RegulatorIR.Uniform RegulatorIR.Motion
open WilsonIndependentRawRosterOrbit (report)
open WilsonIndependentRawRosterWord (film)
open WilsonIndependentRawRosterBudget (span)
open WilsonOriginalPublicNodalSafeCenter (moved)
open scoped Classical ENNReal NNReal
variable {G:Gauge}{X I:Type}{p:ℕ}

/-- A paid schedule. The two schedules need share only the actual opening torus and the submitted raw film. -/
structure Court (G:Gauge)(X:Type)(p:ℕ) where
  M:X → ℕ
  n:Page M → Side
  S:Heir n G
  V:Reel S
  T:S.Accounts
  Γ:Flap M → Layer (Foot G) (Foot G)
  B:Flap M → Bride G
  L:Meter X
  cash:Flap M → ℝ≥0∞
  b:ℕ
  u:ℕ
  D:Choice M
  γ:ℝ
  funds:Cylinder V T Γ B L cash p b u
  light:Lantern S D L cash γ
  ends:V.Endings L
  pass:Passage V
  common:Common V
  unit:∀x,S.l (Page.opening M x)=1
  flat:∀x,V.clock (Page.opening M x)=Clocks.flat

variable (R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)(σ:I → Bool)(d:I → ℕ)
    (key:∀i,(R.family.labels.level (d i)).Index)(arms:Composite I)

def fee (A:Court G X p)(H:ℝ)(k:ℕ)(stop:Choice A.M)(x:X):ℝ:=
  H*(A.L.val x).toReal^k*A.S.modifyErr 0 A.b A.γ stop x

def prior (A:Court G X p)(H:ℝ)(k:ℕ)(stop:Choice A.M)(x:X):ℝ:=
  H*(A.L.val x).toReal^k*(A.S.l (stop.choose x)^A.γ)⁻¹

def value (A:Court G X p)(sites:X → I → Cover)(atPage:Page A.M)(q:ℕ):ℂ:=
  note ((report R W σ d key arms A.T sites).main atPage q 0)

def raw (sample:Sample 2)(sites:I → Cover)(q:ℕ):ℂ:=
  PowerSeries.coeff q (Bare.normalized (W.tree sample.F.p) G (film R W σ d key sample sites arms))

def Offered (A:Court G X p)(sample:X → Sample 2)(sites:X → I → Cover)(x:X → Room)(c₀:ℝ):Prop:=
  (∀w,TopF A.n w=(sample w).F.p.side) ∧
  (∀w,ENNReal.ofReal (1+span (x w) (sites w) arms) ≤ A.L.val w) ∧ 0<c₀ ∧ A.S.cushion c₀ x

theorem stopped (A:Court G X p)(sample:X → Sample 2)(sites:X → I → Cover)(x:X → Room)
    (c₀:ℝ)(ok:Offered arms A sample sites x c₀)(stop:Choice A.M)(later:A.D.age ≤ stop.age)(q:ℕ)(hq:q≤p):
    ∃H:ℝ,∃k:ℕ,0≤H ∧ ∀w,‖raw R W σ d key arms (sample w) (sites w) q-
      value R W σ d key arms A sites (stop.choose w) q‖≤fee A H k stop w:=
  WilsonIndependentRawRosterOrbit.stopped R W σ d key arms sites A.funds A.light A.ends sample x A.unit A.flat
    ok.1 ok.2.1 ok.2.2.1 ok.2.2.2 q hq stop later

theorem intersection (A B:Court G X p)(sample:X → Sample 2)(sites:X → I → Cover)(x:X → Room)
    (c₁ c₂:ℝ)(left:Offered arms A sample sites x c₁)(right:Offered arms B sample sites x c₂)
    (j:Choice A.M)(k:Choice B.M)(earA:A.D.age ≤ j.age)(earB:B.D.age ≤ k.age)
    (s t:X → Cover)(q:ℕ)(hq:q≤p):
    ∃U V H:ℝ,∃u v h:ℕ,0≤U ∧ 0≤V ∧ 0≤H ∧ ∀n:Page k.after.spans,
      let w:=n.bindW
      let z:=moved A.V j s sites
      let y:=moved B.V k t sites
      let a₀:=value R W σ d key arms A z (j.choose w) q
      let b₀:=value R W σ d key arms B y (k.after.page n) q
      ‖a₀-raw R W σ d key arms (sample w) (sites w) q‖ ≤ fee A U u j w ∧
      ‖raw R W σ d key arms (sample w) (sites w) q-b₀‖ ≤ fee B V v k w+prior B H h k w ∧
      ‖a₀-b₀‖ ≤ fee A U u j w+fee B V v k w+prior B H h k w:=by
  obtain ⟨U,u,hU,a⟩:=stopped R W σ d key arms A sample sites x c₁ left j earA q hq
  obtain ⟨V,H,v,h,hV,hH,b⟩:=WilsonOriginalPublicNodalSafeCenter.original R W σ d key arms sites
    B.funds B.light B.ends B.pass B.common sample x B.unit B.flat right.1 right.2.1 right.2.2.1 right.2.2.2
    k earB t q hq
  refine ⟨U,V,H,u,v,h,hU,hV,hH,?_⟩
  intro n w z y a₀ b₀
  have same:=WilsonOriginalPublicNodalOrbitShift.scalar A.V R W σ d key arms sites z A.pass A.common
    A.funds.port (j.choose w) (s w) (fun _=>rfl) q
  have eq:a₀=value R W σ d key arms A sites (j.choose w) q:=congrArg ((↑):ℝ → ℂ) same
  have first:‖a₀-raw R W σ d key arms (sample w) (sites w) q‖ ≤ fee A U u j w:=by
    rw [eq,norm_sub_rev]
    exact a w
  have second:‖raw R W σ d key arms (sample w) (sites w) q-b₀‖ ≤ fee B V v k w+prior B H h k w:=b n
  refine ⟨first,second,?_⟩
  calc
    _ ≤ ‖a₀-raw R W σ d key arms (sample w) (sites w) q‖+‖raw R W σ d key arms (sample w) (sites w) q-b₀‖:=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

end YM.Integration.WilsonOriginalPublicNodalCommonRaw
end
