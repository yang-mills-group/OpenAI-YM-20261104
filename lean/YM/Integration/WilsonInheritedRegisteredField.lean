import YM.Integration.WilsonTranslatedFactory
import YM.Integration.ActualTrajectoryTransport
import YM.MergeProof.Cashew

/-! The original measured microscopic insertion at an embedded point and its
complete calibrated insertion on an arbitrary earlier Wilson field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInheritedRegisteredField
open Function MeasureTheory Lattice RG Wilson Source Push.Local MergeProof
open scoped Classical
variable {G : Gauge} {C : Family G} (h : C.Makes) {N per k d : ℕ}

def packet (hk : k ≤ N) (w : C.label d) (o : Site (C.side k per)) :=
  WilsonTranslatedFactory.entry h hk o ((C.factory d N per).terminal.symm w)

def field (hk : k ≤ N) (w : C.label d) (o : Site (C.side k per))
    (U : Config G (C.side k per)) : ℂ :=
  alto C.path k d * (packet h hk w o).density o (C.localSection d) (C.path.rep N per k) U /
    ((C.path.rep N per k).eval U : ℂ)

private theorem nest {c f n : Side} (u : Ratio c f) (v : Ratio f n) (w : Ratio c n)
    (o : Site c) : w.embed o = v.embed (u.embed o) := by
  have scale : w.count.val = v.count.val * u.count.val := by
    apply Nat.eq_of_mul_eq_mul_left c.property
    calc c.val*w.count.val = n.val := w.exact_size.symm
         _ = (c.val*u.count.val)*v.count.val := by rw [v.exact_size,u.exact_size]
         _ = c.val*(v.count.val*u.count.val) := by ring
  change wrap n (w.count.val • lift o) = wrap n (v.count.val • lift (u.embed o))
  rw [u.lift_embed,scale,mul_smul]

private theorem same {c : Side} (u : Ratio c c) (o : Site c) : u.embed o = o := by
  have scale : u.count.val = 1 :=
    Nat.eq_of_mul_eq_mul_left c.property (u.exact_size.symm.trans (Nat.mul_one c.val).symm)
  rw [Ratio.embed,scale,one_smul,wrap_lift]

private theorem step (hr : C.ref d ≤ k) (hk : k < N) (w : C.label d)
    (o : Site (C.side k per)) :
    actualAverage C (N:=N) (field h hk w ((C.path.levels.clock.op k per).ratio.embed o)) =
      field h hk.le w o := by
  let S := C.path.levels.clock.op k per
  let y := S.ratio.embed o
  let A := C.path.rep N per (k+1)
  let Z := packet h hk w y
  let f := Z.density y (C.localSection d) A
  let t := (C.factory d N per).terminal.symm w
  have sale := WilsonTranslatedFactory.based h (hr.trans k.le_succ) hk y t
  have live : Integrable f (prior G _) :=
    (Z.envelope (C.localSection d) (h.wilson.represents N per (k+1) hk).good sale.2 sale.1).integrableC _
  have restore : (fun U => A.eval U • field h hk w y U) = alto C.path (k+1) d • f := by
    funext U
    have nz : (A.eval U : ℂ) ≠ 0 := by exact_mod_cast (Multi.AxisShift.chosen_positive h.wilson hk U).ne'
    change (A.eval U:ℂ)*(alto C.path (k+1) d * f U / (A.eval U:ℂ))=alto C.path (k+1) d * f U
    field_simp
  funext V
  rw [actualAverage_push]
  change ((C.path.rep N per k).eval V)⁻¹ • S.push _ (fun U => A.eval U • field h hk w y U) V =
    field h hk.le w o V
  rw [restore,S.push_smul f _ _ live]
  unfold field
  rw [show (packet h hk.le w o).density o (C.localSection d) (C.path.rep N per k) =
    ((C.S.block k).val:ℂ)^d • S.push (C.path.β N per (k+1)) f from
      WilsonTranslatedFactory.transfer h hr hk o t]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv]
  rw [alto_at]
  ring

/-- The same original upper label and its full earlier coefficient, including
its old signed amplitudes and the original positive vacuum. -/
theorem original (hk : k ≤ N) (hr : C.ref d ≤ k) (w : C.label d)
    (o : Site (C.side k per)) :
    actualTransport C (N:=N) (C.O N per w ((C.S.toDepth hk per).embed o)) hk =
      field h hk w o := by
  induction hk using Nat.decreasingInduction with
  | self =>
    rw [same,actualTransport_base C h (le_refl N)]
    funext U
    unfold field packet
    rw [WilsonTranslatedFactory.born h hr o ((C.factory d N per).terminal.symm w)]
    have a : (C.S.a N : ℂ) ≠ 0 := by exact_mod_cast (C.S.a_pos N).ne'
    have vac : ((C.path.rep N per N).eval U : ℂ) ≠ 0 := by
      exact_mod_cast (Multi.AxisShift.chosen_positive h.wilson (le_refl N) U).ne'
    change _ = (((C.S.a N:ℂ)^d)⁻¹ * ((C.S.a N:ℂ)^d * _ * C.O N per w o U)) / _
    field_simp
  | of_succ j hj ih =>
    rw [nest (C.path.levels.clock.op j per).ratio (C.S.toDepth hj per) (C.S.toDepth hj.le per),
      actualTransport_step C h (le_refl N) _ hj,ih (hr.trans j.le_succ)]
    exact step h hr hj w o

end YM.Integration.WilsonInheritedRegisteredField
