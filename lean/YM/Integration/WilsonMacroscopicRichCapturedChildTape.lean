import YM.Integration.WilsonMacroscopicRichChildRegistration
import YM.RG05Readout.Address.Shape
import YM.RG05Readout.Suede.Silver

/-! On the actual finite trajectory the compensated physical source has zero
projected label on the whole submitted tape, including its forced terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichCapturedChildTape
open Lattice Wilson RG Source RG16.Literal Trace.Physical.GermGraph RG05Readout RG05Readout.Native
open RG05Readout.Address
open scoped BigOperators Classical
variable {G : Gauge} (C : Family G) (H : C.Makes) {d n N p : ℕ}

def center (d : ℕ) : Letter d := ⟨⟨0,Nat.zero_lt_succ d⟩,Suede.pip.2⟩

def tape (q : store C d p n) : Tape G (C.side n p) :=
  glyph (readJ (center d) 0) (Address.invoice q 0 (C.localSection d) (C.path.rep N p n))

theorem filed (ho : Opened C d n p) (live : n≤N) (A : Cut C N p)
    (report : topReport C N p d H n ho live A=0) (q : store C d p n) {e : ℝ}
    (fee : reads d N p n q e) (issued : credit C N p d A n live=value (C:=C) d N p n q) :
    Printed C d (C.path.rep N p n) 0 (Push.Local.kappa C.path n) (tape (N:=N) C q)
      (chunk (C:=C) (center d) q.x) 0 e ∧
    ∀ φ, pulseOut (tape (N:=N) C q) φ=readJ (center d) 0 φ • credit C N p d A n live := by
  have pageZero : page (C:=C) d p n q=0 := by
    unfold topReport at report
    rw [readPage_eq C N p d A H live ho.post q fee issued] at report
    simpa using congrArg (fitting d N p n H ho live) report
  have vac := (H.wilson.represents N p n live).vac
  have proj : Trace.Physical.Germ.projection (C.labels.level d) C.params
      (C.path.rep N p n).p.threshold 0 q=0 := by rw [vac]; exact pageZero
  have row := printed_one (C:=C) (center d) q fee.1 fee.2
  change Printed _ _ _ _ _ (tape (N:=N) C q) _ (chunk (C:=C) (center d)
      (Trace.Physical.Germ.projection (C.labels.level d) C.params
        (C.path.rep N p n).p.threshold 0 q)) _ at row
  rw [proj] at row
  change Printed C d _ 0 _ (tape (N:=N) C q) (chunk (C:=C) (center d) q.x)
    (chunk (C:=C) (center d) (0 : C.label (kept (center d)))) e at row
  have zero : chunk (C:=C) (center d) 0 = 0 := Pi.single_zero ..
  rw [zero] at row
  refine ⟨row,fun φ => ?_⟩
  rw [issued]
  rfl

def source (ho : Opened C d n p) (live : n≤N) (Y : Cut C N p) : Cut C N p :=
  Y-C.O N p (WilsonMacroscopicRichChildRegistration.returned C H ho live Y) 0

theorem original (ho : Opened C d n p) (live : n≤N) (Y : Cut C N p) (cY : Continuous Y)
    (book : Booked C N p d Y n live) :
    ∃ (q : store C d p n) (e : ℝ), reads d N p n q e ∧
      credit C N p d (source C H ho live Y) n live=value (C:=C) d N p n q ∧
      Printed C d (C.path.rep N p n) 0 (Push.Local.kappa C.path n) (tape (N:=N) C q)
        (chunk (C:=C) (center d) q.x) 0 e ∧
      ∀ φ, pulseOut (tape (N:=N) C q) φ=readJ (center d) 0 φ •
        credit C N p d (source C H ho live Y) n live := by
  obtain ⟨⟨q,e,fee,hq⟩,zero⟩:=WilsonMacroscopicRichChildRegistration.null C H ho live Y cY book
  exact ⟨q,e,fee,hq,filed C H ho live _ zero q fee hq⟩

end YM.Integration.WilsonMacroscopicRichCapturedChildTape

