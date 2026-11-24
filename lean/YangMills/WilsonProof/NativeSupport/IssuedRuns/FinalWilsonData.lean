import YangMills.WilsonProof.NativeSupport.IssuedRuns.PhysicalRunning
import YangMills.WilsonProof.NativeSupport.IssuedRuns.GradedTokens

set_option autoImplicit false

namespace IssuedRuns.FinalWilsonData

open YangMills YangMills.Wilson Filter
open scoped Topology
noncomputable section

variable {g : GaugeGroup}

private theorem reflectedSite {l : ℕ+} (x : Site l) :
    YM.Lattice.affine (YM.Signed.mirror timeAxis) 0 x = timeMirror x := by
  funext i
  by_cases h : i = timeAxis
  · subst i
    simp [YM.Lattice.affine, YM.Signed.act, YM.Signed.mirror, timeMirror]
  · simp [YM.Lattice.affine, YM.Signed.act, YM.Signed.mirror, timeMirror, h, Ne.symm h]

private theorem reflectedLinks {l : ℕ+} (U : Configuration g l) :
    YM.Lattice.pull (YM.Signed.mirror timeAxis) 0 U = timeMirrorLinks U := by
  funext e
  rcases e with ⟨x,i⟩
  change (YM.Lattice.Step.rotate (YM.Lattice.posDir i) (YM.Signed.mirror timeAxis)).read U
      (YM.Lattice.affine (YM.Signed.mirror timeAxis) 0 x) = _
  rw [reflectedSite]
  by_cases h : i = timeAxis
  · subst i
    rfl
  · simp [YM.Lattice.posDir, YM.Lattice.Step.rotate, YM.Signed.mirror, YM.Lattice.Step.read,
      YM.Lattice.Step.used, timeMirrorLinks, h, Ne.symm h]

def original (C : YM.Family g.core) (qualified : C.Makes)
    (hg : g.IsSimple) (B : Maxwell.Reference g) : WilsonData B (wilsonFamily C) where
  regular := IssuedRuns.PhysicalRunning.regular C qualified hg B
  positive := (IssuedRuns.PhysicalRunning.original C qualified hg B).1
  running := (IssuedRuns.PhysicalRunning.original C qualified hg B).2
  translate N p v x b U := (C.translation (N := N) (p := p) x b v.2 U).symm
  conjugate := C.book.conjugate
  conjugate_involutive := by
    rintro ⟨d,v⟩
    exact congrArg (fun w : C.book.Ref d => (⟨d, w⟩ : C.book.Token)) (star_star v)
  starToken := C.book.reflectedToken timeAxis
  star_involutive := by
    rintro ⟨d,v⟩
    exact congrArg (fun w : C.book.Ref d => (⟨d, w⟩ : C.book.Token)) (C.book.reflected d timeAxis v)
  reality v := by
    filter_upwards [eventually_ge_atTop (C.ref v.1)] with N hn
    intro p x U
    exact C.reality qualified hn v.2 x U
  reflection v := by
    filter_upwards [eventually_ge_atTop (C.ref v.1)] with N hn
    intro p x U
    change C.O N p (C.book.adj v.1 timeAxis v.2) (timeMirror x) U =
      star (C.O N p v.2 x (timeMirrorLinks U))
    rw [← reflectedSite, ← reflectedLinks]
    exact (C.rotated qualified hn (star v.2) (YM.Signed.mirror timeAxis) x 0 U).trans
      (C.reality qualified hn v.2 x _)

  raw := IssuedRuns.GradedTokens.original C qualified


end
end IssuedRuns.FinalWilsonData
