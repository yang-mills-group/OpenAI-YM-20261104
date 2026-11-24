import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.RealSectors
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SignedAxes
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.PublicAxes
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Tangents
open YM YM.Maxwell YM.Maxwell.Free YM.XSpace.Normalize
open YangMills.MSbar
variable {g:YangMills.GaugeGroup}{d:ℕ}

theorem original (T:FieldEnd g.core d):
    T∈Change g.core d ↔ Position.IsChange (IssuedMaxwell.Reference.issued g) d T:=by
  constructor
  · rintro ⟨unit,nesting,real,axes⟩
    refine ⟨?_,nesting,(IssuedMaxwell.RealSectors.original T).mp real,?_⟩
    · intro p hp
      have eq:p=leaf g.core d:=Subtype.ext hp
      exact eq ▸ unit
    intro σ sign U hsign hU p q law
    obtain ⟨s,rfl,rfl,rfl⟩:=IssuedMaxwell.PublicAxes.original σ sign U hsign hU
    rw [IssuedMaxwell.SignedAxes.original] at law ⊢
    rw [law]
    exact axes s p
  · intro H
    refine ⟨H.unit _ rfl,H.filtration,(IssuedMaxwell.RealSectors.original T).mpr H.real,?_⟩
    intro s p
    let q := ori s.ortho d p
    have law:YangMills.Matching.RelatedByAxes (IssuedMaxwell.Reference.issued g)
        s.perm (tilt s) (Ortho.motion s.ortho) p.val q.val:=
      (IssuedMaxwell.SignedAxes.original s p q).mpr rfl
    have sign (i:Axis):tilt s i=1 ∨ tilt s i= -1:=by
      unfold tilt
      split <;> simp
    exact (IssuedMaxwell.SignedAxes.original s (T p) (T q)).mp
      (H.signedAxes _ _ _ sign (heads s) p q law)
end IssuedMaxwell.Tangents
end
