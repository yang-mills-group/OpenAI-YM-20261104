import YM.RG12.Common.Consume
import YM.RG12.Joint.Grant
import YM.RG12.Canonical.Conclude
import YM.UVExtension.Reports.Ultraviolet
import YM.EveryPhase.Extension

/-!
# Joint construction and conditional sharp OPE on measurements

Can select from `package` INSTEAD of `common_uv_every_phase`. No assertion that the classical
choice in those files is safe to specialize to RG12: it doesn't expose the extra facilities.
`prepared` (another separate witness) already exports AllShapes -- here actually running
that machinery on the UV provider with the new joint ledger, without choosing separately or
weakening UV and every phase targets. Includes open hypotheses on measurements, so neither
this existential nor the generic consumers yet prove physical sharpness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12
open OPE Filter MergeProof
open scoped Topology BigOperators Classical
variable (G:Gauge)

theorem assembled (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) (order:Extraction.Order):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (L:EveryPhase.Almanac U),
      C.Makes∧ Spec.Calibrated C∧
      C.path.levels.clock.kernel.penalty=penalty∧
      UVExtension.Oasis.Floral (hG:=hG) C∧
      (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T∧
      (∀ d k:ℕ,∀ᶠ n:ℕ in atTop,
        ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i, (v i).1 ≤ d)→ ∃ g,UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧
      ∃ (Q:Prescription U.sector.derivatives)(hq:Q.Coherent),
        AllShapes U Q ∧ (∃ (P:Commission.Port C)(lit:ℕ→Prop), Rail.Outbound P lit U.room.cutoff ∧
       (∀ (b:Filter UVIndex) [b.NeBot], b ≤ (order.refine f).fuse→∀ M, Observing C U.room.cutoff b M→ Rail.Assembly U P lit M Q hq b) ∧ ∀ ax:Axis, (∀ d:ℕ,4 ≤ d→ Arche.Drives.March U ax Q hq d) → (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q) ∧ ((∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→
          ∀ M, Observing C U.room.cutoff b M → ∀ d, 4 ≤ d→ FramesInput U.sector.derivatives Q hq M d) →
          LogTrace U Q):=by
  obtain ⟨C,hA,hC,hM,hWC,hF,⟨P,_,lit,HP⟩,hG',H,hL,h⟩:= PhysicalNext.Repeat.Legato.RG12Joint.lit_construct hG hp
  obtain ⟨f,A,V,R,T,B,hA',s,hN⟩:=h order
  obtain ⟨hs,hGate⟩:= hL (order.refine f) s.copies
  obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=B) H hG hs hGate s hA'.clean.ready hA'.clean.tilt
  obtain ⟨U⟩:= Acme.glistens hC hA'.clean.ready hA'.clean.tilt p
  obtain ⟨L,hL⟩:= EveryPhase.all_characters U
  obtain ⟨w,z,Z,u⟩:= hG'
  have hH:Facilities C (order.refine f) T:= ⟨⟨hs,hG,⟨w,z,Z,u.toPackage⟩,A,V,R,B,hA'⟩,w,z,Z,u⟩
  obtain ⟨Q,hQ⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
  exact ⟨C,f,T,U,L,hM,hC,hA,hF,UVExtension.Reports.useFull hF ⟨U⟩, UVExtension.Poppy.bravo (UVExtension.Oasis.appears hF),hL,hH,
    Q,hQ,hH.toServices.everything U Q hQ,⟨P,lit,HP,fun _ _ z _ v=> Rail.charter hG U P HP hH Q hQ v z,fun a=> Arche.Drives.reading_sharp U a P HP.covered hG hH Q hQ⟩,sharp_from_measurements U hG hH Q hQ⟩
theorem fully_started (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) (order:Extraction.Order):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (L:EveryPhase.Almanac U),
      C.Makes∧ Spec.Calibrated C∧
      C.path.levels.clock.kernel.penalty=penalty∧
      UVExtension.Oasis.Floral (hG:=hG) C∧
      (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T∧
      (∀ d k:ℕ,∀ᶠ n:ℕ in atTop,
        ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i, (v i).1 ≤ d)→ ∃ g,UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧
      ∃ (Q:Prescription U.sector.derivatives)(hq:Q.Coherent),
        AllShapes U Q ∧ (∃ P:Commission.Port C, Commission.Covered P U.room.cutoff ∧ ∀ ax:Axis, (∀ d:ℕ,4 ≤ d→ Arche.Drives.March U ax Q hq d) → (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q) ∧ ((∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→
          ∀ M, Observing C U.room.cutoff b M → ∀ d, 4 ≤ d→ FramesInput U.sector.derivatives Q hq M d) →
          LogTrace U Q):=by
  obtain ⟨C,f,W,X,Z,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,Q,hq,h₉,⟨P,lit,Y,-,hY⟩,H⟩:= assembled G hG penalty hp order
  exact ⟨C,f,W,X,Z,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,Q,hq,h₉,⟨P,Y.covered,hY⟩,H⟩
theorem package (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) (order:Extraction.Order):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (L:EveryPhase.Almanac U),
      C.Makes∧ Spec.Calibrated C∧
      C.path.levels.clock.kernel.penalty=penalty∧
      UVExtension.Oasis.Floral (hG:=hG) C∧
      (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T∧
      (∀ d k:ℕ,∀ᶠ n:ℕ in atTop,
        ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i, (v i).1 ≤ d)→ ∃ g,UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧
      ∃ (Q:Prescription U.sector.derivatives)(hq:Q.Coherent),
        AllShapes U Q ∧ ((∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→
          ∀ M, Observing C U.room.cutoff b M → ∀ d, 4 ≤ d→ FramesInput U.sector.derivatives Q hq M d) →
          LogTrace U Q):=by
  obtain ⟨C,f,W,X,Z,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,Q,hq,h₉,-,H⟩:= fully_started G hG penalty hp order
  exact ⟨C,f,W,X,Z,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈,Q,hq,h₉,H⟩
end YM.RG12
