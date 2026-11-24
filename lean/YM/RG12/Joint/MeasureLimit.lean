import YM.RG12.Joint.Outcome
import YM.RG12.Kintsugi.Guide
import YM.RG12.Common.Consume
import YM.RG12.Joint.MeasureExtension
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

open PhysicalNext.Repeat.Daisy.Charity.RG12
theorem fashions (δ:Decal G) (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) (order:Extraction.Order):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (L:EveryPhase.Almanac U),
      C.Makes∧ Spec.Calibrated C∧
      C.path.levels.clock.kernel.penalty=penalty∧
      UVExtension.Oasis.Floral (hG:=hG) C∧
      (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T∧
      (∀ d k:ℕ,∀ᶠ n:ℕ in atTop,
        ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i, (v i).1 ≤ d)→ ∃ g,UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧ Nonempty (UVExtension.Mast.Couture C hG δ) ∧
      ∃ (Q:Prescription U.sector.derivatives)(hq:Q.Coherent),
        AllShapes U Q ∧ (∃ (P:Commission.Port C)(lit:ℕ→Prop), Alidade.Route P lit U.room.cutoff ∧ Kintsugi.Ranked P ∧
       (∀ (b:Filter UVIndex) [b.NeBot], b ≤ (order.refine f).fuse→∀ M, Observing C U.room.cutoff b M→ Rail.Assembly U P lit M Q hq b ∧ Kintsugi.Bearing U b) ∧
       (∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→ ∃ q:Filter UVIndex,q.NeBot ∧ q≤b ∧ (Alidade.Flat T U.sector.derivatives q ∧ Kintsugi.Bearing U q)) ∧
       (∀ (i:Fin 3)(ax:Axis),(∀ d,4≤d→Alidade.Proposal U Q hq P i d lit ax)→ (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q)∧∀ ax:Axis, (∀ d:ℕ,4 ≤ d→ Arche.Drives.March U ax Q hq d) → (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q) ∧ ((∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→
          ∀ M, Observing C U.room.cutoff b M → ∀ d, 4 ≤ d→ FramesInput U.sector.derivatives Q hq M d) →
          LogTrace U Q):=by
  obtain ⟨C,hA,hC,hM,hWC,hF,⟨P,_,lit,HP,hK⟩,hG',H,hZ8,hL,h⟩:= PhysicalNext.Repeat.Legato.RG12Joint.ranked_construct hG δ hp
  obtain ⟨f,A,V,R,T,B,hA',s,hN⟩:=h order
  obtain ⟨hs,hGate⟩:= hL (order.refine f) s.copies
  obtain ⟨M,I,hI,p⟩:=Acme.emanate (W:=B) H hG hs hGate s hA'.clean.ready hA'.clean.tilt
  obtain ⟨U⟩:= Acme.glistens hC hA'.clean.ready hA'.clean.tilt p
  obtain ⟨L,hL⟩:= EveryPhase.all_characters U
  obtain ⟨w,z,Z,u⟩:= hG'
  have hH:Facilities C (order.refine f) T:= ⟨⟨hs,hG,⟨w,z,Z,u.toPackage⟩,A,V,R,B,hA'⟩,w,z,Z,u⟩
  obtain ⟨Q,hQ⟩:= Prescription.chosen U.room.kernel.laws.toSymmetric U.phase.transport.injection
  exact ⟨C,f,T,U,L,hM,hC,hA,hF,UVExtension.Reports.useFull hF ⟨U⟩, UVExtension.Poppy.bravo (UVExtension.Oasis.appears hF),hL,hH,hZ8,
    Q,hQ,hH.toServices.everything U Q hQ,⟨P,lit,HP,hK,fun _ _ z M v=>⟨Rail.charter hG U P HP.free hH Q hQ v z,Kintsugi.ships U M P HP hK v z hG hH⟩,
     fun b u hu=>by
       obtain ⟨q,hq,he,M,hM⟩:=observe_all C U.room.cutoff (show Filter.Tendsto Prod.fst b atTop from (Push.RelayDifference.cutoff_grows (order.refine f)).mono_left hu)
       exact ⟨q,hq,he,Alidade.credible_flat U hM (Alidade.weiner U Q hQ P hG hM (he.trans hu) hH HP),Kintsugi.ships U M P HP hK hM (he.trans hu) hG hH⟩,
     fun i ax => Alidade.sharps U Q hQ P hG hH i ax HP,fun a=> Arche.Drives.reading_sharp U a P HP.free.covered hG hH Q hQ⟩,sharp_from_measurements U hG hH Q hQ⟩

theorem rankings (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) (order:Extraction.Order):
    ∃ (C:Family G)(f:Extraction.Order)(T:Table C.book)(U:Spec.Final C (order.refine f) T)
      (L:EveryPhase.Almanac U),
      C.Makes∧ Spec.Calibrated C∧
      C.path.levels.clock.kernel.penalty=penalty∧
      UVExtension.Oasis.Floral (hG:=hG) C∧
      (Extraction.Order.mk Extraction.Sequence.full (order.refine f).per).Ordered C T∧
      (∀ d k:ℕ,∀ᶠ n:ℕ in atTop,
        ∀ (r:ℕ) (v:Fin r→ C.book.Token), (∀ i, (v i).1 ≤ d)→ ∃ g,UVExtension.Poppy.Margins C r n k v g) ∧
      EveryPhase.Completed U L ∧ Facilities C (order.refine f) T ∧ Nonempty (UVExtension.Mast.Stock9 C hG) ∧
      ∃ (Q:Prescription U.sector.derivatives)(hq:Q.Coherent),
        AllShapes U Q ∧ (∃ (P:Commission.Port C)(lit:ℕ→Prop), Alidade.Route P lit U.room.cutoff ∧ Kintsugi.Ranked P ∧
       (∀ (b:Filter UVIndex) [b.NeBot], b ≤ (order.refine f).fuse→∀ M, Observing C U.room.cutoff b M→ Rail.Assembly U P lit M Q hq b ∧ Kintsugi.Bearing U b) ∧
       (∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→ ∃ q:Filter UVIndex,q.NeBot ∧ q≤b ∧ (Alidade.Flat T U.sector.derivatives q ∧ Kintsugi.Bearing U q)) ∧
       (∀ (i:Fin 3)(ax:Axis),(∀ d,4≤d→Alidade.Proposal U Q hq P i d lit ax)→ (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q)∧∀ ax:Axis, (∀ d:ℕ,4 ≤ d→ Arche.Drives.March U ax Q hq d) → (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q) ∧ ((∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→
          ∀ M, Observing C U.room.cutoff b M → ∀ d, 4 ≤ d→ FramesInput U.sector.derivatives Q hq M d) →
          LogTrace U Q):=by

  obtain ⟨C,f,T,U,L,hF,hL,hM,h3,h4,h5,h6,h7,⟨hU⟩,hP⟩:=fashions G (garment10 G) hG penalty hp order
  exact ⟨C,f,T,U,L,hF,hL,hM,h3,h4,h5,h6,h7,⟨hU.toStock9⟩,hP⟩
theorem travelling (hG:G.Simple) (penalty:ℝ) (hp:0<penalty) (order:Extraction.Order):
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
        AllShapes U Q ∧ (∃ (P:Commission.Port C)(lit:ℕ→Prop), Alidade.Route P lit U.room.cutoff ∧
       (∀ (b:Filter UVIndex) [b.NeBot], b ≤ (order.refine f).fuse→∀ M, Observing C U.room.cutoff b M→ Rail.Assembly U P lit M Q hq b) ∧
       (∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→ ∃ q:Filter UVIndex,q.NeBot ∧ q≤b ∧ Alidade.Flat T U.sector.derivatives q) ∧
       (∀ (i:Fin 3)(ax:Axis),(∀ d,4≤d→Alidade.Proposal U Q hq P i d lit ax)→ (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q)∧∀ ax:Axis, (∀ d:ℕ,4 ≤ d→ Arche.Drives.March U ax Q hq d) → (∃ ϕ:Filter UVIndex,ϕ.NeBot∧ϕ≤(order.refine f).fuse∧OPE.Log.MatrixTicket T U.sector.derivatives ϕ)∧ LogTrace U Q) ∧ ((∀ (b:Filter UVIndex) [b.NeBot],b ≤ (order.refine f).fuse→
          ∀ M, Observing C U.room.cutoff b M → ∀ d, 4 ≤ d→ FramesInput U.sector.derivatives Q hq M d) →
          LogTrace U Q):=by
  obtain ⟨C,f,T,U,L,h1,h2,h3,h4,h5,h6,h7,h8,-,Q,hQ,h9,⟨P,J,hA,-,hB,hR,hC,hD⟩,hE⟩:=rankings G hG penalty hp order
  refine ⟨C,f,T,U,L,h1,h2,h3,h4,h5,h6,h7,h8,Q,hQ,h9,⟨P,J,hA,(fun b _v he M H=> (hB b he M H).1),(fun b _v he=> ?_),hC,hD⟩,hE⟩
  obtain ⟨q,hq,hQ,hV,-⟩:=hR b he
  exact ⟨q,hq,hQ,hV⟩
end YM.RG12
