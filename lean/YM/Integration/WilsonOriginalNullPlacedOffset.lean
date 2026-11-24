import YM.Integration.WilsonOriginalNullPlacedLinear
import YM.Integration.WilsonOriginalNullMovedOperator
import YM.Next.RANK.Coordinates

/-! The true one-edge primary depends on the actual fine residue.
A common coarse displacement leaves it unchanged, and the aligned
child returns the identical factory parameter on the original Wilson run. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedOffset
open Function Filter Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open WilsonOriginalNullPlacedLinearPanel WilsonOriginalNullPlacedGermMap WilsonOriginalNullPlacedLinear
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "S₀" => (C₀).localSection d

theorem compose {n:Side} (a b:Site n) (f:Config G n→ℂ) :
    (f ∘ Lattice.translate a) ∘ Lattice.translate b=f ∘ Lattice.translate (a+b) := by
  funext U;apply congrArg f;funext e;rcases e with ⟨x,axis⟩
  change U ((x+a)+b,axis)=U (x+(a+b),axis)
  rw [add_assoc]

theorem motion {N p i:ℕ} (live:i<N) (high:Opened C₀ d (i+1) p)
    (y:Site ((C₀).side (i+1) p)) (k:Site ((C₀).side i p)) (x:(C₀).label d) :
    let ratio:=((C₀).path.levels.clock.op i p).ratio
    held R d N p i (y+ratio.embed k) x=held R d N p i y x ∘ Lattice.translate k := by
  intro ratio
  unfold WilsonOriginalNullPlacedLinearPanel.held
  rw [← compose y (ratio.embed k)]
  exact WilsonOriginalNullMovedOperator.commute C₀ d N p i k _ (tested R d live high y x)

theorem shifted {N p i:ℕ} {live:i<N} {home:Opened C₀ d i p} (high:Opened C₀ d (i+1) p)
    (y:Site ((C₀).side (i+1) p)) (k:Site ((C₀).side i p))
    {A B:(C₀).label d →ₗ[ℂ] (C₀).label d} (first:Landed R d N p i live home y A)
    (other:Landed R d N p i live home (y+((C₀).path.levels.clock.op i p).ratio.embed k) B) : A=B := by
  let ratio:=((C₀).path.levels.clock.op i p).ratio
  let o:=ratio.parent y
  let P:=(C₀).path.rep N p i
  let move:=Tour.placard C₀ R.makes N p live.le k
  have root:ratio.parent (y+ratio.embed k)=o+k:=Next.Rank.Station.parent_offset ratio y k
  apply LinearMap.ext;intro x
  obtain ⟨v,z,zf,zp,_,_,_,_,field,_⟩:=first.deposited x
  let z':=Drift.stamp k move z
  have old:Printed C₀ d N p i o z (held R d N p i y x):=⟨zf,⟨_,zp⟩,field.symm⟩
  have pay:Printed C₀ d N p i (o+k) z' (held R d N p i (y+ratio.embed k) x):=by
    refine ⟨Drift.stamp_format k move z zf,⟨_,Drift.stamp_rem k move z zp⟩,?_⟩
    have back:z'.density (o+k) S₀ P=z.density o S₀ P ∘ Lattice.translate k:=
      WilsonOriginalNullRelocation.registered C₀ R.makes d N p i live.le o k z
    exact back.trans ((congrArg (fun f=>f ∘ Lattice.translate k) field.symm).trans (motion R d live high y k x).symm)
  have found:=other.intrinsic x z' (show Printed C₀ d N p i (ratio.parent (y+ratio.embed k)) z' _ by rw [root];exact pay)
  change projection F₀ (C₀).params P.p.threshold (ratio.parent (y+ratio.embed k)) z'=_ at found
  rw [root] at found
  have same:=WilsonOriginalNullRelocation.page F₀ (C₀).params P.p.threshold o k move z
  exact (fitting d N p i R.makes home live.le).injective ((first.intrinsic x z old).symm.trans (same.symm.trans found))

theorem aligned {N p i:ℕ} {live:i<N} {home:Opened C₀ d i p} (high:Opened C₀ d (i+1) p)
    (k:Site ((C₀).side i p)) {A:(C₀).label d →ₗ[ℂ] (C₀).label d}
    (receipt:Landed R d N p i live home (((C₀).path.levels.clock.op i p).ratio.embed k) A) :
    A=LinearMap.id := by
  let ratio:=((C₀).path.levels.clock.op i p).ratio
  let P:=(C₀).path.rep N p i
  let move:=Tour.placard C₀ R.makes N p live.le k
  let φ:=fitting d N p i R.makes home live.le
  apply LinearMap.ext;intro x
  let original:=((C₀).factory d N p).entries i x
  let z:=Drift.stamp k move original
  obtain ⟨zf,zp,_,fields⟩:=WilsonOriginalNullFactoryRoute.entrance R d live.le home k x
  have full:held R d N p i (ratio.embed k) x=calValues (C:=C₀) d N p i x ∘ Lattice.translate k:=by
    refine (WilsonOriginalNullMovedOperator.commute C₀ d N p i k _ ?_).trans ?_
    · exact message d N p (i+1) R.makes high.post live (entryOk d N p (i+1) R.makes high.post live x)
    · exact congrArg (fun f=>f ∘ Lattice.translate k) (factory_eq (C:=C₀) d N p i R.makes home.post live x).symm
  have root:ratio.parent (ratio.embed k)=k:=ratio.embed_parent k
  have quote:Printed C₀ d N p i k z (held R d N p i (ratio.embed k) x):=⟨zf,⟨_,zp⟩,fields.trans full.symm⟩
  have found:=receipt.intrinsic x z (show Printed C₀ d N p i (ratio.parent (ratio.embed k)) z _ by rw [root];exact quote)
  change projection F₀ (C₀).params P.p.threshold (ratio.parent (ratio.embed k)) z=φ (A x) at found
  rw [root] at found
  have same:=WilsonOriginalNullRelocation.page F₀ (C₀).params P.p.threshold 0 k move original
  rw [zero_add] at same
  have native:P.p=(C₀).path.levels.budget i:=(R.makes.wilson.represents N p i live.le).vac
  have re:projection F₀ (C₀).params P.p.threshold 0 original=φ x:=by
    rw [native]
    exact (fitting_apply (C:=C₀) d N p i R.makes home live.le x).symm
  exact φ.injective (found.symm.trans (same.trans re))

end YM.Integration.WilsonOriginalNullPlacedOffset
