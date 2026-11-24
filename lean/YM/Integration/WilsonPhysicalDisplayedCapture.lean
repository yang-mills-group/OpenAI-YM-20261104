import YM.Integration.WilsonPhysicalDisplayedPrice
import YM.Integration.WilsonMovingForkPaidHousing

/-! At a licensed common capture, hear the actual oriented Wilson cylinders on
their respective pooled or weak sources. All regulator cutoffs follow the ear,
the desired exponent and the physical aperture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalDisplayedCapture
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

include L
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)
    {J u:ℕ}(stop:Stop C 0 J u)(d:I→ℕ)(B q:ℕ):
    ∀ᶠf:ℕ in atTop,∀c:ℕ,u+2≤c → c+2≤f → a c/a f≤(β f)^B →
      ∀N per:ℕ,∀deep:f<N,∀o:I → Cover,(∀i,8*‖(C).S.gridPoint f (o i)‖≤a (c+1)) →
      (Pairwise fun i i'=>2*a f*(((P).budget f).B:ℝ)^2≤
        ‖(C).S.gridPoint f (o i)-(C).S.gridPoint f (o i')‖) →
      ∀{D:ℕ}{k:I→ℕ}{r s b:I→ℝ}{stock:∀i,Bank F l D (s i) (b i)}
        {W:∀i,Vane C (k i)}{fits:∀i,D≤k i}{cap:∀i,d i≤D}{V:∀i,Spin.change S (d i)},
      ∀A:∀i,Pair F (stock i) (cap i) (W i) (fits i) (V i) (r i),
      (∀i,(W i).checked order H (k i)) →∀weak:I→Bool,∀v:∀i,S.Field (d i),
      (∀i,station F (A i) (weak i)≤f) →∀turn:I→Motion,∀uf:u≤f,
        let Y(i:I):=displayed R (d i) (((A i).arm (weak i) (v i)).source (N,per)) (turn i)
        ‖gap R N per u (uf.trans deep.le) (word R d f N per deep.le o Y)‖ ≤
          (∏i,Motion.orbitCost ((C).labels.level (d i)) * charge F (A i) f (weak i) (v i))*((β f)^q)⁻¹:=by
  have refs:∀ᶠf:ℕ in atTop,∀i,(C).ref (d i)≤f:=eventually_all.mpr fun i=>eventually_ge_atTop _
  filter_upwards [WilsonOriginalTwoFlatGridScaling.original R d L simple slow stop B q,refs] with f paid ready
  intro c uc cf ratio N per deep o inside apart D k r s b stock W fits cap V A checked weak v live turn uf
  have sc:(a (c+1))≤a c:=(C).S.strictAnti.antitone (Nat.le_succ _)
  have budget: (a (c+1))≤(β f)^B*a f:=sc.trans ((div_le_iff₀ ((C).S.a_pos f)).mp ratio)
  apply paid ((C).S.a_pos (c+1)) ((C).S.strictAnti.antitone (by omega))
    ((C).S.strictAnti (by omega)) budget N per deep o inside apart _ _ _ _ uf
  · intro i
    exact mul_pos (zero_lt_one.trans_le (Motion.orbitCost_one_le _)) (zero_lt_one.trans_le (le_max_left ..))
  · intro i
    exact (WilsonPhysicalDisplayedPrice.original R L (ready i) deep.le _ _).trans
      (mul_le_mul_of_nonneg_left (WilsonOriginalTwoFlatPublicFare.issued F (A i) (checked i) (weak i) (v i) (live i) deep)
        (zero_le_one.trans (Motion.orbitCost_one_le _)))

end YM.Integration.WilsonPhysicalDisplayedCapture
end
