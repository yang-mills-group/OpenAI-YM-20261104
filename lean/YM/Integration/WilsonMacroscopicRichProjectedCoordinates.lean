import YM.Integration.WilsonMacroscopicRichProjectedFiling
import YM.Integration.WilsonMacroscopicRichWatchCurrency

/-! Both physical coefficient estimates for the same fixed-u filing on its original reporting tuples. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichProjectedCoordinates
open Set Function Filter Spec OPE OPE.Orbits PhysMS Pert.Asymptotics Lattice Cells Wilson
open Trace.Pilot RG16 RG16.Literal RG MergeProof Trace.Physical.GermGraph FilteredWilsonProduct
open FilteredIntrinsicGramReadout WilsonMacroscopicRichMeasuredFiling Next.UVStress
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {I:Type}[Fintype I][Nonempty I]{d:I→ℕ}

theorem original (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(fac:Facilities C f S)
    (pace:∀m,((C.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (h:ℕ)(η M B:ℝ)(hη:0<η)(hM:0<M)(hB:20<B):
    ∃a:ℕ,∃W:Fin a→Watch C,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,∃top u:ℕ,∃T:Stop C h top u,
    (∀z,D (fun i=>(W i).tester S h z)=z) ∧
    ∀(v:(j:I)→(Climb.Bel C.book).Field (d j)),(∀i,‖v i‖≤1)→
    ∀(g:ℝ→ℝ),Coupling G g→G.Simple→∀(q:ℕ)(δ ε:ℝ),0<δ→δ<1/16→0<ε→
    ∀ᶠ m : ℕ in atTop, ∃ (hu : u ≤ m), ∀ (ρ : ℝ) (x : I → Cover),Tuple C M η B m ρ x→
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ (hn : m < w.1),
      let r:=C.S.a m*ρ
      let Y:=field F R J v r m x w
      let z:=label (w:=w) F.room.cutoff (T.doors w.2) (hu.trans hn.le) Y
      let Z:=S.project h z
      let A:=R.packet h (fun i=>C.S.gridPoint m (x i)) (Frame.born J r v) 0
      Booked C w.1 w.2 h Y u (hu.trans hn.le) ∧
        ‖Z-A‖≤ε*g r^q*r^((h:ℝ)+δ) ∧ ‖(J r h).symm Z-(J r h).symm A‖≤ε*g r^q*r^δ:=by
  obtain ⟨a,W,D,top,u,T,L,fits,identified⟩:=WilsonMacroscopicRichProjectedFiling.original
    (d:=d) F R J leading foundation fac pace h η M B hη hM hB
  refine ⟨a,W,D,top,u,T,fits,?_⟩
  intro v cap g running simple q δ ε del room ep
  let s:=(δ+1/16)/2
  have space:δ<s:=by unfold s;linarith
  have reserve:s<1/16:=by unfold s;linarith
  have price:=WilsonMacroscopicRichWatchCurrency.normalized F J leading h space L running simple q ep
  filter_upwards [WilsonMacroscopicRichWatchRooms.placed (I:=I) C B price,
    identified v cap s (del.trans space).le reserve] with m every report
  obtain ⟨hu,cells⟩:=report
  refine ⟨hu,?_⟩
  intro ρ x geometry
  filter_upwards [cells ρ x geometry] with w receipt
  obtain ⟨hn,booked,scalar⟩:=receipt
  exact ⟨hn,booked,(every M η ρ x geometry).1 _ _ scalar⟩

end YM.Integration.WilsonMacroscopicRichProjectedCoordinates
