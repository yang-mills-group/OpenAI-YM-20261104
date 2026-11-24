import YM.Integration.WilsonMacroscopicRichWatchFieldLimit
import YM.Integration.WilsonMacroscopicRichWatchLaw
import YM.Integration.WilsonMacroscopicRichWatchRooms

/-! A single fixed macroscopic hearing measures the genuine earlier finite counterterm and the continuum Reader. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichMeasuredFiling
open Set Function Filter MeasureTheory NormedSpace Spec OPE OPE.Orbits PhysMS Lattice Cells Wilson
open Next.UVStress RG16 RG16.Literal RG MergeProof Trace.Physical.GermGraph
open FilteredWilsonProduct FilteredIntrinsicGramReadout WilsonMacroscopicRichWatchReader
open WilsonMacroscopicRichWatchPlot WilsonMacroscopicRichFixedWatchSale
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {I:Type}[Fintype I]{d:I→ℕ}

def counterterm {a h:ℕ}(W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ] S.Field h)
    (H:C.Makes)(w:ℕ×ℕ){u:ℕ}(door:Opened C h u w.2)(live:u≤w.1)
    (Y:Config G (C.side w.1 w.2)→ℂ):S.Field h:=
  D (heard (calibrated S ∘ W) w (C.O w.1 w.2 (label H door live Y) 0))

theorem continuous_field (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(v:(j:I)→(Climb.Bel C.book).Field (d j))(r:ℝ)(m:ℕ)(x:I → Cover)(w:ℕ×ℕ):
    Continuous (field F R J v r m x w):=by
  unfold field
  convert continuous_finsetProd Finset.univ (fun (i:I) _=>continuous_finsetSum Finset.univ
    (fun (j:Fin (d i+1)) _=>C.continuousO w.1 w.2 j.val
      (S.representative _ (R.cutTest j.val (d i) (J r (d i) (v i)))) (location C.S m w.1 w.2 (x i)))) using 1
  funext U
  simp only [Finset.prod_apply,Finset.sum_apply]

theorem original [Nonempty I](F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(fac:Facilities C f S)
    (pace:∀m,((C.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (h:ℕ)(η M B:ℝ)(hη:0<η)(hM:0<M)(hB:20<B):
    ∃a:ℕ,∃W:Fin a→Watch C,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,∃top u:ℕ,∃T:Stop C h top u,∃L:ℝ,
    (∀z,D (fun i=>(W i).tester S h z)=z) ∧ 0≤L ∧
    ∀(v:(j:I)→(Climb.Bel C.book).Field (d j)),(∀i,‖v i‖≤1)→
    ∀(σ ε:ℝ),0≤σ→σ<1/16→0<ε→
    ∀ᶠ m : ℕ in atTop, ∃ (hu : u ≤ m), ∀ (ρ : ℝ) (x : I → Cover), Tuple C M η B m ρ x→
    ∀ κ : ℝ, 0 < κ → ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ (hn : m < w.1),
      let r:=C.S.a m*ρ
      let Y:=field F R J v r m x w
      let z:=counterterm W D F.room.cutoff w (T.doors w.2) (hu.trans hn.le) Y
      Booked C w.1 w.2 h Y u (hu.trans hn.le) ∧
      ‖z-R.packet h (fun i=>C.S.gridPoint m (x i)) (Frame.born J r v) 0‖ ≤
        ‖D‖*(κ+r^((h:ℝ)+1-ε)+L*(Fintype.card (Grades d):ℝ)*((C.S.a m)^h*Real.exp (-σ*C.S.scale m))):=by
  classical
  obtain ⟨a,W,D,fits,reader⟩:=WilsonMacroscopicRichWatchReader.original (d:=d) F R J leading foundation h
  let watches:=calibrated S ∘ W
  obtain ⟨top,u,T,K,positive,test⟩:=WilsonMacroscopicRichFixedDecoder.original (d:=d)
    F R J leading fac pace h η M B hη hM hB watches
  let L:=∑i,K i
  refine ⟨a,W,D,top,u,T,L,fits,Finset.sum_nonneg (fun i _=>positive i),?_⟩
  intro v cap σ ε nn small ep
  let E:=detector W D fits
  have window:=(reader v M η ε hM.le hη ep).and (WilsonWholeLimit.detector_separated_in_room (I:=I) E M η hη)
  filter_upwards [WilsonMacroscopicRichWatchRooms.placed (I:=I) C B window,test σ nn small] with m inroom paid
  obtain ⟨hu,physical⟩:=paid
  refine ⟨hu,?_⟩
  intro ρ x cells κ kp
  let r:=C.S.a m*ρ
  let pts:=fun i=>C.S.gridPoint m (x i)
  let cur:=current W pts (Frame.born J r v)
  let pkt:=R.packet h pts (Frame.born J r v) 0
  obtain ⟨⟨forecast,sites⟩,geometry⟩:=inroom M η ρ x cells
  have hh:‖D cur-pkt‖≤‖D‖*r^((h:ℝ)+1-ε):=forecast pts geometry
  have limit:=WilsonMacroscopicRichWatchFieldLimit.full F fac.toServices R J W D fits v r m x (sites pts geometry)
  filter_upwards [physical,limit.eventually (Metric.ball_mem_nhds cur kp)] with w budget close
  obtain ⟨hn,report⟩:=budget
  obtain ⟨book,_,sums⟩:=report ρ x v cells cap
  refine ⟨hn,book,?_⟩
  let Y:C(Config G (C.side w.1 w.2),ℂ):=⟨field F R J v r m x w,continuous_field F R J v r m x w⟩
  let z:=label F.room.cutoff (T.doors w.2) (hu.trans hn.le) (Y:Config G _→ℂ)
  let Δ:Config G (C.side w.1 w.2)→ℂ:=(Y:Config G _→ℂ)-C.O w.1 w.2 z 0
  let cash:=(Fintype.card (Grades d):ℝ)*((C.S.a m)^h*Real.exp (-σ*C.S.scale m))
  have cp:0≤cash:=mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (C.S.a_pos m).le _) (Real.exp_pos _).le)
  have residual:‖heard watches w Δ‖≤cash*L:=WilsonMacroscopicRichWatchRooms.estimate K positive cp _ sums
  have comparison:‖heard watches w (Y:Config G _→ℂ)-cur‖≤κ:=by
    change ‖heard (calibrated S ∘ W) w (field F R J v r m x w)-cur‖≤κ
    rw [←dist_eq_norm]
    exact le_of_lt close
  have decode:=WilsonMacroscopicRichWatchLaw.decoded C watches D Y z
  change ‖D (heard watches w (C.O w.1 w.2 z 0))-pkt‖≤_
  rw [decode]
  let y:=heard watches w (Y:Config G _→ℂ)
  change ‖D y-D (heard watches w Δ)-pkt‖≤_
  have split:D y-D (heard watches w Δ)-pkt=D (y-cur)+(D cur-pkt)-D (heard watches w Δ):=by rw [map_sub];abel
  rw [split]
  calc
    _ ≤ ‖D (y-cur)+(D cur-pkt)‖+‖D (heard watches w Δ)‖:=norm_sub_le _ _
    _ ≤ (‖D (y-cur)‖+‖D cur-pkt‖)+‖D (heard watches w Δ)‖:=by gcongr;exact norm_add_le _ _
    _ ≤ (‖D‖*κ+‖D‖*r^((h:ℝ)+1-ε))+‖D‖*(cash*L):=
      add_le_add (add_le_add ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_left comparison (norm_nonneg _))) hh)
        ((D.le_opNorm _).trans (mul_le_mul_of_nonneg_left residual (norm_nonneg _)))
    _ = _:=by dsimp only [cash,r];ring

end YM.Integration.WilsonMacroscopicRichMeasuredFiling
