import YM.Integration.WilsonMacroscopicRichWatchBounded
import YM.Integration.WilsonMacroscopicRichBookedLabels
import YM.Integration.WilsonMacroscopicRichWatchCurrency
import YM.Integration.WilsonMacroscopicRichMeasuredFiling

/-! The continuum class of the actual issued raw cutoff label is identified by the same physical detector. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichProjectedFiling
open Filter Function Set Spec OPE OPE.Orbits PhysMS Lattice Cells Wilson Next.UVStress
open RG16 RG16.Literal FilteredWilsonProduct FilteredIntrinsicGramReadout
open WilsonMacroscopicRichMeasuredFiling
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}
variable {I:Type}[Fintype I][Nonempty I]{d:I→ℕ}

theorem original (F:Final C f S)(R:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F R)(fac:Facilities C f S)
    (pace:∀m,((C.S.block m).val:ℝ)≤Real.log (Lambda C.path.levels m))
    (h:ℕ)(η M B:ℝ)(hη:0<η)(hM:0<M)(hB:20<B):
    ∃a:ℕ,∃W:Fin a→Watch C,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,∃top u:ℕ,∃T:Stop C h top u,∃L:ℝ,
    (∀z,D (fun i=>(W i).tester S h z)=z) ∧
    ∀(v:(j:I)→(Climb.Bel C.book).Field (d j)),(∀i,‖v i‖≤1)→
    ∀ s : ℝ, 0 ≤ s → s < 1/16 →
    ∀ᶠ m : ℕ in atTop, ∃ (hu : u ≤ m), ∀ (ρ : ℝ) (x : I → Cover), Tuple C M η B m ρ x→
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ (hn : m < w.1),
      let r:=C.S.a m*ρ
      let Y:=field F R J v r m x w
      let z:=label (w:=w) F.room.cutoff (T.doors w.2) (hu.trans hn.le) Y
      let V:=R.packet h (fun i=>C.S.gridPoint m (x i)) (Frame.born J r v) 0
      Booked C w.1 w.2 h Y u (hu.trans hn.le) ∧
      ‖S.project h z-V‖≤L*r^((h:ℝ)+s):=by
  obtain ⟨a,W,D,top,u,T,L,fits,lp,raw⟩:=WilsonMacroscopicRichMeasuredFiling.original
    (d:=d) F R J leading foundation fac pace h η M B hη hM hB
  let n:ℝ:=Fintype.card (Grades d)
  refine ⟨a,W,D,top,u,T,1+‖D‖*(2+L*n),fits,?_⟩
  intro v cap s sp sf
  filter_upwards [WilsonMacroscopicRichBookedLabels.purchased (d:=d) F R J leading fac pace
    h top u T η M B hη hM hB,raw v cap s (1-s) sp sf (by linarith)] with m stocks heard
  obtain ⟨_,K,stock⟩:=stocks
  obtain ⟨hu,sale⟩:=heard
  refine ⟨hu,?_⟩
  intro ρ x cells
  let r:=C.S.a m*ρ
  obtain ⟨pos,mesh⟩:=WilsonMacroscopicRichWatchCurrency.mesh h (by linarith : 0≤B) sp m x cells
  let t:=r^((h:ℝ)+s)
  have tp:0<t:=Real.rpow_pos_of_pos pos _
  filter_upwards [sale ρ x cells t tp,WilsonMacroscopicRichWatchBounded.measured F W D fits K t tp]
    with w sold all
  obtain ⟨hn,book,reading⟩:=sold
  refine ⟨hn,book,?_⟩
  let Y:=field F R J v r m x w
  let z:=label (w:=w) F.room.cutoff (T.doors w.2) (hu.trans hn.le) Y
  let A:=R.packet h (fun i=>C.S.gridPoint m (x i)) (Frame.born J r v) 0
  let H:=counterterm W D F.room.cutoff w (T.doors w.2) (hu.trans hn.le) Y
  have warm:‖S.project h z-H‖≤t:=all z (stock w.1 w.2 hn ρ x v cells cap)
  have response:‖H-A‖≤‖D‖*(t+t+L*n*t):=by
    change ‖H-A‖≤‖D‖*(t+r^((h:ℝ)+1-(1-s))+L*n*((C.S.a m)^h*Real.exp (-s*C.S.scale m))) at reading
    rw [show (h:ℝ)+1-(1-s)=h+s by ring] at reading
    exact reading.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left mesh (mul_nonneg lp (Nat.cast_nonneg _)))) (ContinuousLinearMap.opNorm_nonneg D))
  calc
    ‖S.project h z-A‖≤‖S.project h z-H‖+‖H-A‖:=norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ t+‖D‖*(t+t+L*n*t):=add_le_add warm response
    _ = (1+‖D‖*(2+L*n))*t:=by ring

end YM.Integration.WilsonMacroscopicRichProjectedFiling
