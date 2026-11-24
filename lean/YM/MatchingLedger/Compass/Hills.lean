import YM.Extension.UV.Station.Delta
import YM.MatchingLedger.Compass.Fix

/-!
# Wilson kinetic convention *through order 2* characterized by germs, part 1

Comparison by critical jets of the local branch determinant & phase.
Convention here uses the tilted tree chart `lifting` of the calculus: exp'd free links
MULTIPLY a replica of the background links, so logJ refers to that density. `Thermal`
uses the full log of this stationary-phase Jacobian term with the critical followed as
function of external. Independent of masks, beta trajectory, internals; any Critical
branch gives the value.

Adapted jet comparison ideas from `Extra.WILSON_STARTUP.TopStep`, `Delta`. Here the
fine path loops carried IN (not top) through degree two and exact (`Matches 2` lemma).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger.Compass
open Function Filter Set Precision RG Tree Wilson Lattice Work Exterior
open WilsonStartup.Change Extension.UV.LoopRate Extension.UV.StationaryData Bid
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f : Side}
variable {S:StepData c f} (F : Forest S.ratio) (t:S.Choices)
local notation "R"=> fieldDir G c 1
variable {p q: Clip} {W U W' U': PathData G} {H A:ChartRatio G}
 (h:LocalRatio H)

/-- Uniform in torus, terms of stationary model. These are Taylor jets along log coordinates,
 no requirement of equality of the extension to arbitrary group charts. -/
structure Stunning (p: Clip) (n:Side) (W U:PathData G) : Prop where
     classicalEq : Matches 4 (AT n p W) (AT n p U) 0
     loop : Matches 2 (L n W) (L n U) 0

variable {x x':fieldDir G c 1→AxisChart G F} (hW:Critical F p W x) (hU:Critical F p U x')
variable {α : ℝ}
include hW h in
lemma change_price (ht : LocalRatio A):
    thermal F t p W x H=ᶠ[𝓝 0] thermal F t p W x A:= by
    have he (i:F.Free) : ∀ᶠ u:R in 𝓝 0,H.J (x u i)= A.J (x u i):=((show Tendsto (fun u:R=> x u i) (𝓝 0) (𝓝 0) by
       convert! (((continuous_apply i).continuousAt.comp hW.2.1.continuousAt).tendsto) using 1; simp [hW.1]).eventually (Interiors.charge h ht))
    filter_upwards [eventually_all.mpr he] with u hu
    unfold thermal; rw [Finset.prod_congr rfl (fun i _=>hu i)]
include h hW hU in
lemma equation (Y: Stunning p f W U) (hd : Definite (onSlice F t p W))
    (h₁ : 0 < (hessian F t p W 0 (x 0)).det):
   Matches 2 (thermal F t p W x H) (thermal F t p U x' H) 0 := by
   let g:=WilsonStartup.Change.graph x; let y:= WilsonStartup.Change.graph x'
   have Hs := tested_match Y.classicalEq hW t
   have he : Matches 2 g y 0 := ((compare Hs (station_of hW t) (station_of hU t) hd).1.lower (by decide))
   have hx:= (station_of hW t).at0
   let f'(P:PathData G) := fun z:VChart G F=> (hessian F t p P z.1 z.2).det
   have hm: Matches 2 (f' W) (f' U) (g 0) := Eq.mpr (congr_arg (Matches 2 (f' W) (f' U)) hx) (compare_det Hs)
   have hd : Matches 2 (f' W ∘ g) (f' U ∘ y) 0:= hm.comp he
   let j (w : R → AxisChart G F) (v:R) := ∏ i,H.J (w v i)
   have hj : Matches 2 (j x) (j x') 0:= by
     have hi:Matches 2 x x' 0:= he.refl_comp contDiffAt_snd
     convert! matches_prod (k:=2) (x:=(0:R)) Finset.univ (f:=fun i v=> H.J (x v i)) (g:=fun i v=> H.J (x' v i)) (fun i _=> (hi.apply_pi i).refl_comp (h.germ (x 0 i) (by rw [hW.1]; simpa using h.patch))) using 1 <;> ext v <;> simp only [j,Finset.prod_apply]
   have hdet:= hd.together hj (H:=fun a b=> (1/2)*Real.log a-Real.log b) (((contDiffAt_fst.log h₁.ne').const_smul (1/2:ℝ)).sub (contDiffAt_snd.log (by simp only [j,hW.1,Pi.zero_apply,h.anchored,Finset.prod_const_one]; exact one_ne_zero)))
   let I := Work.F03.axisLog (G:=G) F; have hI : Matches 2 (L f W ∘ I) (L f U ∘ I) 0 := by
     apply Matches.comp_refl (f:=I) _ (log_smooth F)
     exact (show I 0=0 from log_zero F).symm ▸ Y.loop
   have hh := log_works (G:=G) F
   have hz: Matches 2 (loop W ∘ readFine F) (loop U ∘ readFine F) 0 := hI.unchanged (hh.fun_comp (loop W)) (hh.fun_comp (loop U))
   have ht' : Matches 2 (loop W ∘ readFine F) (loop U ∘ readFine F) (g 0):= (show g 0=0 from hx).symm ▸ hz
   have hr := (ht'.comp he).add hdet
   unfold thermal; simp_rw [add_sub_assoc]; exact hr
include hW hU t in
lemma drops {α : ℝ} (hA : Matches 4 (AT f p W) (AT f p U) 0) (hc : 0<α) (hG : PriceGap F p W α)
    (hd : ClassicalMatch F p q W W' x) (hd' : ClassicalMatch F p q U U' x') : Matches 4 (AT c q W') (AT c q U') 0 := by
   have ht:= tested_match hA hW t
   have he:= compare ht (station_of hW t) (station_of hU t) (definite_of hG hc t ht.left)
   have h1:=hd 4 le_rfl t
   have h2:=hd' 4 le_rfl t
   exact ⟨h1.2.1,h2.2.1,fun i hi=> ((hd i hi t).2.2.symm.trans (he.2.jets i hi)).trans (hd' i hi t).2.2⟩
include h hW in
lemma promos (ht:LocalRatio A){B γ Λ:ℝ}(hg:FiniteBound F W W' p q α H x B γ Λ) :
   FiniteBound F W W' p q α A x B γ Λ :=
     ⟨hg.branch,fun t=>(hg.born t).congr_of_eventuallyEq (change_price _ _ h hW ht).symm,hg.classicalResult,fun s i j v z hi hv=> by
       dsimp only; rw [← ((change_price F s h hW ht).iteratedFDeriv ℝ 2).self_of_nhds]; exact hg.wave_price s i j v z hi hv⟩
end YM.MatchingLedger.Compass
