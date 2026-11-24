import YM.FVA2.Hearth.Carrier
/-!
 # Rail from included `Silk.price`, including remunerating its negative power

 Keep I=L.Warm and use true height. `Rail` may not itself be gauge invariant; holding
 T fixed here (gauge theorem use `rad T O` for physical area). It's just a translation
 to price notation at that order. The pronouncement does not compare to unrestricted
 periodic thermal outing.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.Hearth
open FormalOPE.RG10 FormalOPE.RG10.OpenSlots
open Function Filter Set MeasureTheory Metric PertExtension Precision Lattice GaussianScore Chart RG
open BlockGauge StationaryMarks MultiGauge MultiGauge.Stack MultiGauge.Splice MultiGauge.Blocking Fabric Papers MarkovChain Warp Line Roof Router OpenSlots.Quadratic
open PertExtension.Orb PertExtension.Series Tested Radial Facade RGComparison.Core16 PowerSeries
open RGComparison.Core16.Lumen RGComparison.Core16.Forge
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{n:Side}{L:Fabric G n}(T:Cloth L) (y:Flats G (Bottom L))
variable (w:Rail G (Warm T))

 def fabricWire (i: Wire G (Warm T))(u:Facade.Entry T):= Lumen.turn (u.1 i.1) i.2
 def fabricBook (u:Facade.Entry T) := (w.map (fun i=> fabricWire T i u)).prod
lemma book_nil : fabricBook T []=1:= funext fun _=>rfl
lemma book_cons (i) : fabricBook T (i::w)= fabricWire T i*fabricBook T w:= by ext1 x; unfold fabricBook; simp
lemma hotterWire (i:Wire G (Warm T)): ContDiff ℝ ω (fabricWire T i):= (EuclideanSpace.proj i.2:G.Color→L[ℝ] ℝ).contDiff.comp (Lumen.turn_hot.comp ((contDiff_apply ℝ _ _).comp (f:=Prod.fst) contDiff_fst))
lemma hot_fabric : ContDiff ℝ ω (fabricBook T w):= by induction w with | nil=> exact contDiff_const| cons i w ih=> rw [book_cons]; exact (hotterWire T i).mul ih
lemma atBook (u): Silk.weft w (Fk.scene (Silk.swatch w) u)= fabricBook T w (flank y u) := by
 unfold Silk.weft; change (∏ j:Fin w.length, fabricWire T (w[j]) (flank y u))= _
 induction w with
 | nil=> simp [book_nil]
 | cons i w ih=> rw [book_cons]; dsimp only [List.length_cons]; rw [Fin.prod_univ_succ]; change fabricWire T i (flank y u) * _= _*_; rw [←ih]; rfl
lemma body : Contains T y (Silk.swatch w) (Silk.weft w) (fabricBook T w):= by filter_upwards with i using atBook T y w i
lemma worthRail : ∃ A:Ticket (Facade.Entry T),Stack.rise (fabricBook T w) = X^w.length * A := by
 induction w with
 | nil=> refine ⟨1,?_⟩; simp [book_nil,rise_one]
 | cons i w ih=>
    let B:=Stack.drop 1 (Stack.rise (fabricWire T i)); have he:X^1*B=Stack.rise (fabricWire T i):= by
        refine Stack.recover _ _ ?_; intro j hj; obtain rfl:j=0:= (by omega); unfold Stack.rise; rw [coeff_mk]; apply Subtype.ext; funext x; change jet (fabricWire T i) 0 x=0; rw [jet_zero]; unfold fabricWire; rw [show (0:Entry T).1 _=(0:G.Color) from rfl,Lumen.turn_zero]; rfl
    obtain ⟨A,ha⟩:= ih; refine ⟨B*A,?_⟩; rw [book_cons, rise_mul ((hotterWire ..).contDiffAt.of_le le_top) ((hot_fabric ..).contDiffAt.of_le le_top),ha,←he,pow_one]; change _= X^(w.length + 1)* _; rw [pow_succ']; ring

section norm
variable {S R:Type} [CommRing S] [CommRing R]
lemma holdingTake (f:S→+R)(p:PowerSeries S)(n:ℕ): throughPrice f (X^n*p)=X^n*throughPrice f p:= by
 apply PowerSeries.ext; intro i; rw [tagThrough, coeff_X_pow_mul', coeff_X_pow_mul']; split
 · rw [tagThrough]
 rw [map_zero]
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] [NormedAddCommGroup F][NormedSpace ℝ F]
lemma fitTake (q:Quadratic (E × F))(μ:Measure E)[μ.IsAddHaarMeasure] (hq:(core q).RespectsPrice)(W A:Ticket (E×F))(n:ℕ): fit q μ hq (X^n * A) W= X^n * fit q μ hq A W:= by
 unfold fit; rw [mul_left_comm W (X^n) A]; unfold uptake; rw [holdingTake,mul_assoc]
end norm

variable {J:ChartRatio G}
variable (x:G.ColorIndex)(v:L.Accounts→ℝ→ℝ)
local notation "P"=> localClimate T y x v
variable (z:L.Accounts→PowerSeries ℝ)(hz:∀ i,0<term (z i) 0)(N:ℕ) (hw:∀ i,ContDiffAt ℝ ω (v i) 0)(h:∀ i,Through N (amount (v i)) (z i))
local notation "U"=> (sticker T z hz (J:=J) (Stack.rise (fabricBook T w)))
lemma chargeRail : U=X^w.length * Stack.drop w.length U := by
 obtain ⟨A,H⟩:=worthRail T w; rw [H]; unfold sticker; rw [fitTake, Stack.drop_mul]
-- Silk.published at exactly `chart G`, not guessing J.
local notation "D"=> RGComparison.Core16.Silk.chart G
local notation "Ξ"=> Stack.drop (List.length w) (sticker T z hz (J:=D) (Stack.rise (fabricBook T w)))
local notation "Y"=> Stack.read y Ξ
include hw h
lemma price_field (u:ℕ)(H:w.length+u ≤ N) : coeff u (Silk.price P w)= coeff u Y:=by
 unfold Silk.price; rw [coeff_mk, posts T y x v (Next.Foundations.chart_ok G) z hz N hw h (body T y w) ((hot_fabric T w).contDiffAt.of_le le_top) w.length u H];
 nth_rw 1 [chargeRail T w]; rw [Stack.read,map_mul,map_pow,map_X,coeff_X_pow_mul', if_pos (by omega),Nat.add_sub_cancel_left]
-- shift only. With explicit `Through` schedules.
end YM.FVA2.Hearth
