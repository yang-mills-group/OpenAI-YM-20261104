import YM.MSbar.CrossH.Mounds
import YM.MSbar.Lis.Aspire
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tramp
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Wave
open AnalyticBridge.VerifiedReset Native.Chart Tensor
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable (G:Gauge)(n: Side)
-- augment chart.B aux gauge insertion.Z.Make local.V
abbrev Block (G:Gauge)(n:Side):= Site n × G.ColorIndex
abbrev Cards(G:Gauge)(n:Side):=Primary n G ⊕ Block G n ⊕ Primary n G
noncomputable def slide(G:Gauge)(n:Side): Cards G n→Site n:= Sum.elim (Measuring.chart n G) (Sum.elim Prod.fst (Measuring.chart n G))
local notation "Π!"=>Positions (Primary n G)
local notation "A"=> Primary n G
local notation "X"=>Positions (Cards G n)
noncomputable def tintCost (G:Gauge) := Fintype.card (Strand G)
noncomputable def summerSize (G:Gauge) := tintCost G+(Fintype.card G.ColorIndex+tintCost G)
lemma tok1 : Multiplicity (slide G n) (summerSize G):= by exact embryo _ _ (starM G n) (embryo _ _ (powerP n G.ColorIndex) (starM G n))
-- orientation tilt. JSON navigation.Luminosity
noncomputable def cards0 : Positions (Cards G n) →L[ℝ]Positions (Primary n G):= (ContinuousLinearMap.fst ℝ _ _).comp (partSpace _ _).toContinuousLinearMap
noncomputable def cardsL : Positions (Cards G n)→L[ℝ] Positions (Block G n) := (ContinuousLinearMap.fst ℝ _ _).comp <| (partSpace _ _).toContinuousLinearMap.comp ((ContinuousLinearMap.snd ℝ _ _).comp (partSpace _ _).toContinuousLinearMap)
noncomputable def cardsH : Positions (Cards G n) →L[ℝ] (Site n→ G.Color):= (tint G _).toContinuousLinearMap.comp (cardsL ..)
local notation "T"=> cards0 G n
local notation "H"=>cardsH G n
open MvPolynomial -- alpha
variable (p:ℕ)(x: Positions (Cards G n)) (i:Primary n G) (j:Site n)
local notation "U"=> slide G n
local notation "L"=> Measuring.chart n G
local notation "E"=>Native.Chart.Rail G
noncomputable def chair (z:G.Color)(c:G.ColorIndex):ℝ:=z c
-- vent cost linear Map, multilinear.S.Coord.Pivot
noncomputable def pend(i:Primary n G) : Positions (Cards G n)→L[ℝ]Native.Chart.Rail G:=
    ((ContinuousLinearMap.proj i.1.1).comp (cardsH G n)).prod ((ContinuousLinearMap.proj (i.1.1+step (rope i).2)).comp (cardsH G n))
lemma present : pend _ _ i x=ran (cardsH _ _ x) i.1:=rfl -- binder order n G arg inclusion? redundant
-- animated amplitude. global polynomial. S.Yield entropy.
noncomputable def ventral (p:ℕ)(c:G.ColorIndex)(x:ℝ × G.Color × Native.Chart.Rail G):ℝ:= x.1*(ventG p x.2.2 x.2.1) c
noncomputable def launch (i:Primary n G): Positions (Cards G n) →L[ℝ] ℝ × G.Color × Native.Chart.Rail G := (ContinuousLinearMap.proj (Sum.inr (Sum.inr i))).prod <| ((tune i).comp (cards0 G n)).prod (pend _ _ i)
noncomputable def iridesce (G:Gauge)(n:Side)(p:ℕ)(i:Primary n G)(v:Positions (Cards G n)):= v (.inr (.inr i)) * choir p (cardsH G n v) (cards0 G n v) i
lemma flutter : iridesce G n p i x= ventral G p i.2 (launch G n i x):=by unfold iridesce; rw [compass];rfl
lemma lot (t:ℝ) (p:ℕ)(c:G.ColorIndex)(x:ℝ × G.Color × Native.Chart.Rail G) : ventral G p c (t •x)=t^(p+2)*ventral G p c x:=by
    unfold ventral; change t*x.1 * (ventG p (t •_) (t • _)) c=t^(p+2)*_
    rw [steeper]; unfold ventG; rw [Tensor.homogeneous,PiLp.smul_apply,PiLp.smul_apply]; simp only [smul_eq_mul]; ring -- implicit argument
-- linear family smooth.S
lemma tints (p:ℕ)(c:G.ColorIndex): ContDiff ℝ ω (ventral G p c):=by
    let B:= Module.Free.chooseBasis ℝ E; let I:=Module.Free.ChooseBasisIndex ℝ E; haveI:Finite I := Module.Finite.finite_basis B; letI:= Fintype.ofFinite I
    let u(x:E)(y:G.Color):ℝ:=ventG p x y c; have hE(x:E)(y:G.Color): u x y=∑ i:I,B.repr x i*u (B i) y:= by
       let Q:E→ₗ[ℝ]ℝ:={
           toFun:=fun x=>u x y
           map_add':=fun x z=> congr_arg (fun v:G.Color=> v c) (grok p y x z)
           map_smul':=fun t x=> congr_arg (fun v:G.Color=>v c) (steeper p y x t) }
       change Q x = _; nth_rw 1 [← B.sum_repr x]; rw [_root_.map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [_root_.map_smul];rfl
    let f(x:ℝ × G.Color × E):=u x.2.2 x.2.1; apply ContDiff.mul (f:=Prod.fst) contDiff_fst (show ContDiff ℝ ω f from ?_); rw [show f=(fun x=>∑ i:I,B.repr x.2.2 i*u (B i) x.2.1) from funext fun x=> hE _ _]; refine ContDiff.sum fun i hi => ?_
    let Z(e:E):=B.repr e i; have hv : ContDiff ℝ ω Z := (B.coord i).toContinuousLinearMap.contDiff; exact (hv.comp (contDiff_snd.comp contDiff_snd)).mul ((compass_sm (B i) c p).comp (contDiff_fst.comp contDiff_snd))
lemma spell : ContDiff ℝ ω (iridesce G n p i):=by rw [show iridesce _ _ _ _= ventral G p i.2 ∘ launch _ _ i from funext fun x=>flutter ..]; exact (tints ..).comp (launch G n i).contDiff
noncomputable def auroraS (G:Gauge)(n:Side)(p:ℕ)(i:Primary n G): Pot (Cards G n):= potter (iridesce G n p i) (p+2)
lemma sprite (p:ℕ)(i:Primary n G)(x:Positions (Cards G n)) : clue (auroraS G n p i) x= iridesce G n p i x:=by
    unfold clue auroraS; rw [pots]; unfold diagonal Tensor.coeff; rw [_root_.smul_apply]; let C:= iridesce G n p i; let t:= launch G n i
    have he: diagonal (iteratedFDeriv ℝ (p+2) C 0) x= (p+2).factorial * C x :=by
        rw [← Next.Foundations.iteratedDeriv_on_line ((spell ..).contDiffAt.of_le (m:=↑(p+2:ℕ)) le_top)]; rw [show (fun y:ℝ=> C (y • x))= (fun y:ℝ=> y^(p+2)*C x) from funext (fun y=>by unfold C; rw [flutter,flutter,map_smul,lot])] -- inspect e.C.unfold
        rw [iteratedDeriv_mul_const_field, iteratedDeriv_fun_pow_zero]; simp -- inspect
    change ((p+2).factorial:ℝ)⁻¹*Tensor.diagonal (iteratedFDeriv ℝ _ C 0) x=_; rw [he]; field_simp; rfl
end YM.MSbar.Tramp
