import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Owners
import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.AtEnd
/-! # Export original-continuum (G.9) purchase on explicit hypotheses.
    Use budgets for BB's proof, not merging Inversion contexts. No mesh-estimator (ii) attached.
    H_r at every slot; cost for unit balls through ANY field/argument caps (here through d,
    covers mixed caps as well by up-lifts). For M.2 buy the first-line's two `Round`
    with this. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open FVA2.Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d e :ℕ} {I : Type} {F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {K:Set (Points n)}{E:Set (Points m)} {r T:I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S)(N:WilsonPrescription G)(Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(H0:LogTrace U Q.port)
    (hJ : Leading U J)(hp: normal U J N.store) {sim:G.Simple}{dial:Bool}
    (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial){A' :∀ d:ℕ,ℝ→Change G d}
    (P:Realized J Y N A' (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)
local notation "g" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "Y₀" => physicalY U Y
variable (R:Room W c δ A B)(hm:Amplifies K A)(hv:Amplifies E B)(L:Loader G U J N W K E)
    (ha:0<a)(hb:0<b) (ν:ℝ) (l : List (Fin (n+m)×Axis)) {b' :ℝ} (hz:0≤b')

structure Passage (W a b b':ℝ)(K:Set (Points n))(E:Set (Points m))(d:ℕ) extends Flash.Register U W a b K E where
   u : Balls b' G (fun (_:Fin (n+m))=>d)
include hz H P hm hv L ha hb H0 S0 S1 hJ hp ν R
lemma operator_price (p j:ℕ) : ∃ c₀:ℝ,0<c₀ ∧ ∃ k k':ℕ,
    ∀ᶠ r in late, ∀ T≥W, T≤ a*g r^(-b) → ∀ x∈K,∀ y∈E,∀ v:Viewers U,∀ u∈ Balls b' G (fun (_:Fin (n+m))=>d),
      let z:=joins x y T; let q i:=coeff i ∘ storyV N u; let r0:= dots l (Y₀ v u r) z
      let τ0:= dots l (reply U J (N:=N) u r p) z
      ‖r0-τ0‖ ≤ c₀ * g r ^ (p+1)*(1+Real.log T)^k ∧ ‖dots l (fun x=>q j x) z‖ ≤ c₀*(1+Real.log T)^k' ∧
        ‖r0‖≤ c₀ * (g r)⁻¹ := by
  let I:= Passage U W a b b' K E d; let r (i:I):=i.r; let T (i:I):= i.T; let F:= comap r late; let x(i:I):=i.x.val; let y(i:I):= i.y.val; let u(i:I):=i.u.val
  have h:Aim F G W a b r T:= ⟨tendsto_comap,Eventually.of_forall fun i=> i.inside,Eventually.of_forall fun i=> i.second ⟩
  let z i:= joins (x i) (y i) (T i); let v (i:I):=i.v; let q(i:I) :ℂ:=dots l (Y₀ (v i) (u i) (r i)) (z i)
  have he := enlarging U J Y N Q H0 hJ hp M H P S0 S1 h R (x:=x) (y:=y) (Eventually.of_forall fun i:I=> i.x.property) (Eventually.of_forall fun i:I=> i.y.property) hm hv v L ha hb ν l u b' hz ( Eventually.of_forall fun i:I=>i.u.property) p
  have hi:= aspirant R h; have hp0 := h.reach.eventually (g0_pos sim)
  obtain ⟨C,hC,y₀,D⟩:= Fare.pays hi (hp0.mono (fun i hi=> show 0 ≤ g (r i)^(p+1)*1 from by positivity)) he.expense
  obtain ⟨B₀,hB₀,k,K'⟩:= Fare.pays hi ( Eventually.of_forall (fun i:I=> show 0 ≤ Pose.home i from zero_le_one)) (he.prices j)
  have hy:= cents R h (sim:=sim) hb (Coin.costs (tendsto_comap (f:=r) |>.eventually ( (coupling_payment sim (Pose.guaranteed U J hJ N hp M H S1)).mono fun i hi=>hi.2.1 )) ( h.reach.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp))) ) hi he)
  obtain ⟨M₀,hM₀,H'⟩:= (hy.congr_right fun i => one_mul (g (r i))⁻¹).exists_pos
  refine ⟨C+B₀+M₀,by positivity,y₀,k,?_⟩
  filter_upwards [eventually_comap.mp (D.and (K'.and H'.bound)), g0_pos sim] with r H' h T hr hs x hx y hy v u hv' z q r0 τ0
  obtain ⟨d,D,Y⟩:=H' ( { r:=r,T:=T,x:=⟨x,hx⟩,y:=⟨y,hy⟩,inside := hr, second := hs,v:=v,u:=⟨u,hv'⟩ } : I ) rfl
  have he : z∈ conf (n+m):= R.event _ hr _ (includes hm hx) _ (includes hv hy)
  change ‖r0-crop p (t r) (indexed N l u z)‖ ≤ C*((g0 G r)^(p+1)*1)*(1+Real.log T)^_ at d
  rw [← paid_top N M H u he l, mul_one] at d; change ‖coeff j (indexed N l u z)‖ ≤ B₀*1*(1+Real.log T)^_ at D
  rw [indexed,coeff_mk,mul_one] at D; change ‖r0‖ ≤ M₀* ‖(g0 G r)⁻¹‖ at Y
  rw [Real.norm_of_nonneg (inv_nonneg.mpr h.le)] at Y; have ht := Real.log_nonneg ((height R).trans hr )
  exact ⟨d.trans (by gcongr; linarith), D.trans (by gcongr; linarith), Y.trans (by gcongr; linarith)⟩

end YM.FVA2.GradedFar259.Flash

namespace YM.FVA2.GradedFar259.Flash
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open FVA2.Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score O.Enh Comparing Pose Original Matrix Quotes Sparks
open Flash259HorizonFork Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {n m d :ℕ}{A:Set (Points n)}{B:Set (Points m)}{W c δ a b:ℝ} {K:Set (Points n)}{E:Set (Points m)}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S)(N:WilsonPrescription G)(Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(H0:LogTrace U Q.port)
    (hJ : Leading U J)(hp: normal U J N.store) {sim:G.Simple}{dial:Bool}
    (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial){A' :∀ d:ℕ,ℝ→Change G d}
    (P:Realized J Y N A' (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)
local notation "g" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "YY" => Scale.Measure.outlook N.scheme N.criterion
variable (R:Room W c δ A B)(hm:Amplifies K A)(hv:Amplifies E B)(L:Loader G U J N W K E)
    (ha:0<a)(hb:0<b) (ν:ℝ) {D: Fin n→ℕ} {e:Fin m→ℕ}
include H P hm hv L ha hb H0 S0 S1 hJ hp ν R
lemma purchases (hd:∀ i,D i≤d) (he:∀ i,e i≤d)(p:ℕ) : Round YY t (measures U Y D e) hd he p a b W K E := by
  intro u v; let Z:= Fin.append (liftSlots hd (word u)) (liftSlots he (word v))
  obtain ⟨B,hB,Y₀⟩ : ∃ C:ℝ, 0≤ C ∧ Z∈Balls C G (fun _=>d) := by
    let C:= ∑ i:Fin (n+m), ∑ b:Toon G d, ‖coord b (Z i)‖; exact ⟨C, Finset.sum_nonneg (fun i _=> Finset.sum_nonneg (fun b _=>norm_nonneg _)), fun i b=> le_trans ( (Finset.single_le_sum (fun x (_:x∈(Finset.univ:Finset (Toon G d)))=> norm_nonneg (coord x (Z i))) (Finset.mem_univ b))) ( Finset.single_le_sum (fun (i:Fin (n+m)) _=>Finset.sum_nonneg (fun b (_:b∈(Finset.univ:Finset (Toon G d)))=>norm_nonneg (coord b (Z i)))) (Finset.mem_univ i) )⟩
  obtain ⟨C,hC,k,b,Q⟩:= operator_price U J Y N Q H0 hJ hp M H P S0 S1 R hm hv L ha hb ν [] hB (d:=d) p 0
  refine ⟨C,hC.le,k,?_⟩; filter_upwards [Q, (Original.height (taking U J Y N hJ P M H S1 hp) d), self_mem_nhdsWithin] with r h ho hr T hr' ht x hx y hy o
  have hz:= R.event T hr' x (includes hm hx) y (includes hv hy)
  rw [ Flash.promote U Y o hz hr ho _ _ hd he,readyPT hz hr ]
  exact (h T hr' ht x hx y hy o.1 Z Y₀).1
omit ha hb L hm hv R
/-- Standing purchase from (C5) on those moving parameters. We have not proven this
 hypothesis (it requires the continuum portion of real meshed estimates); note no
 need for uniformity of mesh winners across irrelevant calls made at different installations. -/
def Pays (U:Final C f S) (J:ℝ→tower S)(N:WilsonPrescription G) :=
    ∀ n m:ℕ,∀ A:Set (Points n),∀ B:Set (Points m),IsCompact A→A⊆conf n→IsCompact B→B⊆Outside m→∀ᶠ W:ℝ in atTop, Loader G U J N W A B
include H
lemma provider (P': Pays U J N) : supplies_round U Y YY t := by
  intro n m d z e A B hd he hA hx hB hy; obtain ⟨C,D,hC,hD,Q'⟩ := afford hA hx hB hy
  filter_upwards [P' n m A B hA hx hB hy, Q'] with r hr ⟨c,δ,h⟩; exact fun b hb p=> purchases U J Y N Q H0 hJ hp M H P S0 S1 h hC hD hr zero_lt_one hb ν hd he p
end YM.FVA2.GradedFar259.Flash
