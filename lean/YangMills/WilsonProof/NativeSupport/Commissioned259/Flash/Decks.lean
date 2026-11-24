import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Credit
/-! # (G.9) earned at THE ROUNDED POSES, then extend to true continuum layouts.
    This is conditional on (C5), not asserting the construction of calibrated samples here.
    `Loader` on A0⊆A,E0⊆B. This is the + field precision cost before cropping back to q at t.
-/
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
variable {n m d :ℕ}{I:Type}{F:Filter I}{A:Set (Points n)}{B:Set (Points m)}
variable {W c δ a b:ℝ} {K:Set (Points n)}{E:Set (Points m)}{x x':I→Points n}{y y':I→Points m}{r T:I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J Y:ℝ→tower S)(N:WilsonPrescription G)(Q:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin) (H0:LogTrace U Q.port)
    (hJ : Leading U J) (hp: normal U J N.store) {sim:G.Simple}{dial:Bool}
    (M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))){σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial) {A' :∀ d:ℕ,ℝ→Change G d}
    (P:Realized J Y N A' (Paper.meter U J N.criterion))
    (S0:∀ d:ℕ, Mixture U J N d) (S1: Shop U J N)
variable {w p:ℕ} {X:I→Change G d}{s:I→ℝ} (L:Flash.Mesh U J N F w p r T s X x x' y y')
local notation "V" => Scale.Measure.start N.scheme N.criterion
local notation "g" => (fun i=>g0 G (r i))
local notation "V'" => Scale.Measure.outlook N.scheme N.criterion
local notation "t" => Paper.meter U J N.criterion
local notation "τ" => t ∘ r
local notation "Φ" x:max "," y:max => (fun i=>joins (x i) (y i) (T i))
local notation "hard" => (fun i:I=>g i^(w+1))
local notation "M0" => Paper.point U Y
variable (h : Aim F G W a b r T) (R:Room W c δ A B)(hx:∀ᶠ i in F,x i∈K)(hy:∀ᶠ i in F,y i∈E)(hm:Amplifies K A)(hv: Amplifies E B)
    (hd:6≤d)(v:Tags G d (n+m))
    (o:I→Viewers U) (L0 : Loader G U J N W K E)
    (ha:0<a)(hb:0<b) (ν:ℝ)
lemma currency {a:I→ PowerSeries ℂ}{v:I→ℂ}{t':I→ℝ}{P:I→ℝ} (h': Coin F Pose.home t' P p Pose.home v a) : Coin F T t' P p Pose.home v a := ⟨fun i=> Fare.bare (homebound (h'.prices i)), Fare.bare (homebound h'.expense)⟩
include ν hJ hp H P S1 R h hx hy U J Y
include hm hv L hd
lemma credit (p':ℕ) (hq:p'≤w) : Coin F T τ g p' Pose.home (fun i=> M0 (r i) d (n+m) ((Φ x',y') i) v) (fun i=>storyV N v ((Φ x',y') i)) := by
  let k:=n+m; let φ := Φ x',y'; let Wx (i:I):= Paper.point U J (r i) d k (φ i); let Z' i:= fxt (V d) (φ i); have hz:= Pose.guaranteed U J hJ N hp M H S1
  let hT:= aspirant R h; have hx':∀ᶠ i in F,x' i∈A := ((inside hm hx (closer h.reach L.payA sim)).mono fun i hi=> hi (right_mem_segment ..))
  have hy':∀ᶠ i in F,y' i∈B := ((inside hv hy (closer h.reach (grow hT L.payB) sim)).mono fun i hi=> hi (right_mem_segment ..))
  have pay:= peson _ _ _ _ H P hz h.reach; have ht : ∀ᶠ i in F, |τ i| ≤ 1 := h.reach.eventually ((coupling_payment sim hz).mono fun i hi=>hi.2.1); have he:= h.reach.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp : |(0:ℝ)| < 1)))
  have qr := labels pay ht he hT Wx Z' («t»:=τ) (m:=p') (fun u=> calibrated_grid U J N hJ hp M H L h R hx' hy' (word u) hd S1 ν p' hq )
    (fun a b=> currency (T:=T) (paper J Y t M H P hz h.reach p' a b))
  refine (Eval.fixed pay ht he hT _ _ v qr).congr ?_ ?_ (Eventually.of_forall fun i=>by unfold Pose.home; simp)
  · filter_upwards [h.reach.eventually (P.relates d)] with i hi; unfold Wx; rw [MultilinearMap.compLinearMap_apply,Paper.use,Paper.use]; unfold Original.own; simp_rw [hi]; rfl
  filter_upwards with i; unfold Z' storyV Scale.Measure.outlook; simp [fxt_m,φ]

include hb S0 H0
lemma grid (p':ℕ) (hq:p'≤w) : Fare T F (fun i=>g i^(p'+1)) (fun i=> differ (N:=N) U J Y (r i) p' (o i) v ((Φ x',y') i)) := by
  obtain f:= (credit U J Y N hJ hp M H P S1 L h R hx hy hm hv hd v ν p' hq)
  have hT := aspirant R h
  have hx':∀ᶠ i in F,x' i∈A := ((inside hm hx (closer h.reach L.payA sim)).mono fun i hi=> hi (right_mem_segment ..))
  have hy':∀ᶠ i in F,y' i∈B := ((inside hv hy (closer h.reach (grow hT L.payB) sim)).mono fun i hi=> hi (right_mem_segment ..))
  have e:= decamps R ν U J Y Q H0 H P S0 S1 hJ hp h hb hx' hy' o (fun _=>none) v (p'+1)
  exact (Fare.add hT (Fare.bare e) (f.expense.extend (Eventually.of_forall fun _=>mul_one _))).congr (Eventually.of_forall fun i=> sub_add_sub_cancel ..)
omit L
include ha L0
lemma lands (p':ℕ) : Fare T F (fun i=>g i^(p'+1)) (fun i=> differ (N:=N) U J Y (r i) p' (o i) v ((Φ x,y) i)) := by
  obtain ⟨q,hq,t'⟩:= ( (eventually_ge_atTop p').and (crossing R ν U J Y Q H0 H P S0 S1 hJ hp h hb hx hy v o hm hv p') ).exists
  obtain ⟨k,s0,M',x',y',L'⟩:= L0 d hd I F r T a b ha hb h x y hx hy q
  have z:= grid U J Y N Q H0 hJ hp M H P S0 S1 L' h R hx hy hm hv hd v o hb ν p' hq
  exact (Fare.add (aspirant R h) (Fare.bare ( t' x' y' L'.payA L'.payB )) z).congr (Eventually.of_forall fun _=>sub_add_cancel ..)
end YM.FVA2.GradedFar259.Flash
