import YangMills.WilsonProof.NativeSupport.Commissioned259.Flash.Path
/-! # On each FAMILY of growing-grid installations financed in the hypothesis.
 This is the BB `gathered from (C5)` purchase; state explicitly and condition on it.
 Points themselves can vary with r, data and T; so t'ℓ projections can depend on the
 layout, but are still in the advertised tolerance and normalization back to W. They are
 NOT using t(r) calibration as a hypothesis.

 Use only actual **continuum** portion of this price (one consequence of having it on the
 real f-grids), NOT comparing measurements on true cutoffs in this theorem. I can be the
 set of all configurations & T & windows with filter of their costs. Thus these hypotheses
 are never used without simultaneous uniformity asserted. To compare regulators themselves
 need stronger hypotheses than those necessary here.
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
variable {K:Set (Points n)}{E:Set (Points m)}
    {W c δ a b:ℝ} {x x':I→Points n}{y y':I→Points m}{r T:I→ℝ}
local notation "late" => 𝓝[>] (0:ℝ)
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (U:Final C f S)(J:ℝ→tower S)(N:WilsonPrescription G)

-- on W actual unselected; hypothesis generator cost on AGAIN compact tasks with same s t'
def unpack (A:I→Change G d) (R:Alcove) (s t:I→ℝ) (p w:ℕ) (i:I) (x:Points R.n) (v:Tags G d R.n) :=
    Paper.point U J (s i) d _ x v - array (Scale.Measure.start N.scheme N.criterion d) x p (t i) (stand (A i) ∘ v)

structure Cash (F:Filter I) (w p:ℕ) (r t:I→ℝ) (A:I→Change G d) : Prop where
    stamps : Tendsto t F late
    budget : t=O[F] (g0 G ∘ r)
    chart : Tendsto (fun i=>guide G d (A i)) F (𝓝 0)
    repays : w+1 ≤ p
    compact (R:Alcove) : R∈ requests N d → ∀ v:Tags G d R.n,
      (fun i:I×Points R.n=> unpack U J N A R r t p w i.1 i.2 v)=O[booth R.K F] fun i=> g0 G (r i.1)^(w+1)
structure Mesh (F:Filter I)(w p:ℕ)(r T t:I→ℝ)(A:I→Change G d)(x x':I→Points n)(y y':I→Points m)
    : Prop extends Cash U J N F w p r t A where
    payA : (fun i=>x' i-x i)=O[F] (fun i=>g0 G (r i)^(w+1))
    payB : (fun i=>T i • (y' i-y i))=O[F] (fun i=>g0 G (r i)^(w+1))
    charges : ∀ v:Tags G d (n+m), (fun i=>
      Paper.point U J (r i) d (n+m) (joins (x' i) (y' i) (T i)) v -
        array (Scale.Measure.start N.scheme N.criterion d) (joins (x' i) (y' i) (T i)) p (t i) (stand (A i) ∘ v))=O[F] fun i=>g0 G (r i)^(w+1)
/-- Only point/net portion of (C5) on those varying families at the f-grid.
    Need cash stamps also for Store & Rose for the SAME installation's projection.
    `t` below is t'ℓ ; not the test t extrapolated in (M.1).
    Standard assumption in taking this part of proof; not meaning of estimator on UV cutoffs.
    Includes scores in f units (r shape). No estimate between vertices assumed away
    from those sampled points, except for the already advertised independent C5 compacta.
    Use with any compact K,E to be rounded. Need aperture W eventually large; the
    hypothesis written here for one of the admissible simultaneous compact geometries.
-/
def Loader (G:Gauge) {C:Family G}{f:Extraction.Order}{S:Table C.book}(U:Final C f S) (J:ℝ→tower S)(N:WilsonPrescription G)
    (W:ℝ) (K:Set (Points n))(E:Set (Points m)) : Prop :=
    ∀ (d:ℕ), 6≤d →∀ (I:Type) (F:Filter I)(r T:I→ℝ) (a b:ℝ), 0<a → 0<b →
      Aim F G W a b r T →∀ (x:I→Points n)(y:I→Points m), (∀ᶠ i in F,x i∈K) → (∀ᶠ i in F,y i∈E) →
        ∀ w:ℕ, ∃ (p:ℕ) (t:I→ℝ) (A:I→Change G d)(x':I→Points n)(y':I→Points m), Mesh U J N F w p r T t A x x' y y'

-- Generalize Pose rates for these moving installations/families. Needn't agree across families.
local notation "V" => Scale.Measure.start N.scheme N.criterion
local notation "g" => (fun i=>g0 G (r i))
variable {w p:ℕ} {X:I→Change G d}{t:I→ℝ} (P:Cash U J N F w p r t X) (hr:Tendsto r F late) (hJ : Leading U J) (hp: normal U J N.store)
    {sim:G.Simple}{dial:Bool}{M: MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{σ : MS.Land.Prescription (Press.portDeck G)} (H: Main.Match N sim M σ dial)
local notation "Q" => N.store.survey d
local notation "D" => Paper.hierarchy U J d
include hp P H hr
lemma amount : (fun i=> guide G d (X i))=O[F] (fun i=>g i^(w+1)) := by
  let L:= Reg.Faith.reports 0 N.criterion M d
  refine Pose.screen («V»:=N.store) _ (A:=fun i=>bundle L p (t i)) ( (Filter.Tendsto.comp (Pose.watching N M H id d p nhdsWithin_le_nhds) (P.stamps) ) ) P.chart
    (Eventually.of_forall (fun i=> Pose.positioned N M H p (t i))) (hr.eventually (hp d)) (fun j=>?_)
  let v:=(Q).scope j; let a:=v.t; have u:= opening (E':=fun i x=>array (V d) x p (t i) (stand (X i) ∘ v.p))
    (w:=fun i=>g i^(w+1)) ((hr.eventually self_mem_nhdsWithin).mono fun i hi=>⟨Paper.smooth U J v.p hi,array_smooth (orders N M H).light _ p (t i)⟩ )
    ( P.compact (Alcove.testing v.t) (brace N j) v.p ) (subset_refl (tsupport a))
  apply u.congr' ?_ (EventuallyEq.refl ..); filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi
  exact congr_arg₂ (·-·) ( Paper.actual U J d v.n a v.p hi).symm ( tests_point (stand (X i) ∘ v.p) _ (orders N M H) _ _ a ).symm

lemma fees (R:Alcove) (hR:R∈ requests N d) (v:Tags G d R.n) :
    (fun i:I×Points R.n=> Paper.point U J (r i.1) d R.n i.2 v - array (V d) i.2 p (t i.1) v)=O[booth R.K F] fun i=>g i.1^(w+1) := by
  have y:Tendsto Prod.fst (booth R.K F) F:=tendsto_fst
  have X' := P.compact R hR v
  have ht := y.eventually (( P.stamps.mono_right nhdsWithin_le_nhds ).abs.eventually (ge_mem_nhds (by simp : |(0:ℝ)| < 1)))
  have V' := insert_tags (fun i j=> IsBigO.comp_tendsto (insertCoord _ (amount U J N P hr hp H) i (v j)) y)
    (isBigO_const_of_tendsto ((((g0_zero sim).pow (w+1)).comp hr).comp y) one_ne_zero) (fun i j=> Pose.cpoint _) (fun u=>bounded_array _ (orders N M H).light R.cost R.space placed (word u) p ht)
  exact (X'.add V').congr_left (fun i=>sub_add_sub_cancel ..)
include hJ in
lemma shoots (hv:6≤d) : (fun i=> Paper.meter U J N.criterion (r i)-t i)=O[F] fun i=>g i^(w+1) := by
  let L:= Pose.ground N; let B:=booth L.K F; have ep : Tendsto Prod.fst B F:=tendsto_fst
  have ht:= Fare.over_pow (w+1) (p+1) (P.repays.trans (Nat.le_succ _)) F (fun i=>g i) (((g0_zero sim).comp hr).abs.eventually (ge_mem_nhds (by simp : |(0:ℝ)| < 1)))
  let dB i (x:Points 3) b:= Paper.point U J (r i) 6 3 x (ret G b)
  refine Pose.reread N M H t dB ?_ (isBigO_const_of_tendsto (((g0_zero sim).pow (w+1)).comp hr) one_ne_zero) ht P.budget (( P.stamps.mono_right nhdsWithin_le_nhds ).abs.eventually (ge_mem_nhds (by simp : |(0:ℝ)| < 1))) ((hr.eventually self_mem_nhdsWithin).mono fun i hi=> continuous_log3 (fun b => Paper.smooth U J (ret G b) hi)) ((show 1≤w+1 by omega).trans P.repays)
  intro b; refine (fees U J N P hr hp H L (pod N) (fun i=>up hv (ret G b i))).congr' ?_ (EventuallyEq.refl ..)
  filter_upwards [(hr.comp ep).eventually (Paper.pointing U J hJ (n:=3) hv), Pose.placed] with i hi v
  let x (i:I×Points 3):Points 3:= i.2; let a:=ret G b; have h0 : x i ∈ conf 3 := (Rose.test N.criterion).tsupport_subset v
  have eq0:= hi a _ h0; have eq:= array_rises N M H hv h0 a p (t i.1); exact congr_arg₂ (·-·) eq0.symm eq.symm

end YM.FVA2.GradedFar259.Flash

