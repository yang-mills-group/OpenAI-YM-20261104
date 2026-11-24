import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Hier
import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Evaluation
/-! # BB PoseFit step 4 from its actual (C5) estimates as hypotheses -- **conditional**
pricing lemma. These are MUCH stronger physical inputs than election hypotheses. Expose them
at the application. Give compact-(C5) tasks literally: NOT requiring all-orders at t on these
Moments. NOT defining a t using a witness at each increased OPE horizon. `PoseFit` may use
*another* t'/cash for every fixed finite analysis task, as in BB.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Pose
open Function Filter Set Asymptotics MeasureTheory Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale O.Score Comparing
open scoped Topology ContDiff Classical BigOperators

-- §C5(F4) unselected W, horizon through d. Pay this STRONG at true positions rx in continuum family.
variable {G : Gauge} {d n q m p : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J : ℝ→PhysMS.tower S)
    (N : WilsonPrescription G) (A : ℝ→Change G d) (t : ℝ→ℝ)
-- fixed uses only
structure Alcove where
  n : ℕ
  K : Set (Points n)
  cost : IsCompact K
  space : K ⊆ conf n
local notation "late" => 𝓝[>] (0:ℝ)
local notation "P" => Paper.point U J
local notation "W" => Scale.Measure.start N.scheme N.criterion
local notation "δ" => g0 G
local notation "FF" => N.store.survey d
/-- C5 purchases ONLY. Actual W tests and bare formal prediction. Use at horizon d;
`start` agrees with the higher presentation horizon on C5 by exact inheritance. Unit ball C5
is stronger; needs here only each fixed label (equiv multilinear basis purchases).
`p` exponent/read error, q is Q* (fixed by that setting, witness, LOGICALLY bigger). -/
def summary (R : Alcove) (m q : ℕ) : Prop :=
    ∀ v: Fin R.n → Sec G d,
    (fun i:ℝ×Points R.n=> P i.1 d R.n i.2 v - array (W d) i.2 q (t i.1) (stand (A i.1) ∘ v))=O[booth R.K late]
      fun i=>δ i.1^m
/-- Ready on these compacts, measured input predictions exact. -/
structure C5 (S0 : Finset Alcove) (m q : ℕ) : Prop where
    compared : ∀ R∈S0, summary U J N A t R m q
    coupon : Tendsto (fun r=>guide G d (A r)) late (𝓝 0)
    enough : m ≤ q
    calibrated : Calibrated G t

-- explicit premises StrongBook ⇒ (Leading W) plus equality of position screen
-- on W (`WilsonPositionPrescribedFrame.original` on Leading J).
def normal (U : Final C f S) (J : ℝ→tower S) (V : Normalize.Store G) : Prop :=
    ∀ d:ℕ, ∀ᶠ r in late,(V.measure d).D (Paper.hierarchy U J d r)=(V.measure d).D (reference G d)

-- required supports. Request all these from PoseFit strong upstream.
def Alcove.testing {n} (p : Test n) : Alcove := ⟨n, tsupport p, p.hasCompactSupport, p.tsupport_subset⟩
def braces (N : WilsonPrescription G) (d : ℕ) : Finset Alcove :=
    Finset.univ.image (fun i : Fin (N.store.survey d).n => Alcove.testing (((N.store.survey d).scope i).t))
def ground (N : WilsonPrescription G) : Alcove := Alcove.testing (Rose.test N.criterion)
def requests (N : WilsonPrescription G) (d : ℕ) := Insert.insert (ground N) (braces N d)
lemma brace (j : Fin (N.store.survey d).n) : Alcove.testing (((N.store.survey d).scope j).t) ∈ requests N d :=
  Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
lemma pod : ground N∈requests N d:= Finset.mem_insert_self ..

variable {S0 : Finset Alcove} (V : C5 U J N A t S0 m q)
    (hz : requests N d ⊆ S0) (hp : normal U J N.store)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "L" => Reg.Faith.reports 0 N.criterion M
include H
lemma watching (v : ℝ→ℝ) (e m : ℕ) (hc : Tendsto v late (𝓝 0)) : (N.store.survey e).Via (u:=late) (fun i=>bundle (L e) m (v i)) := by
  refine tendsto_pi_nhds.mpr fun j=>tendsto_pi_nhds.mpr fun k=>?_
  let u:= (N.store.survey e).scope j; let T (j : Fin u.n):= Module.finBasis ℝ (Sec G e) (k j)
  let F (t:ℝ):= bundle (L e) m t u.n u.t T
  have H' : Continuous F := by
    unfold F; simp_rw [bundle_val]; exact continuous_finsetSum _ fun i _=>by fun_prop
  suffices h : F 0=reference G e u.n u.t T by
    change Tendsto (F ∘ v) _ (𝓝 (reference G e u.n u.t T)); rw [← h]; exact H'.continuousAt.tendsto.comp hc
  unfold F; rw [bundle_val, Finset.sum_eq_single 0]
  · rw [pow_zero,one_mul,blanking N M H]
  · intro i _ hi; rw [Complex.ofReal_zero,zero_pow hi,zero_mul]
  simp

lemma candidate_fee (paid : Calibrated G t) : t=O[late] g0 G := IsBigO.of_bound 2 ((coupling_payment sim paid).mono fun i hi=> hi.2.2.trans (by gcongr; exact le_abs_self _))
include V hz hp
lemma cash_price : (fun i=> guide G d (A i))=O[late] (fun i =>δ i^m) := by
  refine Pose.screen (V:=N.store) _ (watching _ M H t d q ((candidate_fee N t M H V.calibrated).trans_tendsto (g0_zero sim))) V.coupon
    (Eventually.of_forall (fun i=> positioned N M H q (t i))) (hp d) (fun j=>?_)
  let R := (FF).scope j; let a:= R.t; let u:= R.p
  have hc : Tendsto Prod.fst (booth (tsupport a) late) late:= tendsto_fst
  have hn : ∀ᶠ i in late, 0 < i := self_mem_nhdsWithin
  let X:= opening (w:=fun i=>δ i^m) (E':=fun i x=> array (W d) x q (t i) (stand (A i) ∘ u)) (Eventually.mono hn
    (fun i hi=>⟨Paper.smooth U J u hi, array_smooth (orders N M H).light _ q (t i)⟩)) (V.compared _ (hz (brace N j)) u) (subset_refl (tsupport a))
  refine IsBigO.congr' X ?_ (EventuallyEq.refl ..)
  filter_upwards [self_mem_nhdsWithin (s:=Ioi (0:ℝ))] with i hi
  rw [show a.applyTo (fun x=> P i d R.n x u)= _ from (Paper.actual U J d R.n a u hi).symm]
  congr 1; exact Eq.symm (tests_point _ _ (orders N M H) q (t i) a)

lemma bare_price {R:Alcove} (hR:R ∈ S0) (u: Fin R.n→ Sec G d) :
    (fun i:ℝ×Points R.n=> P i.1 d R.n i.2 u - array (W d) i.2 q (t i.1) u)=O[booth R.K late]
      fun i=>δ i.1^m := by
  let B:= booth R.K late
  have hf : Tendsto Prod.fst B late:= tendsto_fst
  have H': ∀ᶠ (i:ℝ×Points R.n) in B, |t i.1| ≤ 1 := hf.eventually ((coupling_payment sim V.calibrated).mono fun i hi=>hi.2.1)
  refine ((V.compared _ hR u).add ?_).congr_left (fun i=> sub_add_sub_cancel _ (array (W d) i.2 q (t i.1) (stand (A i.1) ∘ u)) _)
  exact insert_tags
    (fun j k=>IsBigO.comp_tendsto (insertCoord A (cash_price U J N A t V hz hp M H) j (u k)) hf)
    (by
      have z:= (g0_zero sim).pow m; exact isBigO_const_of_tendsto (z.comp hf) one_ne_zero)
    (fun j k=>cpoint _) (fun v=>bounded_array (W d) (orders N M H).light R.cost R.space placed (word v) q H')

end YM.FVA2.GradedFar259.Pose
