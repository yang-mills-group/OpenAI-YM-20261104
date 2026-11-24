import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Attempt
/-! # Determining tests through d. Real Lipschitz error, no smooth inverse of W family
 assumption. Use earlier purchases from F4. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d}
    (hJ:Leading U J) (P:Realized J Y N A (Paper.meter U J N.criterion)) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "χ" => invoice J Y N t ν M d
local notation "FW" => Paper.point U J
local notation "ψ" => GroupS.ψ N.criterion M ν
local notation "V" => Scale.Measure.start N.scheme N.criterion
local notation "LD" => Reg.Faith.reports 0 N.criterion M
local notation "φ" => minute U J N ν M

variable (h : Shop U J N) (hp: normal U J N.store) {r T:I→ℝ}(hr:Tendsto r L late)(ht:∀ᶠ i in L,T i∈ Icc 1 2) (hQ:Mixture U J N d)
local notation "η" => Quotes.post T
local notation "RR" => (fun i:I=>r i*T i)
local notation "ρ" => (t∘r)
local notation "measure" => Paper.hierarchy U J d

lemma apply_trial (v:Tags G d n) (i r T:ℝ)(p:Test n) (k:ℕ)(hr:0<r*T) : recruit (stand (χ r T k)) (measure (r*T)) n p v=p.applyTo (fun x=> ordinary U J Y N ν M d k r T x v) := by rw [recruits,Paper.actual U J _ _ _ _ hr]; rfl
lemma ordinary_point (v:Tags G d n) (r T:ℝ) (hr:0<r*T) (p:ℕ) : ContinuousOn (fun x=> ordinary U J Y N ν M d p r T x v) (conf n) := Paper.smooth U J _ hr
lemma array_first {x:Points n} (v:Tags G d n)(i:ℝ) : array (V d) x 0 i v=fxt (V d) x 0 v := by simp_rw [array_eq,crop_apply,Finset.sum_range_succ]; simp
include hJ hp H h hr
lemma investment (v:Tags G d n)(p:Test n) :
    (fun i=> measure (r i) n p v - (LD d 0) n p v)=O[L] (δ∘r) := by
  let S':= Alcove.testing p; have hb: Tendsto Prod.fst (booth S'.K L) L := tendsto_fst
  have h := (F4 U J hJ N hp M H h S' v 0).comp_tendsto
    ( (hr.comp hb).prodMk (tendsto_principal.mpr placed))
  have hh : (fun i:I×Points n=> FW (r i.1) d n i.2 v-fxt (V d) i.2 0 v)=O[booth S'.K L] ((δ ∘ r) ∘ Prod.fst) := by
    apply h.congr; · intro i; exact congr_arg ( _ - · ) (array_first N ..)
    intro i; exact pow_one _
  let X:= opening (K:=tsupport p) ((hr.eventually ( self_mem_nhdsWithin ) ).mono fun i hi=>⟨Paper.smooth U J v hi,(orders N M H).light n 0 v⟩ ) hh (subset_refl (tsupport p))
  refine X.congr' ?_ (EventuallyEq.refl ..); filter_upwards [hr.eventually self_mem_nhdsWithin] with i hi; rw [Paper.actual U J d n p v hi,(orders N M H).exact n 0]; rfl
lemma wide : (N.store.survey d).Via (u:=L) (fun i=>measure (r i)) := by
  let a i:= (N.store.survey d).scope i
  apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro k
  let v (j:Fin (a i).n) := Module.finBasis ℝ (Sec G d) (k j); let p:= (a i).t; have he:= (investment U J N hJ M H h hp hr v p).trans_tendsto ((g0_zero sim).comp hr)
  rw [blanking N M H] at he; let X:= reference G d (a i).n p v
  exact tendsto_sub_nhds_zero_iff.mp he

include ht P
lemma inEntire (v:Tags G d n)(p:Test n)(m:ℕ) :
    let Y i := p.applyTo (fun x=>ordinary U J Y N ν M d m (r i) (T i) x v)
    let X i := p.applyTo (fun x=>array (V d) x m (φ m (r i) (T i)) v)
    (fun i:I=> Y i-X i)=O[L] fun i=> δ (r i)^(m+1) := by
  dsimp only
  let Y':= Alcove.testing p
  have e:Tendsto Prod.fst (booth Y'.K L) L:= tendsto_fst
  have hh := attempt U J Y N hJ P ν M H h hp (hr.comp e) (e.eventually ht) Y' Prod.snd placed m v
  have hT:= (later_G hr ht sim).1.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))
  exact opening (w:=fun i=>δ (r i)^(m+1)) (K:=Y'.K)
    (hT.mono fun i hi=>⟨ordinary_point U J Y N ν M v (r i) (T i) hi m,array_smooth (orders N M H).light v m _⟩) hh (subset_refl (tsupport p))
lemma entire (v:Tags G d n)(p:Test n)(m:ℕ) :
    (fun i=> recruit (stand (χ (r i) (T i) m)) (measure (RR i)) n p v - bundle (LD d) m (φ m (r i) (T i)) n p v)=O[L] fun i=>δ (r i)^(m+1) := by
  refine IsBigO.congr' (inEntire U J Y N hJ P ν M H h hp hr ht v p m) ?_ (EventuallyEq.refl ..)
  filter_upwards [(later_G hr ht sim).1.eventually (self_mem_nhdsWithin (s:=Ioi (0:ℝ)))] with i hi
  exact congr_arg₂ (·-·) (apply_trial U J Y N ν M v 0 (r i) (T i) p m hi).symm (tests_point v _ (orders N M H) _ _ p).symm

include hQ
lemma billed (p:ℕ) : (fun i=> guide G d (χ (r i) (T i) p))=O[L] (fun i=>δ (r i)^(p+1)) := by
  let W i:= measure (RR i); let Z i:= bundle (LD d) p (φ p (r i) (T i))
  refine Pose.screen («V»:= N.store) _ (wide U J N hJ M H h hp (later_G hr ht sim).1)
    (yours U J Y N t hJ P ν M H (Pose.guaranteed U J hJ N hp M H h) hr ht hQ p) (B:=Z) ((later_G hr ht sim).1.eventually (hp d)) (Eventually.of_forall fun i=> Pose.positioned N M H p _ ) ?_
  intro j; let a:=(N.store.survey d).scope j; exact (isBigO_neg_left.mpr (entire U J Y N hJ P ν M H h hp hr ht a.p a.«t» p)).congr_left (fun i=>neg_sub ..)
lemma after (R:Alcove)(x:I→Points R.n)(hx:∀ᶠ i in L,x i∈R.K)(p:ℕ)(u:Tags G d R.n) :
    (fun i=> FW (RR i) d R.n (x i) u - array (V d) (x i) p (φ p (r i) (T i)) u)=O[L] fun i=>δ (r i)^(p+1) := by
  let g i:=δ (RR i); let Y' i:=FW (RR i) d R.n (x i)
  have hr':= (later_G hr ht sim).1; have boundt:= (coupling_payment sim (Pose.guaranteed U J hJ N hp M H h))
  have hh := insert_tags (f:=Y') (fun a b=> insertCoord _ (billed U J Y N hJ P ν M H h hp hr ht hQ p) a (u b) ) (isBigO_const_of_tendsto (((g0_zero sim).pow _).comp hr) one_ne_zero) (fun _ _=> Pose.cpoint _) (fun u=>homebound (Coin.costs (hr'.eventually (boundt.mono fun i hi=>hi.2.1)) (hr'.eventually ((g0_zero sim).abs.eventually (ge_mem_nhds (by simp)))) (one_paid _) (pupil U J N hJ h hp M H hr' R x hx d p u)))
  refine ((attempt U J Y N hJ P ν M H h hp hr ht R x hx p u).sub hh).congr_left fun i=>?_; rw [ordinary,MultilinearMap.compLinearMap_apply]; unfold Λ Y'; abel
end YM.FVA2.GradedFar259.Quotes
