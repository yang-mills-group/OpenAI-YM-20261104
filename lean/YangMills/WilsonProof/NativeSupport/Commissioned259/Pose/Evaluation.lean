import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Slip
import YangMills.WilsonProof.NativeSupport.Commissioned259.Pose.Lip
import YangMills.WilsonProof.NativeSupport.Commissioned259.Ball
import Mathlib.Analysis.Asymptotics.Lemmas
/-! # The prepared solution gives a *price* on frame error; also multilinear change tariff -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Pose
open Function Filter Set PowerSeries Asymptotics MeasureTheory
open Maxwell XSpace XSpace.Normalize XSpace.Structure1 Equiv
open FVA2.Scale Comparing O.Score Dframe
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {d n : ℕ} {I J : Type*} {F : Filter I}
    {V : Normalize.Store G} (z : I→Change G d) (t : I→ℝ)
    {A B : I→Prediction G d} {w:I→ℝ}

-- measured bundle route, derive rate from C.5 on *true* W reports. Also applied when
-- reversing the sides (W vs dilation of W).
lemma screen (hv : (V.survey d).Via A (u:=F))
    (h : Tendsto (fun i=>guide G d (z i)) F (𝓝 0))
    (hA : ∀ᶠ i in F,(V.measure d).D (A i)=(V.measure d).D (reference G d))
    (hB : ∀ᶠ i in F,(V.measure d).D (B i)=(V.measure d).D (reference G d))
    (ha : ∀ j:Fin (V.survey d).n, let a:Normalize.Window G d:= (V.survey d).scope j
      (fun i=> watch a (B i) - watch a (recruit (stand (z i)) (A i)))=O[F] w) :
    (fun i=>guide G d (z i))=O[F] w := by
  let D:= V.survey d; let S':= V.prepared d; let Z:= guide G d; let x:= fun i=> D.purse (A i)
  have H : (fun i=> D.itinerary (x i,Z (z i))-D.itinerary D.opening)=O[F] w := by
    let L i : Fin D.n→ℂ := fun j=> (watch (D.scope j)) (B i)-watch (D.scope j) (recruit (stand (z i)) (A i))
    have ht : L=O[F] w := isBigO_pi.mpr ha
    have hr (P:Prediction G d) : D.stamps (fun i=>watch (D.scope i) P)= guide G d ((V.measure d).D P) := by rw [←D.equal]; rfl
    apply (isBigO_neg_left.mpr ((D.stamps.isBigO_comp ..).trans ht)).congr' ?_ (EventuallyEq.refl ..)
    filter_upwards [hB] with i hB; unfold x L Z; rw [D.way,Fray.opening,D.way, Fray.box, Fray.box,map_zero, stand0,Screen.recruit_one, ← hB,LinearEquiv.symm_apply_apply]
    change -D.stamps ( (fun j=> watch (D.scope j) (B i)) - (fun j=> watch (D.scope j) (recruit _ _)) ) = _
    rw [map_sub, hr,hr,neg_sub]
  obtain ⟨c,hc,C⟩:= Lip.residual D S' hv h
  have hm := D.unmoor S' hv (fun i=>(0:Change G d)) (by simp_rw [map_zero]; exact tendsto_const_nhds)
  refine (IsBigO.of_bound c ?_).trans H; filter_upwards [C,hA,hm] with i hi a b
  apply le_trans (Eq.ge ?_) hi; rw [← D.guid, b.mp ?_, map_zero,zero_sub,norm_neg]; change Fray.SetEq _ _ _; unfold Fray.SetEq; rw [stand0,Screen.recruit_one]; exact a

variable {a b : I→ ℂ} {K:Set I}
lemma cpoint (c : ℂ) : (fun (_:I)=>c)=O[F] home := homebound (Fare.constant c)
lemma insertCoord (hp : (fun i=> guide G d (z i))=O[F] w) (p: Toon G d) (u : Sec G d) :
    (fun i=> coord p (stand (z i) u)-coord p u)=O[F] w := by
  let L : MoveSpace G d →ₗ[ℝ] ℂ := {
    toFun x:= coord p (((guide G d).symm x).val u)
    map_add' := by intro a b; rw [map_add]; exact _root_.map_add (coord p) _ _
    map_smul' := by intro a b; rw [map_smul]; exact _root_.map_smul ((coord p).restrictScalars ℝ) _ _ }
  let M := LinearMap.toContinuousLinearMap L
  apply ((M.isBigO_comp ..).trans hp).congr_left; intro i; change coord p (((guide G d).symm _).val u) = _
  rw [LinearEquiv.symm_apply_apply,stood,map_add,add_sub_cancel_left]

-- insertion family.
variable {a b : I→Tags G d n} {f : I→Structure1.Point G d n}
variable (h : ∀ i j,(fun k=> coord i (a k j)-coord i (b k j))=O[F] w)
  (hw : w=O[F] home) (hb : ∀ i j, (fun k=> coord i (b k j))=O[F] home)
  (hp : ∀ u: BasisSlots G (fun _:Fin n=>d),(fun k=> f k (word u))=O[F] home)
include hb
lemma digit (j : BasisSlots G (fun _:Fin n=>d)) : (fun i=> coordinates j (b i))=O[F] home := by
  unfold coordinates; exact homebound ((Fare.prod (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>Fare.bare (hb (j i) i))).extend (Eventually.of_forall fun i=> Finset.prod_const_one))
include hw h
lemma around (i : Toon G d) (j : Fin n) : (fun k=>coord i (a k j))=O[F] home := (((h i j).trans hw).add (hb i j)).congr_left (fun _=>sub_add_cancel ..)
include hp
lemma insert_tags : (fun i=> f i (a i)-f i (b i))=O[F] w := by
  simp_rw [word_sigma (a _) (f _), word_sigma (b _) (f _), ← Finset.sum_sub_distrib,smul_eq_mul, ← sub_mul]
  apply IsBigO.sum
  intro j _
  refine ((IsBigO.mul ?_ (hp j)).congr_right (fun i=> mul_one _)); unfold coordinates
  exact homebound ((Fare.overall (Eventually.of_forall (fun (_:I)=>le_rfl (a:=(1:ℝ)))) (s:=Finset.univ)
    (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>Fare.bare (around h hw hb (j i) i))
    (fun i (_:i∈(Finset.univ:Finset (Fin n)))=>Fare.bare (hb (j i) i)) (g:=w)
    (fun i _=> (Fare.bare (h (j i) i)).extend (Eventually.of_forall fun _=>(mul_one _).symm) )).extend (Eventually.of_forall fun _=>by unfold home; simp))
omit hw h
include hp
lemma tags_cost : (fun i=> f i (b i))=O[F] home := by
  simp_rw [word_sigma (b _) (f _),smul_eq_mul]; exact IsBigO.sum (fun j _=> mix_home (digit hb j) (hp j))
end YM.FVA2.GradedFar259.Pose
