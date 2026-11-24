import YM.GradedFar.Physical.Away

/-!
# Continue Pose.F3 on a general trajectory of *calibrations*, when installation
index can still depend on T (and r goes to zero). Use later in buying its C-grid
estimate (VALUES).
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t p : ℕ} {I J:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G

variable (T:Filter I) (r:I→ℝ) (hr:Tendsto r T (𝓝[>] (0:ℝ))) {t':I→ℝ}
variable {F:Pose.Plans G h} {Y:ℝ→ Prediction G h}(H' : Held N Y F)
  {D':I→ Normalize.Change G h} (ht:Tendsto (fun i=> t' i/gYM G (r i)) T (𝓝 1)) (hD : Tendsto (fun i=> guide G h (D' i)) T (𝓝 0))
local notation "L"=>gYM G ∘ r
include H hr ht
set_option linter.unusedSectionVars false in
lemma sailed : ∀ᶠ i in T, 0<t' i ∧ |t' i|≤2*g (r i) := by
   filter_upwards [ht.eventually (lt_mem_nhds (by norm_num : (0:ℝ)<1)),ht.eventually (gt_mem_nhds (show (1:ℝ)<2 by norm_num)),hr.eventually (positive_g simple)] with i h1 h2 h
   have hx : 0<t' i:= (div_pos_iff_of_pos_right h).1 h1; exact ⟨hx,by rw [abs_of_pos hx]; exact ((div_lt_iff₀ h).1 h2).le⟩
lemma sailing : Buys T (fun i=>(t' i:ℂ)) L 1 := by
   apply budget_of T (C:=2) _ ((hr.eventually (positive_g simple)).mono fun i h=>h.le); filter_upwards [sailed N M H T r hr ht] with i hi; rw [Complex.norm_real,pow_one,Real.norm_eq_abs]; exact hi.2
set_option linter.unusedSectionVars false in
lemma sailed_to : Tendsto t' T (𝓝 0) := by
   have hh:= ht.mul ((shrink simple).comp hr); rw [mul_zero] at hh; exact hh.congr' ((hr.eventually (positive_g simple)).mono fun i h=> div_mul_cancel₀ _ h.ne')

-- `G^P` w prediction on exact compact; matrix & coupling still need to be paid from whole job book
abbrev Notice (q k:ℕ)(F:Pose.Plans G h)(x:I→ℝ) (Y':I→Normalize.Change G h)
    (K : Set (Points n))(v:Tags G h n) :=
    Terms T (fun i=> L i^k) (fun i (s:↥K)=> F (r i) n s.val v - crop q (x i) (Pose.line N s.val (stand (Y' i)∘v)))
include H'
omit ht in
lemma target_watch (v:Normalize.Window G h)(q k:ℕ)(HE:Notice N T r q k F t' D' (tsupport v.t) v.p) :
    Buys T (fun i=> watch v (Y (r i))-watch v (recruit (stand (D' i)) (foresee N M h q (t' i)))) L k := by
    obtain ⟨C,hC,hr0⟩:= HE.price
    apply IsBigO.of_bound (Read.Value v.t*C)
    filter_upwards [hr0,hr.eventually self_mem_nhdsWithin] with i h' (h0: r i∈Ioi 0)
    unfold watch;
    change ‖Y (r i) v.n v.t v.p - foresee N M h q (t' i) v.n v.t _‖≤ _; rw [H'.full _ h0, weighted N M H]
    let U' := stand (D' i) ∘ v.p
    have hx:= (H'.cont _ h0 v.n v.p).mono v.t.tsupport_subset
    have hy : ContinuousOn (fun x:Points v.n=> crop q (t' i) (Pose.line N x U')) (tsupport v.t) := by
       unfold Pose.line; simp only [crop_eq]; simp_rw [coeff_mk]; refine continuousOn_finsetSum _ (fun j _=> ((Pose.birth N M H h).light _ j _).const_mul _ |>.mono v.t.tsupport_subset)
    change ‖(v.t.applyTo _)-v.t.applyTo (fun x=>crop q (t' i) (Pose.line N x U'))‖≤_
    rw [← Read.smear_sub _ hx hy, mul_assoc]; exact Read.value_le _ (hx.sub hy) (fun i hi=> h' ⟨i,hi⟩)

include hD
lemma targeted (q k:ℕ) (B:Fray (N.store.measure h)) (hq : ∀ i : Fin B.n, let v:= B.scope i; Notice N T r q k F t' D' (tsupport v.t) v.p) :
    Buys T (fun i=> guide G h (D' i)) L k := by
   let R i:= recruit (stand (D' i)) (foresee N M h q (t' i)); let s i j:= watch (B.scope j) (Y (r i)) - watch (B.scope j) (R i)
   obtain ⟨C,hC,hx⟩:= (isBigO_pi.mpr (show ∀ j, Buys T (fun i=> s i j) L k from fun j=> target_watch N M H T r hr H' (B.scope j) q k (hq j))).exists_pos
   apply IsBigO.of_bound (2*(‖B.stamps‖*C))
   filter_upwards [hx.bound,hr.eventually H'.fixed,itinerary_fare N M H B q (sailed_to N M H T r hr ht) D' hD] with i hi hr h
   have he : B.stamps (s i)=guide G _ ((N.store.measure _).D (reference G _) - (N.store.measure _).D (R i)) := by
     rw [← hr]; change guide G _ (B.tally _) = _
     rw [show s i=(fun j=>watch (B.scope j) (Y (r i)-R i)) from funext fun _=> (map_sub ..).symm,B.equal,map_sub]
   have hw := le_trans (ContinuousLinearMap.le_opNorm B.stamps (s i)) (mul_le_mul_of_nonneg_left hi (norm_nonneg B.stamps))
   rw [he,map_sub,norm_sub_rev] at hw; rw [map_sub] at h
   exact h.trans ((mul_le_mul_of_nonneg_left hw (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))
-- pay without matrix change on compact
omit H' hD
lemma notice_lost (q k:ℕ){K:Set (Points n)}(hK:IsCompact K)(hx:K⊆conf n)(x : Tags G h n)(H0 : Buys T (fun i=>guide G h (D' i)) L k)
    (HE:Notice N T r q k F t' D' K x) :
    Terms T (fun i=> L i^k) (fun i (s:↥K)=> F (r i) n s.val x - crop q (t' i) (Pose.line N s.val x)) := by
   let R:= comap (Prod.fst : I × K→I) T
   let u (i:I × K):=t' i.1; let t (i:I × K):ℂ:=u i; let p:= L ∘ (Prod.fst : I × K→I)
   have hz : Buys R t p 1:=(sailing N M H T r hr ht).comp_tendsto tendsto_comap; have hT:Tendsto p R (𝓝 0) := ((shrink simple).comp hr).comp tendsto_comap
   have hf (j: Choices G (fun _:Fin n=>h)): Buys R (fun (i:I × K)=> crop q (u i) (Pose.line N i.2.val (basisInputs j))) p 0:=
      (before (p:=q) R hz hT (beauty R N M (r ∘ Prod.fst) (hr.comp tendsto_comap) H (fun i=> i.2.val) hK hx (Eventually.of_forall (fun i=> i.2.property)) (basisInputs j))).congr_left
        (fun i => (crop_by (Pose.line N i.2.val (basisInputs j)) q (u i)).symm)
   let a (j:Choices G (fun _:Fin n=>h))(i:I):= combo (stand (D' i)∘x) j; let a' (j:Choices G (fun _:Fin n=>h)):= combo x j
   have hh j:Buys T (fun i=> a j i-a' j) L k:=by
      suffices H:∀ s:Finset (Fin n), Buys T (fun i=>(∏ l∈s,coord (j l) (stand (D' i) (x l))) - (∏ l∈s,coord (j l) (x l))) L k from H Finset.univ
      intro s; induction s using Finset.induction_on with
      | empty=> simp_rw [Finset.prod_empty,sub_self]; exact isBigO_zero ..
      | insert i s h ih=>
         let t l:= coord (j i) (stand (D' l) (x i)); let t':= coord (j i) (x i)
         have hx:= coord_change (x i) (j i) H0; have hv: Buys T t L 0:= by simpa only [t,t',sub_add_cancel] using (budget_growth T (p:=k) hx 0 (Nat.zero_le _) (jet_level T ((shrink simple).comp hr))).add (budget T (C:= ‖t'‖) (q:=fun _=>t') («g»:=L) (Eventually.of_forall fun _=> le_rfl))
         have hn:= times_cost T hv ih; let X :=∏ l∈s,coord (j l) (x l); rw [zero_add] at hn
         simp_rw [Finset.prod_insert h]; refine (hn.add (times_cost T hx (budget T (C:= ‖X‖) (q:=fun _=>X) («g»:=L) (Eventually.of_forall fun _=> le_rfl)))).congr_left (fun l=>?_)
         unfold t X; ring
   have he j : Buys R (fun (z:I × K)=> (a j z.1 - a' j)*crop q (u z) (Pose.line N z.2.val (basisInputs j))) p k :=
      times_cost R ((hh j).comp_tendsto tendsto_comap) (hf j)
   have hx' : Buys R (fun (z:I × K)=>F (r z.1) _ z.2.val x-crop q (u z) (Pose.line N z.2.val (stand (D' z.1)∘x))) p k:= HE
   unfold Terms; refine (hx'.add (IsBigO.sum (fun j (_:j∈ Finset.univ)=> he j))).congr_left ?_; intro z
   simp only [Function.uncurry]; rw [Pose.roman N (stand _ ∘ x),Pose.roman N x]; simp_rw [sub_mul, Finset.sum_sub_distrib]; unfold u a a'; abel
end
end YM.FVA2.GradedFar.Physical.Round
