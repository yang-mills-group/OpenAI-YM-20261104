import YM.GradedFar.Moving.Yard

/-!
# Apply same screen and job estimates on the trial and actual alignments
-/
namespace YM.FVA2.GradedFar.Moving
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh O.Canon Scale Dframe Jury Facets Growth
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n d e : ℕ} {I J : Type} {p : ℕ} (T : Filter I) (N : WilsonPrescription G)
  (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable (r z : I→ℝ) (hr : Tendsto r T τ) (hz : ∀ i,z i∈Growth.Small) {simple : G.Simple}
  {A : Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
  {Z : Rolled G d} (hZ : Righted Z) {F : Pose.Plans G d}
variable (θ : ℝ→ℝ) (ht : Tendsto (fun r=> θ r/gYM G r) τ (𝓝 1)) (h : Beginning N θ d F)
local notation "W"=> compareZ N M θ Z p
local notation "x'"=> fun i=> resize (r i) (z i)
structure Held (Y : ℝ→ Prediction G d) (F : Pose.Plans G d) : Prop where
    cont (r : ℝ) : 0< r → ∀ n x, ContinuousOn (fun p=>F r n p x) (conf n)
    full (r : ℝ) (hr : 0<r) (n : ℕ) (x : Tags G d n) (y : Test n) : Y r n y x=y.applyTo (fun p=> F r n p x)
    fixed : ∀ᶠ r in τ,(N.store.measure d).D (Y r)=(N.store.measure d).D (reference G d)
variable (Y : ℝ → Prediction G d) (hy : Held N Y F) (he : refit Z F)
include hy h H hr
omit hr in
lemma warmth (D : Fray (N.store.measure d)) : Tendsto (fun i=> D.purse (Y i)) τ (𝓝 D.opening.1) := by
    apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro k
    let w:=D.scope i
    let u (j : Fin w.n) := Module.finBasis ℝ (Sec G d) (k j)
    obtain ⟨C,hC,h⟩:= (h w.n 0 _ (w.t.hasCompactSupport) w.t.tsupport_subset u).price
    apply tendsto_iff_norm_sub_tendsto_zero.mpr; let Fm i:=F i w.n; let L x:=fxt (Pose.Bbook N d) x 0 u
    have hp : ∀ᶠ (i : ℝ) in τ, ‖Y i w.n w.t u - reference G d w.n w.t u‖ ≤ Read.Value w.t*(C*g i) := by
      filter_upwards [h, positive_g simple,self_mem_nhdsWithin] with i h hu (hx : i∈Ioi 0)
      have hc:= (hy.cont _ hx _ u).mono w.t.tsupport_subset
      have hb:= ((Pose.birth N M H d).light _ 0 u).mono w.t.tsupport_subset
      rw [hy.full _ hx _,←Pose.ground N M H d,(Pose.birth N M H d).exact,← Read.smear_sub _ hc hb]
      refine Read.value_le _ (hc.sub hb) fun j hj=> ?_
      have hv:=h (⟨j,hj⟩: ↥(tsupport w.t)); rw [Real.norm_of_nonneg (by positivity)] at hv; simpa [crop,Pose.line] using hv
    refine squeeze_zero' (Eventually.of_forall fun i=> norm_nonneg _) hp ?_
    simpa only [mul_zero] using ((shrink simple).const_mul C).const_mul (Read.Value w.t)

include hz ht he
lemma nephew (u : Tags G d n) (t : Test n) :
    Buys T (fun i=> recruit (compareZ N M θ Z p (r i) (z i)) (Y (x' i)) n t u-
      Pose.foresee N M d p (new_clock N M θ (z i) (r i) p) n t u) (g∘r) (p+1) := by
    let q := tsupport t; let P i:= ray N M θ (z i) (r i) p d; let b i:=W (r i) (z i); let t' i:=new_clock N M θ (z i) (r i) p
    let V i x := F (resize (r i) (z i)) n x (b i∘u)
    have owner (i : I) (r0: 0 < r i) (x : Points n) (hx:x∈ q): V i x= F (r i) n (exp (z i) • x) (P i∘u) := by
      unfold V; rw [he _ _ r0 (hz i) n _ x (t.tsupport_subset hx)]; apply congr_arg; funext j; exact (Z (r i) (z i)).apply_symm_apply ..
    let U i x:=crop p (t' i) (Pose.line N x u)
    let T':= comap (Prod.fst : I × q→ I) T
    let i (z:I × q):=z.1; let x (z:I × q):=z.2.val
    have h0 := hom_trial (p:=p) T' N M (r∘i) (z∘i) (hr.comp tendsto_comap) (Eventually.of_forall fun k=> hz k.1) H θ (K:=q) x t.hasCompactSupport t.tsupport_subset
      (Eventually.of_forall fun i=> i.2.property) h ht u
    obtain ⟨C,hC,Hs⟩:= h0.exists_pos; apply IsBigO.of_bound (Read.Value t*C)
    filter_upwards [eventually_comap.mp Hs.bound, hr.eventually self_mem_nhdsWithin,(span_nears T N M r z hr (Eventually.of_forall hz) H).eventually self_mem_nhdsWithin] with i' h' (h1 : r i'∈Ioi 0) (h2 : resize (r i') (z i')∈Ioi 0)
    have hv : ContinuousOn (V i') q:= (hy.cont _ h2 n _).mono t.tsupport_subset
    have hu : ContinuousOn (U i') q:= by
      unfold U Pose.line; simp only [crop_eq]; simp_rw [coeff_mk]; exact continuousOn_finsetSum _ fun j _=> (((Pose.birth N M H d).light _ j u).const_mul _).mono t.tsupport_subset
    rw [recruits,Pose.weighted N M H,hy.full _ h2]; change ‖t.applyTo _ - t.applyTo (U i')‖ ≤ _
    rw [← Read.smear_sub t hv hu, mul_assoc]; apply Read.value_le t (hv.sub hu)
    intro j hj; rw [Pi.sub_apply,owner i' h1 j hj]; exact h' (i',⟨j,hj⟩) rfl

include hZ
lemma screened (D : Fray (N.store.measure d)) :
    Buys T (fun i=> guide G d ((N.store.measure d).D
      (recruit (compareZ N M θ Z p (r i) (z i)) (Y (resize (r i) (z i))))-
        (N.store.measure d).D (reference G d))) (g∘r) (p+1) := by
    let R i:= Pose.foresee N M d p (new_clock N M θ (z i) (r i) p)
    let A i:= recruit (compareZ N M θ Z p (r i) (z i)) (Y (resize (r i) (z i)))
    have hi i : guide G d ((N.store.measure d).D (A i)-(N.store.measure d).D (reference G d))=
        D.stamps (fun j=> watch (D.scope j) (A i-R i)) := by
      change _ = guide G d (D.tally _); rw [D.equal,(N.store.measure d).D.map_sub]; unfold R; rw [Pose.presumes N M H] -- unfold
    simp_rw [show ∀ i, guide G d ((N.store.measure d).D
      (recruit (compareZ N M θ Z p (r i) (z i)) (Y (resize (r i) (z i))))-
        (N.store.measure d).D (reference G d))=D.stamps (fun j=> watch (D.scope j) (A i-R i)) from hi]
    simp_rw [map_sub]
    let v i j := watch (D.scope j) (A i)-watch (D.scope j) (R i)
    obtain ⟨C,hC,hw⟩:= (isBigO_pi.mpr (show ∀ j, Buys T (fun i=> v i j) (g∘r) (p+1) from fun j=>
      nephew T N M r z hr hz H θ ht h Y hy he (D.scope j).p (D.scope j).t)).exists_pos
    apply IsBigO.of_bound (‖D.stamps‖ * C); filter_upwards [hw.bound] with i hi
    exact (And.intro ((ContinuousLinearMap.le_opNorm D.stamps _).trans ((mul_le_mul_of_nonneg_left hi (norm_nonneg D.stamps)).trans_eq (mul_assoc ..).symm)) hZ).1
end
end YM.FVA2.GradedFar.Moving
