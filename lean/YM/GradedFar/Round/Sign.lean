import YM.GradedFar.Round.Retails

/-!
# PoseFit's applied (F.3) includes for the varying installation
  Here is the price for the F.3 on the proceeds of an arbitrary application;
  including later at comap/g-promise vs grid. Retaining orientation and signed calibration.
-/
namespace YM.FVA2.GradedFar.Physical.Round
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh
open Moving Growth Pose Books Scale Dframe Jury
open Continuation Continuation.Window
open XSpace.Rose
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m h t p : ℕ} {I J:Type} {d : Fin n → ℕ}{e: Fin m→ℕ} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
variable (T:Filter I) (r:I→ℝ) (hr:Tendsto r T (𝓝[>] (0:ℝ))) {t':I→ℝ}
variable {F:Pose.Plans G h} 
  {D':I→ Normalize.Change G h} (ht:Tendsto (fun i=> t' i/gYM G (r i)) T (𝓝 1))
local notation "L"=>gYM G ∘ r
include H hr ht
lemma notice_conversion (q k:ℕ)(hp:p ≤ q)(hk: p+1≤k) {K:Set (Points n)}(hK:IsCompact K)(hx: K⊆conf n)(u:Tags G h n)
    (hD:Buys T (fun i=> guide G h (D' i)) L k)(hN : Notice N T r q k F t' D' K u) :
    let S:= I × ↥K; let p' := (Prod.fst:S→I); let x (i:S):=(i.2.val); let t i:ℂ:=t' (p' i)
    Pays (comap p' T) (fun i=> F (r (p' i)) n (x i) u) (fun i=> tells (Pose.line N (x i) u)) (L ∘ p') p t := by
   intro S p' x t; let f:= comap p' T
   have ht':= notice_lost N M H T r hr ht q k hK hx u hD hN; let g':=L ∘ p'
   let V i:= tells (Pose.line N (x i) u)
   have he (q:ℕ): Till f V g' q:= beauty f N M _ (hr.comp (show Tendsto p' f T from tendsto_comap)) H _ hK hx (Eventually.of_forall fun i=> i.2.property) u
   have h0 := ((shrink simple).comp hr).comp (show Tendsto p' f T from tendsto_comap)
   have hΘ: Buys f t g' 1:= (sailing N M H T r hr ht).comp_tendsto (show Tendsto p' f T from tendsto_comap)
   have hx : Buys f (fun i=> F (r (p' i)) _ (x i) u - blend (V i) q (t i)) g' k := by
     apply IsBigO.congr_left ht'
     intro i
     exact congr_arg (fun z : ℂ => F (r (p' i)) n (x i) u - z)
       (crop_by (Pose.line N (x i) u) q (t' (p' i)))
   have hi (a b:ℕ)(hp:a≤b)(i:S) : blend (V i) b (t i) - blend (V i) a (t i)=
       ∑ j∈Finset.Ico (a+1) (b+1), (t i)^j • V i j := by unfold blend; rw [Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hp)]
   have hz: Buys f (fun i=> blend (V i) q (t i) - blend (V i) p (t i)) g' (p+1) := by
       simp_rw [hi p q hp]; apply IsBigO.sum; intro j hj; have hh:= Finset.mem_Ico.mp hj; exact budget_times_smul f (budget_growth f (budget_pow f hΘ j) _ hh.1 (jet_level f h0)) (he q j (by omega))
   exact ⟨he p, ((budget_growth f hx (p+1) hk (jet_level f h0)).add hz).congr_left fun i=> by unfold V; abel⟩

section
variable {F:Pose.Plans G 6}{Y:ℝ→ Prediction G 6}(H' : Held N Y F) {D':I→Normalize.Change G 6}
local notation "Q"=>Rose.test N.criterion
local notation "Z"=>tsupport Q
private lemma canopy (q k:ℕ)(hp:p ≤ q)(hk:p+1≤ k)(hD:Buys T (fun i=> guide G _ (D' i)) L k)
    (hN:∀ s:Badge, Notice N T r q k F t' D' Z (missing (tag G) s)) :
    Terms T (fun i=>L i^(p+1)) (fun i (x:↥Z)=> Pose.value (Pose.watchRose F (r i) x.val) -
      crop p (t' i) (Select.Single (Pose.Bbook N 6) x.val)) := by
  let S:= I × ↥Z; let p' := (Prod.fst:S→I); let x (i:S):=(i.2.val); let t i:ℂ:=t' (p' i); let f:= comap p' T
  let A i:= batchT (fxt (Pose.Bbook N 6) (x i)); let U (b: Badge) i:= Pose.watchRose F (r (p' i)) (x i) b; let T':=L ∘ p'
  have H' (b: Badge): Pays f (U b) (fun i=>tells (A i b)) T' p t :=
    notice_conversion N M H T r hr ht q k hp hk (Rose.test N.criterion).hasCompactSupport (Rose.test N.criterion).tsupport_subset (missing (tag G) b) hD (hN b)
  have hf:Tendsto T' f (𝓝 0):=((shrink simple).comp hr).comp tendsto_comap; have hT: Buys f t T' 1:= (sailing N M H T r hr ht).comp_tendsto tendsto_comap
  have H2 := addition f (addition f (mult f hT hf (H' {0,1}) (H' {2})) (mult f hT hf (H' {0,2}) (H' {1}))) (mult f hT hf (H' {1,2}) (H' {0})); have X:= mult f hT hf (mult f hT hf (H' {0}) (H' {1})) (H' {2})
  have H3:= addition f (subtraction f (H' Finset.univ) H2) (addition f X X)
  simp_rw [crop_by,Pose.value, Select.Single, b3,two_smul,two_mul]; exact H3.2

open private posed from YM.GradedFar.Moving.Tempo
include H'
lemma received (q k:ℕ)(hp:p ≤ q)(hk:p+1≤ k)(hp':1≤p)(hD:Buys T (fun i=> guide G _ (D' i)) L k)
    (hN:∀ s:Badge, Notice N T r q k F t' D' Z (missing (tag G) s)) :
    Buys T (fun i=> (Pose.kinetic N F (r i):ℂ) - (t' i:ℂ)) L (p+1) := by
  obtain ⟨C,hC,hv⟩:= Terms.price (canopy N M H T r hr ht q k hp hk hD hN)
  let c:=cT N.criterion.cut G N.criterion.image; have hc: 0 < |c| :=abs_pos.mpr N.criterion.fresh.ne
  apply IsBigO.of_bound (O.Read.Value Q*C/|c|)
  filter_upwards [hv,hr.eventually self_mem_nhdsWithin] with i hX (h : r i∈Ioi 0)
  let F' x:= Pose.watchRose F (r i) x
  let B x:=crop p (t' i) (Select.Single (Pose.Bbook N 6) x)
  have hz (b):ContinuousOn (fun x=> F' x b) Z := (H'.cont _ h 3 _).mono (Rose.test N.criterion).tsupport_subset
  have ha : ContinuousOn (fun x=> Pose.value (F' x)) Z := by
    unfold Pose.value; exact ((hz _).sub ((((hz _).mul (hz _)).add ((hz _).mul (hz _))).add ((hz _).mul (hz _)))).add
      (ContinuousOn.const_mul (((hz _).mul (hz _)).mul (hz _)) _)
  have hb : ContinuousOn B Z := by
    simp only [B, crop_eq]
    exact continuousOn_finsetSum _ fun j _=> ((Select.steady _ (Pose.birth N M H 6).1).const_mul _).mono (Rose.test N.criterion).tsupport_subset
  let ψ : ℂ := c*(t' i:ℂ)
  have hw0 : (Rose.test N.criterion).applyTo B=ψ := posed N M H p hp' (t' i)
  have hx : ‖Pose.total N F (r i)-ψ‖ ≤ Read.Value Q*(C*‖L i ^(p+1)‖) := by
     rw [←hw0, Pose.total, ← Read.smear_sub Q ha hb]; exact Read.value_le _ (ha.sub hb) (fun j hj=> hX ⟨j,hj⟩)
  have he : (Pose.total N F (r i)-ψ).re=(Pose.kinetic N F (r i)-t' i)*c := by
     change ( _ - ψ).re= ((Pose.total N F (r i)).re / c - t' i)*c; rw [Complex.sub_re, sub_mul, div_mul_cancel₀ _ (abs_pos.mp hc)]; unfold ψ; rw [← Complex.ofReal_mul,Complex.ofReal_re,mul_comm (t' i) c]
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,show Read.Value Q*C/|c| * _=Read.Value Q*(C*‖L i^(p+1)‖) / |c| by ring, le_div_iff₀ hc, ←abs_mul,← he]
  exact (Complex.abs_re_le_norm _).trans hx
end
end
end YM.FVA2.GradedFar.Physical.Round
