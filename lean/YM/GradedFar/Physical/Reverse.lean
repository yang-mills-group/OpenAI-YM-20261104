import YM.GradedFar.Physical.Compact

/-!
 Recover other direction on fixed spans, no extra PoseFit orientation hypothesis needed.
-/
namespace YM.FVA2.GradedFar.Physical.ScaleBudget
noncomputable section
open Filter Function Real PowerSeries Set Asymptotics
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open O O.Score O.Enh Moving Growth Pose Books Scale Dframe
open Continuation Continuation.Window
open MS.Book.Program
open scoped Topology BigOperators Classical ContDiff
variable {G : Gauge} {n m d h p : ℕ} {I:Type} (N : WilsonPrescription G)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) {simple : G.Simple} {A : MS.Land.Prescription (Press.portDeck G)} (H : Main.Match N simple M A true)
local notation "τ"=>𝓝[>] (0:ℝ)
local notation "g"=>gYM G
local notation "ν"=>Teller.logNu 1
local notation "ψ"=> GroupS.ψ N.criterion M ν
variable {R : Family G} {f : Extraction.Order} {P : Table R.book}
    (U : Spec.Final R f P) (J K : FramesH P) (θ:ℝ→ℝ) (Q:Earned N M U J K θ)
    (T : Filter I) {r z:I→ℝ} (hr:Tendsto r T (𝓝[>] (0:ℝ)))
local notation "L"=> g∘ r
local notation "W"=> fun i=>resize (r i) (z i)
local notation "Z"=>fun d=> Zenith (next K d)
local notation "KP"=> fun d y=> names (Kseries N M d (-y))
section lemmas
variable {V:Type}[NormedAddCommGroup V][NormedSpace ℂ V]
private lemma substitute_bg {u y:I→ℂ}{Y:I→ PowerSeries ℂ}{Q':I→Portion V}{l:I→ℝ}(hp:Tendsto l T (𝓝 0))(ht:Till T Q' l p)
    (hv:Buys T y l 0)(hY:∀ i,Rooted (Y i)) (h:Pays T y (fun i=> tells (Y i)) l p u)(hl:Buys T u l 1) :
    Pays T (fun i=>blend (Q' i) p (y i)) (fun i=>Program.substitute (Y i) (Q' i)) l p u := by
    let t (i:I):= blend (tells (Y i)) p (u i)
    have he (j:ℕ) : Buys T (fun i=>y i^j-t i^j) l (p+1) := by
       induction j with| zero=>simp_rw [pow_zero,sub_self];exact isBigO_zero ..| succ j ih=>
         have h1:=before T hl hp h.1; have h1:=times_cost T ih h1
         have h2:=times_cost T h.2 (y:=fun i=> (y i)^j) (n:=0) (by have hx:=hv.pow j; simpa only [Buys,pow_zero,one_pow] using hx)
         exact (h1.add h2).congr_left (fun i=> by unfold t; rw [pow_succ,pow_succ]; ring)
    have hx : Buys T (fun i=>blend (Q' i) p (y i)-blend (Q' i) p (t i)) l (p+1) := by
       unfold blend; simp_rw [← Finset.sum_sub_distrib,← sub_smul]; apply IsBigO.sum; intro j hj; exact budget_times_smul T (he j) (ht _ (Finset.mem_range_succ_iff.mp hj))
    exact ⟨shifted T h.1 ht,(hx.add (recrop_substitution T hl hp h.1 hY ht)).congr_left (fun i=> by unfold t; abel)⟩
end lemmas
private lemma blended (hp:1≤p)(t:ℂ):blend (tells PowerSeries.X) p t=t:= by
    unfold blend tells; rw [Finset.sum_eq_single 1]; · simp
    · intro b hb he; simp [coeff_X,he]
    intro h; simp at h; omega
private lemma blent (t:ℂ): blend (names (1:Guard G d)) p t=1:=by
    unfold blend names; rw [Finset.sum_eq_single 0]; · simp
    · intro b hb he; simp [coeff_one,he]; ext1 x; change (t^b) • (0:RowSpace G d)=0; exact smul_zero _
    simp
variable {C:ℝ} (hz:∀ᶠ i in T, z i∈Icc 0 C)
include H Q hr hz
lemma reversing (hp:1≤p) :
      Buys T (fun i=> (θ (r i):ℂ) - bend N M (-(z i)) p (θ (W i):ℂ)) L (p+1) ∧
      Buys T (fun i=> Z d (W i) (-z i)-crank N M d (-z i) p (θ (W i):ℂ)) L (p+1) := by
    let t i:ℂ:=θ (r i); let x i:ℂ:= θ (W i); let C' i:= ψ (-z i)
    have hm:= measuring T N M r hr H θ Q.clock
    let L':= timespan (G:=G) T r hr; have hs :=arriving N M H U J K θ Q T hr hz; have hQ : Tendsto x T (𝓝 0):= theta_nears N M H θ Q.clock L' z hs
    obtain ⟨hx,hZ⟩:=going (p:=p) (d:=d) N M H U J K θ Q T hr hz
    have hl:Tendsto L T (𝓝 0):= (shrink simple).comp hr; have ht:= Pays.fee T hm hl hx
    have hb : ∀ᶠ i in T,-z i∈ Icc (-C) 0:= hz.mono (fun i h=> ⟨neg_le_neg h.2,neg_nonpos.mpr h.1⟩)
    have h' : Till T (fun i=> KP d (-(z i))) L p:= point_frame N M H T isCompact_Icc (z:=fun i=> -z i) hb
    have h1:= substitute_bg T hl h' ht (fun i=> (tendsK N M H _).start) hx hm
    have h2:= substitute_bg T hl (point_ψ (z:=fun i=> -z i) N M H T isCompact_Icc hb) ht (fun i=> (tendsK N M H _).start) hx hm
    constructor
    · refine h2.2.neg_left.congr_left (fun i=>?_)
      dsimp only; rw [← composition_tells _ _ (tendsK N M H _|>.start), ← Lclock N M H,add_neg_cancel,neg_zero,zero_clock N M H,blended hp]; simp [bend,resize]
    let A i:= Z d (r i) (z i); let B i:= Z d (W i) (-z i)
    let M' i:=crank N M d (-(z i)) p (θ (W i):ℂ)
    have he : Buys T (fun i=>A i*M' i-1) L (p+1) := by
      apply (Pays.joint T hm hl hZ h1).2.congr_left; intro i
      simp_rw [← composition_names, ← revenue_names, ← Lframe N M H, add_neg_cancel,neg_zero, zero_frame N M H, blent]; rfl

    have h: Buys T B L 0 := budget T (C:=2) (by
      filter_upwards [hr.eventually (Q.main 0 d zero_lt_one zero_lt_one).2, window_pass N M H U J K θ Q T hr hz,hz] with i hi hr ht; exact (hi _ ht.1 hr).2 )
    have hb:= times_cost T h he; rw [zero_add] at hb; refine hb.neg_left.congr_left (fun i=> ?_); dsimp only; rw [mul_sub, ← mul_assoc, show B i*A i=1 from (Growth.back (Z d) (r i) (z i) (hasMotion K d)).1, mul_one,one_mul]; simp [B,M',resize]
end
end YM.FVA2.GradedFar.Physical.ScaleBudget
