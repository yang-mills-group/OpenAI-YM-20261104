import YM.MSbar.Sage.Broad
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Heath
open Lattice Wilson RG Function Filter MeasureTheory Push.Local Push Push.AbsoluteSums WilsonStartup
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}{n:Side}{U V U' V':Config G n}{x:Site n}{R:PathData G}{σ C T a v δ w:ℝ}
open Finset RG.PathData
variable {Y X: Support n}{k M:ℕ}{p:BudgetPoint}{d:Clip}
open AnalyticBridge.VerifiedReset Next.Scheduling
lemma rise {A:ℕ}(h₀:0<σ)(hi:M<A): 1 ≤ Real.exp (σ*A)*Real.exp (-σ/2*M):=by
    rw [← Real.exp_add]; apply Real.one_le_exp; have hm: (M:ℝ) ≤ A:=by exact_mod_cast hi.le
    linarith only [mul_le_mul_of_nonneg_left hm h₀.le, mul_nonneg h₀.le (Nat.cast_nonneg (α:=ℝ) M)]
variable (h: R.Bounds d σ C T) (j:Face (Per n))
set_option quotPrecheck false
local notation "o!"=> j.1
include h
lemma lamp (hq:o!∈halo M Y → Agrees (halo (2*M) Y) U V)(hz:o!∉halo M Y → Spine Y U V): ‖R.ell U j-R.ell V j‖ ≤ C*(4*silk M σ Y o!) := by
    let b i:=R.row j.2 i; let f i:= |(b i).1|; let g i:=Real.exp (σ*(b i).2.length); let D:= silk M σ Y o!
    have hF i: ‖R.ellTerms j i U-R.ellTerms j i V‖ ≤ f i*g i * (4*D) := by
       let k:=(b i).2; let P:= Wages.walkCuts k o!
       have hz'(W): ‖R.ellTerms j i W‖ ≤ f i*2:=by rw [ellTerms,norm_smul]; exact mul_le_mul_of_nonneg_left (Slot.eval_norm ..) (norm_nonneg _)
       suffices H: Agrees P U V ∨ 1≤ g i*D by
          rcases H with h|h
          · rw [show R.ellTerms j i U=R.ellTerms j i V from congr_arg ((b i).1 • ·) (slot_reads k o! U V h),sub_self,norm_zero]; exact mul_nonneg (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) (mul_nonneg (by norm_num) (silk_pos ..))
          have h₀:= (norm_sub_le ..).trans (add_le_add (hz' U) (hz' V)); refine h₀.trans ((le_mul_of_one_le_right (show 0≤f i*2+f i*2 from by have he:0≤ f i:=abs_nonneg _; positivity) h).trans_eq ?_); ring
       by_cases he:o!∈halo M Y
       · by_cases hk:k.length ≤ M
         · have ht:P⊆ halo (2*M) Y:=seep he (fun i hi=> (separation_comm ..).trans_le ((slot_length _ o! hi).trans hk)); exact Or.inl (agrees_mono (hq he) (coe_subset.mpr ht))
         unfold D silk; rw [if_pos he]; exact Or.inr (rise h.width (lt_of_not_ge hk))
       by_cases hA: Disjoint P Y
       · exact Or.inl (hz he P hA)
       obtain ⟨y,hy,hH⟩:= not_disjoint_iff.mp hA
       right; have hi: 1 ≤ Real.exp (σ*k.length)*Real.exp (σ*↑(0:ℕ))*D:= windmill he y hH h.width k.length 0 ((separation_comm ..).trans_le (slot_length _ _ hy)); simpa only [Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] using hi
    have hm:= R.ell_dominated h j; let Z:= fun i=> R.ellTerms j i U-R.ellTerms j i V; have hs:= (h.rows j.2).2.1; have hu := hs.mul_right (4*D); have hf:= hu.of_nonneg_of_le (fun i=> norm_nonneg (Z i)) hF
    unfold ell; rw [← (hm.summable U).tsum_sub (hm.summable V)]; refine (norm_tsum_le_tsum_norm (show Summable _ from hf)).trans ((hf.tsum_le_tsum hF hu).trans ?_); rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right ((h.rows j.2).2.2) (mul_nonneg (by norm_num:0≤(4:ℝ)) (silk_pos ..))
private lemma baseG (U:Config G n): ‖R.ell U j‖≤ 2*C:=by
    let g i:=|((R.row j.2 i).1)| * Real.exp (σ*(R.row j.2 i).2.length); have hs:= (h.rows j.2).2.1
    have ht:= (R.ell_dominated h j).absolute U; apply (norm_tsum_le_tsum_norm ht).trans
    have hg(i) : ‖R.ellTerms j i U‖ ≤ g i *2 :=by
       rw [ellTerms,norm_smul]; exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg h.width.le (Nat.cast_nonneg (α:=ℝ) ((R.row j.2 i).2.length))))) (Slot.eval_norm ..) (norm_nonneg _) (h.rows j.2|>.1 i)
    refine (ht.tsum_le_tsum hg (hs.mul_right _)).trans ?_; rw [tsum_mul_right]; exact (mul_le_mul_of_nonneg_right (h.rows j.2|>.2.2) zero_le_two).trans_eq (mul_comm ..)
lemma lantern (hq:o!∈halo M Y → Agrees (halo (2*M) Y) U V) (hz:o!∉halo M Y → Spine Y U V): |‖R.ell U j‖^2/2-‖R.ell V j‖^2/2| ≤ (8*C^2)*silk M σ Y o!:=by
    have he : |‖R.ell U j‖-‖R.ell V j‖|≤ C*(4*silk M σ Y o!) := (abs_norm_sub_norm_le ..).trans (lamp h j hq hz); have hf :0≤ C:=budget_nonneg h.three
    rw [← sub_div,abs_div,abs_of_nonneg (zero_le_two (α:=ℝ)),sq_sub_sq,abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),div_le_iff₀ (by norm_num : (0:ℝ)<2)]; refine (mul_le_mul (add_le_add (baseG h j U) (baseG h j V)) he (abs_nonneg _) (by positivity)).trans_eq ?_; ring
-- Actual excluded volume from a common field halo
variable (hp:Place Y M U U' V V' p.threshold)(hk:p.B≤M)(hd:Decent d p)
def bCost (R: PathData G)(p:BudgetPoint)(d : Clip)(U V:Config G n)(j:Face (Per n)):= R.baseTerm d p U j-(d.direct*G.price (faceValue V j)+‖R.ell V j‖^2/2)
include hp hk hd
lemma soreness : |bCost R p d U U' j - bCost R p d V V' j| ≤ 16*C^2*silk M σ Y o!:=by
    have hn: 2 ≤ p.B:= hd.radius; let X:= halo p.B {o!}; let y:= touched j
    have hT : y⊆ X:= fun i hi=>halo_spec.mpr ⟨_,mem_singleton_self _,(separation_comm ..).trans_le ((WilsonStartup.visit_near _ hi).trans hn)⟩
    let t:=p.threshold; let K:= 8*C^2*silk M σ Y o!; have hx: 0≤K:= mul_nonneg (by positivity) (silk_pos ..)
    unfold bCost baseTerm; by_cases he : o! ∈ halo M Y
    · have hy(z:Site n)(hz:z∈ X): separation o! z ≤ M :=by obtain ⟨i,hi,hh⟩:=halo_spec.mp hz; exact (mem_singleton.mp hi ▸ hh).trans hk -- parse issue
      have hm : X⊆ halo (2*M) Y:= seep he hy; have hG:=kept_small_halo hd (Finset.disjoint_of_subset_left hm hp.seals_old); have hH:=kept_small_halo hd (Finset.disjoint_of_subset_left hm hp.seals_new); have hz(P' : Config G n)(he:kept d t o! P') : clipped d t (G.chord (faceValue P' j))=d.direct*G.price (faceValue P' j):=by unfold clipped; rw [if_pos (WilsonStartup.kept_small d p P' j he),G.chord_price]; ring
      have hU: faceValue U' j=faceValue U j:= (face_local j U U' (agrees_mono hp.source (coe_subset.mpr (hT.trans hm)))).symm
      have hV: faceValue V' j=faceValue V j:= (face_local j V V' (agrees_mono hp.sinks (coe_subset.mpr (hT.trans hm)))).symm
      have h₁:=lantern h j (fun _=>hp.source) (fun hn=> (hn he).elim); have h₂:=lantern h j (fun _=>hp.sinks) (fun hn=> (hn he).elim)
      rw [if_pos hG,if_pos hH,hz U hG,hz V hH,hU,hV, add_sub_add_left_eq_sub,add_sub_add_left_eq_sub]; exact (abs_sub _ _).trans ((add_le_add h₁ h₂).trans_eq (by ring))
    have hh: Disjoint X Y:= by rw [disjoint_left]; intro i hi hz; obtain ⟨j,hj,hH⟩:=halo_spec.mp hi; rw [mem_singleton.mp hj,separation_comm] at hH; exact he (halo_spec.mpr ⟨i,hz,hH.trans hk⟩)
    rw [show faceValue U j=faceValue V j from face_local _ U V (hp.old _ (hh.mono_left hT)),show faceValue U' j=faceValue V' j from face_local _ U' V' (hp.afterX _ (hh.mono_left hT)), kept_local d hd o! (hp.old _ hh)]; let Z:= d.direct*G.price (faceValue V' j)
    let u(i):= ‖R.ell i j‖ ^2 /2; let C₀:= clipped d p.threshold (G.chord (faceValue V j)); have h₀:=lantern h j (fun ha=>(he ha).elim) (fun _=>hp.afterX); split
    next h'=>
       rw [show C₀+u U-(Z+u U')-(C₀+u V-(Z+u V'))=(u U-u V)-(u U'-u V') by abel]; exact (abs_sub _ _).trans ((add_le_add (lantern h j (fun ha=>(he ha).elim) (fun _=> hp.old)) h₀).trans_eq (by ring))
    next h' => rw [show C₀+0-(Z+u U')-(C₀+0-(Z+u V'))=u V'-u U' by abel, abs_sub_comm (u V')]; linarith only [show |u U'-u V'| ≤ _ from h₀,hx]
end YM.MSbar.Heath
