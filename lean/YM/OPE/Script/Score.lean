import YM.OPE.Script.Quaver
import YM.OPE.Pulse.Extinct
/-!
# Build propagating ropes for subtraction and correcting arrays
Adapted from South/Bus and Celery. Keep pepper prices & all alignments. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I : Type}[Fintype I]{n:Side}{G:Gauge}{C:Family G}{N k m p d:ℕ}
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
section
variable {H:History G} {D':GaugeDoor (H.rep N p (m+1)) (H.rep N p m)}
set_option quotPrecheck false
local notation "R0"=> H.rep N p m
local notation "R1"=> H.rep N p (m+1)
local notation "Z"=> (H.levels.clock.op m p)
namespace Lamp
def together (q:I→ℂ)(L:I→Lamp G n): Lamp G n:= ⟨∑ i,q i • (L i).watch,∑ i,q i • (L i).sparks, combies _ (fun i=>rainbow (L i|>.lit) (q i)) _⟩
lemma together_rays (q:I→ℂ) (L:I→Lamp G n)(R:Rep G n) : (together q L).rays R= ∑ i,q i • (L i).rays R:=by unfold rays together; rw [prof_sum _ (fun i=>rainbow (L i|>.lit) (q i))]; exact sum_congr rfl fun i _=> profile_scale R.activities ..
lemma together_pays (q:I→ℂ) (L:I→Lamp G n)(R:Rep G n){e:ℝ}(hp:R.activities.KBound R.p e): (together q L).disburse R=∑ i,q i • (L i).disburse R:=by unfold disburse together; rw [coin_sum _ _ (fun i=>rainbow (L i|>.lit) (q i)) _ hp]; exact sum_congr rfl fun i _=> coin_mul ..
end Lamp
namespace Debt
lemma bunch (h:H.Selected)(hn:m<N) (hD:SoundDoor (H.levels.clock.op m p) D') {w:ℝ}{v r:I→ℝ}(q:I→ℂ)(o:Site (H.S.side (m+1) p)) {A:I→Lamp G (H.S.side (m+1) p)} {B:I→Lamp G (H.S.side m p)} (hs:∀ i, Debt H N p D' (r i) o (A i) (B i)) (hp:0≤w)(hz:∀ i,0≤ v i) (hf:∀ i,w*‖q i‖=v i*r i)(he:∑ i,v i ≤ 1) (hx:∀ i, Integrable ((A i).disburse (H.rep N p (m+1))) (prior G _)):Debt H N p D' w o (Lamp.together q A) (Lamp.together q B):=by
    choose μ y b c ht hl hy hT hQ using fun i=>(hs i).votes; let β i:= q i*y i; let b' i:=‖q i‖*b i; let c' i:=‖q i‖*c i; have hη(i):0≤ b i ∧ 0 ≤ c i:=by
       obtain ⟨L,y1,M,s,ψ,hx⟩:=hl i; obtain ⟨e,H,p⟩:=hx.cost.toll; exact ⟨sumBudget_credit hx.purchase,sumBudget_credit H⟩
    have hg(i):0 ≤ b' i:=mul_nonneg (norm_nonneg _) (hη i).1; have hγ(i):0≤ c' i:=mul_nonneg (norm_nonneg _) (hη i).2; let S:= ⋃ i,μ i
    refine ⟨⟨S,∑ i,β i,∑ i,b' i,∑ i,c' i,Set.finite_iUnion ht,?_,?_,?_,?_⟩,?_⟩
    · rw [Lamp.together_rays,Lamp.together_rays]; apply Tale.upon hD (fun i=> ((hl i).travel (q i)).climb (Y:=S) (Set.subset_iUnion μ i) le_rfl le_rfl) _ _ _ (hasSum_fintype β) ⟨hg,Summable.of_finite,(tsum_fintype ..).le⟩ ⟨hγ,Summable.of_finite,(tsum_fintype ..).le⟩
      · intro U; unfold Lamp.together; dsimp only; rw [Finset.sum_apply]; exact hasSum_fintype _
      · intro p U; rw [Finset.sum_apply,Finset.sum_apply]; exact hasSum_fintype _
      intro p U; rw [Finset.sum_apply,Finset.sum_apply]; exact hasSum_fintype _
    · rw [mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show 2*w*b' i≤v i from ?_)) he
      rw [show 2*w*b' i=v i*(2*r i*b i) from by unfold b'; calc
                   _= 2*(w*‖q i‖)*b i:= by ring
                   _= _:= by rw [hf];ring]; exact mul_le_of_le_one_right (hz i) (hy i)
    · rw [mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show w*c' i≤ v i from ?_)) he
      unfold c'; rw [← mul_assoc, hf,mul_assoc]; exact mul_le_of_le_one_right (hz i) (hT i)
    · apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) hp); rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show w*‖β i‖ ≤ v i from ?_)) he
      unfold β; rw [norm_mul, ← mul_assoc,hf,mul_assoc]; exact mul_le_of_le_one_right (hz i) (hQ i)
    simp_rw [Lamp.together_pays q _ _ (h.represents N p (m+1) hn|>.good.labels.boundK), Lamp.together_pays q _ _ ((h.represents N p m hn.le).good.labels.boundK), push_list _ (fun i=>(hx i).smul (q i)) _ (H.levels.transition_mass ..)]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [(hs i).arrives, StepData.push_smul _ _ _ _ (hx i)]
end Debt
end
set_option quotPrecheck false
open Relay GridApprox
local notation "T"=> C.path
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
variable {Q:Coefficient (C.labels.level d) (C.side k p)}{B:Album C N k p d} {x t c w E:ℝ}
    (H:C.Makes) (h:Scrim C W u ψ φ δ ζ r D) (hn:k ≤ N)
    (hm:C.ref d ≤ m) (he:m ≤ k) (hw:0<w) (hy:0<E)
    -- always exact hN via Assigned
    (hP: Asked (φ:=φ) (ζ:=ζ) (ψ:=ψ) (D:=D) (m:=m) Q E w B hn)(hB:Chant W D ζ ψ φ Q E B hn)
local notation "xo"=> (fun i=> (0:Site (C.S.side i p)))
local notation "q*"=> Size.axis (C.labels.level d)
local notation "l*" => lens C N k p d
include H h hn hm he hw
private lemma lays {Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}{x:ℕ→ℝ}(hk:Club T C.params Y! (ζ d) ψ m k N p (stair φ w m) D Z x hn): ∃ S, Drive T m k N p xo (stair φ w m) D S hn ∧ ∀ i:ℕ,m ≤ i→i ≤ k→(S i).watch=liftF T Y! N p (1,false) xo Z i ∧ (S i).rays (R i)= liftK T N p (1,false) xo Z i ∧ Integrable ((S i).disburse (R i)) (prior G _):=by
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have hz i (he:m ≤ i): 0 < stair φ w m i:= march_pos _ _ _ _ _ (fun _=>hw) hF i he _
    obtain ⟨Y,hΛ,hγ,_⟩:= h.costs.heights d m N p hm (he.trans hn)
    exact beam T C.params Y! (ζ d) ψ m k N p (1,false) xo (stair φ w m) D Z x H.wilson (H.sections d) hn hk (fun i he _=>hz i he) (fun i hi _=> by rw [show stair φ w m (i+1)=φ i*stair φ w m i from by unfold stair; rw [march,if_pos hi]]; exact mul_le_of_le_one_left (hz i hi|>.le) (hγ.level i hi)) hΛ (fun i _ _=> (embed_origin _).symm) (fun j _ hj=> by obtain ⟨w,p,hx,hv⟩:=h.costs.night.days N p j (hj.trans_le hn); exact hx.propagate)
include hy hP
lemma score_aid (i:(F).Index) : ∃ S, Drive T m k N p xo (stair φ (8*E*w) m) D S hn ∧
    (S k).watch= soarF T Y! N p B.song (-B.ear i) (1,false) xo k + l* (q* i) ∧ (S k).rays (R k)= soarK T N p B.song (-B.ear i) (1,false) xo k:=by
    let x':=8*E*w; have hE:= hP.desks i
    obtain ⟨S,hS,hU⟩:= lays H h hn hm he (show 0 < x' by unfold x'; positivity) hE.descent; rw [← show x'=8*E*w from rfl]
    refine ⟨S,hS,?_,?_⟩
    · rw [(hU k he le_rfl).1]; unfold liftF soarF radiant; rw [hE.exp]; simp_rw [stepid]; funext U; change (_:ℂ)*(_+_)=_*_+_*_; ring
    rw [(hU k he le_rfl).2.1]; unfold liftK soarK sunny; rw [hE.tank]
include hB
lemma score_mark (R₀:Lamp G (C.side k p))(h0:Ignite C.path N p k C.params (C.localSection d) Q c 0 R₀): ∃ S, Drive T m k N p xo (stair φ w m) D S hn ∧
    (S k).watch= R₀.watch+B.body ∧ (S k).rays (R k)=R₀.rays (R k):=by
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    have hz i (he:m ≤ i): 0 < stair φ w m i:= march_pos _ _ _ _ _ (fun _=>hw) hF i he _
    let X:=Option (F).Index; let P: X→∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p):=fun i=>Option.elim i B.pillar B.wing; let s:X→ℂ:= fun i=>Option.elim i (1:ℂ) (fun j=>-B.blend j); let a':=2*w; let v':=8*E*w; let w':X→ℝ:= fun i=>Option.elim i a' (fun _=>v'); let t':X→ℕ→ℝ:= fun i=>Option.elim i B.cost B.bill
    have hp i:0<w' i:=by cases i; exact mul_pos zero_lt_two hw; next=> exact (show 0 < v' by unfold v'; positivity)
    have ht i: Club T C.params Y! (ζ d) ψ m k N p (stair φ (w' i) m) D (P i) (t' i) hn:=by cases i; exact hP.passage; next i=>exact (hP.desks i).descent
    choose U hu hU using fun i=>lays H h hn hm he (hp i) (ht i)
    let Y i:=Lamp.together s (fun j=>U j i)
    let ν i:=w*‖s i‖/w' i; have hvux : ∑ i,ν i ≤ 1 := by
       have hx':0<v':=by unfold v'; positivity
       unfold ν; rw [Fintype.sum_option]; simp only [w',s,Option.elim, norm_one,mul_one,norm_neg]
       rw [show w/a'=(1:ℝ)/2 from by unfold a'; field_simp, ← Finset.sum_div,← Finset.mul_sum]; linarith only [(show w*(∑ i,‖B.blend i‖)/v'≤ 1/2 from le_trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB.worth hw.le) hx'.le) (le_of_eq (by unfold v';field_simp;norm_num)))]
    refine ⟨Y,⟨fun i hi ht=>?_⟩,?_⟩
    · have he:m ≤ i+1:=hi.trans i.le_succ; obtain ⟨v,β,hQ,Hq⟩:=h.costs.night.days N p i (ht.trans_le hn); exact Debt.bunch H.wilson (ht.trans_le hn) hQ.propagate s 0 (fun j=>(hu j).drives i hi ht) (hz _ he|>.le) (fun i=>div_nonneg (mul_nonneg hw.le (norm_nonneg _)) (hp i).le) (fun i=>stair_cost _ _ _ _ _ _ (hp i)) hvux (fun i=> (hU i _ he ht).2.2)
    have ht := plush C N k p d B.song P B.ear B.blend B.mark_ q* Q (1,false) xo (hm.trans he) hn hB.lyrics.sung hB.blended hP.pitch (fun i=> (hP.desks i).exp) hP.joints (fun i=> (hP.desks i).tank)
    rw [h0.track,h0.rays]; unfold Y; rw [Lamp.together_rays]; change ((∑ i,s i • (U i k).watch) = _) ∧ _ ;simp_rw [(show ∀ j,(U j k).watch=_ from (fun j=>(hU j k he le_rfl).1)), (show ∀ j,_ from (fun j=>(hU j k he le_rfl).2.1))]; simp only [stepid] at ht; exact ht
end YM.MergeProof.Ribbons.ManyCopies.Patrol
