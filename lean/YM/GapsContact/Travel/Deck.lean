import YM.GapsContact.Travel.Club
/-! Lifts sum into coast. Variants of Sight & Hearth with actual combined tables. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D) (L:Stock.Tabs C.path.levels)
variable {o:∀ i,Site (C.side i p)}(a:Motion) (Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g :ℕ→ℝ}
    (hK:C.ref d ≤ m)(hk:m≤k)(e:k≤N)(hw:0<w)(hS:∀ i ≥ m,i<k→ o (i+1)=(C.path.levels.clock.op i p).ratio.embed (o i))
local notation "τ"=> stair φ w m
local notation "f"=> liftF T Y! N p a o Z
local notation "Λ"=> liftK T N p a o Z
include h H hK hk e hw hS
lemma logBeams (he:Club T C.params Y! (ζ d) ψ m k N p (fun _:ℕ=>w) D Z g e) :∃ G', Wakes T m k N p o (fun _:ℕ=>w) f G' D e∧ (∀ i≥m,i≤k → profile (R i).activities (G' i)=Λ i ∧ Integrable (coin (R i) (f i) (G' i)) (prior G _)) ∧ ∀ U,w*‖(f m) U‖ ≤ 2 ∧ w*(∑ i:Box (C.side m p),‖profile (R m).activities (G' m) i U‖)≤1:=by
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    obtain ⟨Y,hΛ,hγ,_⟩:= h.costs.heights d m N p hK (hk.trans e); let x:= fun (_:ℕ)=>w;
    obtain ⟨t,hT,hσ⟩:= chapter T C.params Y! (ζ d) ψ m k N p a o x D Z g H.wilson (H.sections d) e he (fun j hj _=> hw) (fun _ _ _=>le_rfl) hΛ hS (fun j _ hj=> by obtain ⟨_,_,hx,_⟩:=h.costs.night.days N p j (hj.trans_le e); exact hx.propagate)
    refine ⟨t,hT,fun j hj ht=> ⟨hσ j hj ht,?_⟩,fun U=>?_⟩
    · have hz:= he.ticks j hj ht; obtain ⟨X,hQ,hh,hα⟩:= sparkling T C.params Y! (Z j) a (o j) (alto T j d) H.wilson 0 (ht.trans e) (H.sections d) hz.1 hz.2
      rw [coin_port _ _ (hT.stocked j hj ht) hh ((hσ j hj ht).trans hQ) ((H.wilson.represents _ _ _ (ht.trans e)).good.labels), liftF,hα]
      exact (tint _ _ _ (play_integrable T N H.wilson (ht.trans e) hz.1 hz.2)).smul _
    have hi:=he.rates m le_rfl hk
    rw [hσ _ le_rfl hk]; exact toasted C N m p d H Z (ζ d) hK (hk.trans e) a (o m) (he.ticks _ le_rfl hk|>.2) hw.le hi (hΛ.coin m le_rfl) U

end YM.MergeProof
end
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
section
variable {I:Type}[Fintype I](h:Scrim C W u ψ φ δ ζ r D)
variable {o:∀ i,Site (C.side i p)}{x:I→ℝ}(a:I→ℂ){F':I→∀ i:ℕ,Config G (C.side i p)→ℂ}{K:I→∀ i:ℕ,ℕ → Config G (C.side i p)→ℂ}
   (hk:m≤k)(e:k≤N)(hw:0<w)(hx:∀ i,0 < x i)(hz:∑ i,w*‖a i‖/x i≤1)
local notation "t!"=> stair φ
local notation "f"=> fun j=>∑ i,(a i • F' i j)
local notation "Z"=> fun j=>∑ i,(a i • K i j)
include H e h hw hx hz
lemma arrangedD (hh:∀ i,Wakes T m k N p o (fun _:ℕ=>x i) (F' i) (K i) D e)(hc:∀ i j,m ≤ j→ j≤k→ Integrable (coin (R j) (F' i j) (K i j)) (prior G _)) : Wakes T m k N p o (fun _:ℕ=>w) (f) (Z) D e:=by
    have hJ(i j)(hp : m ≤ j)(hv : j≤k): Dominated (a i • K i j):=rainbow ((hh i).stocked j hp hv) _; let Y:=f; let Z':=Z
    refine ⟨fun i he h=> combies _ (fun j=> hJ j i he h) _,fun j hj hv=> ?_,fun i hK hm=>?_⟩
    · choose μ y b c ht he hα hf using fun i=> (hh i).sways j hj hv
      let A:=⋃ i,μ i; let B:= Fintype.card I; let β i:=a i*y i
      let b' i:=‖a i‖*b i; let c' i:=‖a i‖*c i; have hη(i):0≤ b i ∧ 0 ≤ c i:=by
         obtain ⟨L,y1,M,s,ψ,hx⟩:=hf i; obtain ⟨e,H,p⟩:=hx.cost.toll
         exact ⟨sumBudget_credit hx.purchase,sumBudget_credit H⟩
      have hg(i):0 ≤ b' i:=mul_nonneg (norm_nonneg _) (hη i).1; have hγ(i):0≤ c' i:=mul_nonneg (norm_nonneg _) (hη i).2
      let u':= w; let τ' i:= x i; let pX i:= w*‖a i‖/x i; have hp i:0 ≤ pX i:=div_nonneg (mul_nonneg hw.le (norm_nonneg _)) (hx i).le
      refine ⟨A,∑ i,β i,∑ i,b' i,∑ i,c' i,Set.finite_iUnion ht,?_,?_,?_⟩
      · rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show 2*u'*b' i≤pX i from ?_)) hz
        rw [show 2*u'*b' i=pX i*(2*τ' i*b i) from by unfold b'; have hE:u'*‖a i‖=pX i*τ' i:= (show _ from (by unfold u' pX τ'; field_simp [(hx i).ne'])); calc
                   _= 2*(u'*‖a i‖)*b i:= by ring
                   _= _:= by rw [hE];ring]; exact mul_le_of_le_one_right (hp i) (he i)
      · rw [Finset.mul_sum]; refine le_trans (Finset.sum_le_sum (fun i _=> show u'*c' i≤ pX i from ?_)) hz
        unfold u' c'; rw [← mul_assoc, show w*‖a i‖ = pX i * x i from (by unfold pX; field_simp [(hx i).ne']),mul_assoc]; exact mul_le_of_le_one_right (hp i) (hα i)
      obtain ⟨v,β₁,hQ,H⟩:=h.costs.night.days N p j (hv.trans_le e)
      change Tale A _ _ _ (∑ i,a i • F' i (j+1)) (profile _ (∑ i,a i • K i (j+1))) (profile _ (∑ i,a i • K i j)) _ _ _ _
      -- elem
      simp_rw [prof_sum _ (fun i=> hJ i (j+1) (hj.trans j.le_succ) hv), prof_sum _ (fun i=>hJ i j hj hv.le),profile_scale]; apply Tale.upon hQ.propagate (fun i=> ((hf i).travel (a i)).climb (Set.subset_iUnion μ i) le_rfl le_rfl) _ _ _ (hasSum_fintype β) ⟨hg,Summable.of_finite,(tsum_fintype ..).le⟩ ⟨hγ,Summable.of_finite,(tsum_fintype ..).le⟩
      · intro i; rw [Finset.sum_apply]; exact hasSum_fintype _
      · intro i U; rw [Finset.sum_apply, Finset.sum_apply]; exact hasSum_fintype _
      intro i U; rw [Finset.sum_apply,Finset.sum_apply]; exact hasSum_fintype _
    let H':= hm.trans_le e; have hR:= (H.wilson.represents  N p (i+1) H').good.labels; have hR₀:= (H.wilson.represents N p i H'.le).good.labels
    simp_rw [coin_sum _ _ (fun j=>hJ j i hK hm.le) _ hR₀.boundK, coin_sum _ _ (fun j=> hJ j (i+1) (hK.trans i.le_succ) hm) _ hR.boundK,coin_mul,push_list _ (fun j=>(hc j (i+1) (hK.trans i.le_succ) hm).smul (a j)) _ (T|>.levels.transition_mass ..)]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [(hh j).feeds i hK hm, StepData.push_smul _ _ _ _ (hc j _ (hK.trans i.le_succ) hm)]
end
end YM.MergeProof
end
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open GapsContact.Dusk
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d J:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
lemma club_restrict {x:ℕ→ℝ}{w:ℝ}{f:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)}(hm:m≤k){hk:k≤N}(hc:Club T C.params Y! (ζ d) ψ J k N p (stair φ w m) D f x hk): Club T C.params Y! (ζ d) ψ J m N p (fun _=>w) D f x (hm.trans hk):=by
   refine ⟨fun i hi hp=>hc.ticks i hi (hp.trans hm),fun i hi hp=>?_ ,fun i hi hp=>hc.votes i hi (hp.trans_le hm)⟩
   have h:=hc.rates i hi (hp.trans hm); rw [show stair φ w m i=w from march_beforeD ..] at h; exact h; assumption
section
variable {I V:Type}[Fintype I][Fintype V][DecidableEq V] {B:Census V}(h:Scrim C W u ψ φ δ ζ r D)
variable (o:∀ i:ℕ,V→Site (C.side i p)){x:I→ℝ}(s:V→Motion)(a:V→I→ℂ) (Z:I→∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g:I→ℕ→ℝ}
   (e:m≤N)(hw:0<w)(hx:∀ i,0<x i)(hz:∀ i,∑ j,w*‖a i j‖/x j≤1)
local notation "f"=> fun i j=>∑ n, a j n • liftF T Y! N p (s j) (fun l=>o l j) (Z n) i
local notation "p!"=> fun i j=>∑ n, a j n • liftK T N p (s j) (fun l=>o l j) (Z n) i
include H h

omit H h [Fintype V] in
lemma gust_cross {G:Gauge}{A:History G}{N m k p J:ℕ} {x:Config G (A.S.side k p)→Poly B} (hi:J ≤ m) (h:m ≤ k): gust A N p k x J (hi.trans h) = gust A N p m (gust A N p k x m h) J hi:=by
   induction hi using Nat.decreasingInduction with
   | self=>rw [gust_base]
   | of_succ i hi ih=> rw [gust_step A N p k x (hi.trans_le h), gust_step A N p m _ hi, ih]

set_option maxHeartbeats 800000 in
lemma decks {M:Config G (C.side m p)→Poly B} (hG:G.Simple)(K:Shipper T r D) (ht:ℓ ≤ J)(hk:J ≤ m) (hi: Integrable M (prior G _))(hη:Migrating T J p m o)(hM:∀ i,J ≤ i→ i ≤ m→Injective (o i)) (he:∀ i:I,Club T C.params Y! (ζ d) ψ J m N p (fun _=>x i) D (Z i) (g i) e) (hQ:Served (R m) (f m) (p! m) M (o m) (fun _=>w) (C.path.levels.budget m).supportExponent 1) (hw:0<w)(hx:∀ i,0<x i)(hz:∀ i,∑ j,w*‖a i j‖/x j≤1): let v := paceFactor T m J * w; Served (R J) (f J) (p! J) (gust T N p m M J hk) (o J) (fun _=>v) (C.path.levels.budget J).supportExponent 1∧ Vault (fun _=>v) (f J) (p! J) 2 1:=by
    let X i j:= liftF T Y! N p (s i) (fun l=>o l i) (Z j); let Y i j:=liftK T N p (s i) (fun l=>o l i) (Z j); let f':= f; let p':= p!
    choose G' H' hp' hP using fun (i:V)(j:I)=>logBeams C N m J p d H (x j) h (s i) (o:=fun l=> o l i) (Z j) ht hk e (hx j) (fun l hl hL=> (congr_fun (hη.mare l hl hL) i).symm) (he j)
    let Fv j (i:V):= ∑ l, a i l • G' i l j
    have hW (i:V) : Wakes T J m N p (fun j=>o j i) (fun _=>w) (fun j=>f' j i) (fun j=>Fv j i) D e:= arrangedD C N m J p H w h (a i) e hw hx (hz i) (H' i) (fun j l hl hL=> (hp' i j l hl hL).2)
    have hj(j)(hr:J ≤ j)(hn:j ≤ m): tapes T p N Fv j=p' j:=by
       unfold p'; funext i; change profile _ (Fv j i)=_
       have hx(l): Dominated (a i l • G' i l j):= rainbow ((H' i l).stocked j hr hn) _
       simp_rw [Fv, prof_sum _ hx, profile_scale]; exact Finset.sum_congr rfl fun n _=> congr_arg _ ((hp' i n j hr hn).1)
    have H':= GapsContact.Dusk.continue_ T r D K hG N p m J w e H.wilson hi hw hW hη hM (fun j _ _=> h.back j) (show Served _ (f' m) (tapes T p N Fv m) M _ _ _ _ from (hj m hk le_rfl).symm ▸ hQ) hk
    rw [hj J le_rfl hk] at H'; have hh:paceFactor T m J*w ≤ w:=mul_le_of_le_one_left hw.le ?_ -- left/right
    · refine ⟨H',⟨fun i U=> ?_,fun i U=>?_⟩⟩
      · refine le_trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _)) (le_trans ?_ (fare1 w _ hw hx (hz i) (fun j=> X i j J U) zero_le_two (fun j=> hP i j U|>.1)))
        simp_rw [Finset.sum_apply]; rfl
      rw [← Finset.mul_sum]
      refine (mul_le_mul_of_nonneg_right hh (sum_nonneg fun i _=>norm_nonneg _)).trans ?_; simp_rw [Finset.sum_apply]; exact fare w _ hw hx (hz i) (fun j l=>Y i j J l U) zero_le_one (fun j=>by
         have h:= (hP i j U).2; rw [(hp' i j J le_rfl hk).1] at h; exact h)
    exact (tour_limit T r D K m J).2
lemma solos {M:Config G (C.side m p)→Poly B} (hG:G.Simple)(K:Shipper T r D) (ht:ℓ ≤ J)(hk:J ≤ m) (hi: Integrable M (prior G _))(hη:Migrating T J p m o)(hM:∀ i,J ≤ i→ i ≤ m→Injective (o i)) {g:ℕ→ℝ} {F':∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)} (he: Club T C.params Y! (ζ d) ψ J m N p (fun _=>w) D F' g e) (hw:0<w) : let X (i:ℕ) (j:V):=liftF T Y! N p (s j) (fun l=>o l j) F' i; let Y (i:ℕ) (j:V):= liftK T N p (s j) (fun l=>o l j) F' i; Served (R m) (X m) (Y m) M (o m) (fun _=>w) (C.path.levels.budget m).supportExponent 1 → let v := paceFactor T m J * w; Served (R J) (X J) (Y J) (gust T N p m M J hk) (o J) (fun _=>v) (C.path.levels.budget J).supportExponent 1∧ Vault (fun _=>v) (X J) (Y J) 2 1:=by
    simpa only [one_smul, Fintype.sum_unique] using! (fun hQ => decks (M:=M) (x:=fun _:Unit=>w) C N m p d J H w h o s (fun _ _=>1) (fun _=> F') e hG K ht hk hi hη hM (g:=fun _=>g) (fun _=>he) hQ hw (fun _=>hw) (fun i=>by simp[hw.ne']))
end
end YM.MergeProof
