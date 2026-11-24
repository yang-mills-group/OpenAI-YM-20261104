import YM.RG3.Script.Bale
/-! # Introduce all needed section labels BEFORE forced merge. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Script.Edition
open Function Lattice RG Wilson Overlay Marker RG3.Forms RG3.Render RG3.Press RG3.Primary Ac Extra.Multi Push.AbsoluteSums MeasureTheory Extra.Iteration Source Push.Local Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {n : Side} {V : Type} [DecidableEq V] [Fintype V] {R:Census V}{ζ : V→Site n}{G : Gauge}
 {P : Rep G n}{d : Deck R P}{e : Edition ζ R G}{D:V→ℕ}{H : Hol G}{X:(s:V)→Labels.Frame G (D s)}{L:(s:V)→SectionData (X s)}
 {k : V→ℝ}
variable (hr: ∀ s, Readable H (L s) P.p n (k s))(hz:d.contents.origins=ζ)(he:d.Active)(h:e.Principle P.p)
  {a δ : ℝ}{m : ℕ→ℝ}{w:V→ℝ}(hl: Loaded H a m δ L d e k w)(hw: ∀i,0<w i)
include hr hz he h hl hw

def tonic (d:Deck R P)(e:Edition ζ R G)(H:Hol G)(L:(s:V)→SectionData (X s))(hr:∀ i, Readable H (L i) P.p n (k i)) : Feed G n R (V×ℕ) := ⟨fun x=>(jointFeed x.1 d e L H hr).column x.2,fun x=>(jointFeed x.1 d e L H hr).value x.2⟩
def bracken (d:Deck R P)(e:Edition ζ R G)(k:V→ℝ)(H:Hol G)(X:(s:V)→Labels.Frame G (D s))(m:ℕ→ℝ) : V×ℕ→ℝ:= fun x=> Primary.ink (F:=X x.1) x.1 (e.scribe d) H (k x.1) m x.2 -- placeholder

local notation "F"=> tonic d e H L hr

lemma restore {M : ℕ} (hO : Occupancy ζ M) (ha : P.p.supportExponent+1+1 ≤ a) (hs : 0 ≤ δ):
    (F).Keeps P.p ζ ∧ (F).Worth w P.p.B (P.p.supportExponent+1) (bracken d e k H X m) (M* siteFactor P.p.B*δ) ∧
      (∀ i,Feed.hot ((F).mode i)) ∧ (∀ U,(F).text U=∑ i,(jointFeed i d e L H hr).text U):= by
  have hx s:= Primary.kept s (e.scribe d) H (L s) (hr s) (authorized hz h he)
  have ht s:= (trunk hr hz he h hl hw (show P.p.supportExponent+1 ≤ a by linarith) s).1
  let f:=bracken d e k H X m
  have hf i : 0≤f i:=(ht i.1).positive _
  have he' s (j) : ζ s ∈ Primary.stem s (e.scribe d) (L s) j:= mem_union_right _
    (by simpa only [SectionData.footprint,scribe,map_zero,zero_add] using mem_image_of_mem (fun x=>wrap n x + ζ s) (hr s).sound.anchored)
  have hZ (i : V×ℕ) : Feed.hot ((F).mode i):= R.fire_hot _
  have Hf : (F).Worth w P.p.B (P.p.supportExponent+1) f (M*siteFactor P.p.B*δ) := by
    refine ⟨hf,fun i=>(ht i.1).always i.2,?_⟩
    refine root_hit (mode:=fun i : V×ℕ=> (R.fire i.1).val) hO (fun i=>mul_nonneg (Poly.worth hw _).le (hf i)) hs (fun i _=>?_) (fun s=>?_)
    · exact ⟨i.1,mem_singleton_self _,he' i.1 i.2⟩
    refine budget_of_sum (fun i=>?_ ) (fun t=>?_)
    · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Poly.worth hw _).le (hf _)); rfl
    let Z(j:V×ℕ):= if s=j.1 then Real.exp ((P.p.supportExponent+1+1)*coverNumber P.p.B ((F).locus j))*(Poly.toll w (R.fire j.1)*f j) else 0
    have hU : (∑ j∈t,Z j) ≤ w s * (∑ i∈ (t.image Prod.snd), paidR H a m L d e k s i) := by -- H shadow; rename
      rw [show (∑ j∈t,Z j)=∑ j∈t.filter (fun j=>s=j.1),Z j from by rw [Finset.sum_filter]; refine Finset.sum_congr rfl (fun j _=>?_); unfold Z; split <;> simp]
      let v:=t.filter (fun j=>s=j.1); let q:=v.image Prod.snd
      have hp (i) (hi:i∈v) : s=(i:V×ℕ).1:=(Finset.mem_filter.mp hi).2
      have hE : (∑ j∈v,Z j) ≤ ∑ i∈ q,w s*paidR H a m L d e k s i:= by
        unfold q; rw [Finset.sum_image (fun i hi j hj hz=> Prod.ext ((hp i hi).symm.trans (hp j hj)) hz)]
        refine Finset.sum_le_sum fun i hi=>?_ ; unfold Z; rw [if_pos (hp i hi),Poly.solo_toll]
        obtain ⟨i,j⟩:=i; have he:=hp (i,j) hi; change s=i at he; subst i
        apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (show (P.p.supportExponent+1+1)*_ ≤ a* _ from mul_le_mul_of_nonneg_right ha (by positivity))) (mul_nonneg (hw _).le (hf _)))
        unfold f paidR bracken expense; apply le_of_eq; exact mul_left_comm ..
      rw [mul_sum]; apply hE.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image (Finset.filter_subset ..)) (fun i _ _=> (hl.2 _).1 i))
    exact le_trans (by simpa only [Z, show ∀ i:V×ℕ,(s∈(R.fire i.1).val)=(s=i.1) from fun i=>propext mem_singleton] using! hU) ((by rw [mul_sum]; exact budget_sum (hl.2 s) _))
  refine ⟨⟨fun i U hh=>(hh (hZ i)).elim,fun i=>(hx i.1).gauge i.2,fun i=>(hx i.1).borel i.2, fun i=>(hx i.1).read i.2, fun i=>(hx i.1).flags i.2,fun i U x hm he=> ?_⟩,Hf,hZ,fun U=>?_⟩
  · obtain h:x=i.1:=mem_singleton.mp he; exact h ▸ he' i.1 i.2
  have hα:0≤P.p.supportExponent+1:=by linarith [P.p.exponent_pos]
  let f' i:=Poly.send ((F).mode i) ((F).value i U)
  have hS:Summable f' := (Poly.budgeted hw (Hf.weighted_enough hα hw) (fun i=> show Poly.price w (f' i) ≤ _ from by rw [show f' i=Poly.send _ _ from rfl,Poly.solo]; exact mul_le_mul_of_nonneg_left (Hf.always _ _) (Poly.worth hw _).le)).1
  unfold Feed.text; simp_rw [if_pos (hZ _)]
  rw [hS.tsum_prod (f:=f'),tsum_fintype]
  unfold f' tonic jointFeed; unfold Feed.mode; simp_rw [show ∀ z j, Feed.hot ((feeds z (e.scribe d) H (L z) (hr z|>.sound.anchored)).column j).2 from fun i j=>R.fire_hot i,if_true]

-- compare ray differences: only ONE of the singleton summands moved every old ray
local notation "q"=> sprayed e H L d
variable (i:V)
private abbrev one := Primary.dress i (e.scribe d) H (L i)
private abbrev dawn (U:Config G n)(i:ℕ):= (e.scribe d).contents.ray i U
private abbrev rk (U:Config G n)(i:ℕ):=Poly.send (e.pins i) (masked P.p.threshold (e.tent L d i) (e.display H L d i) U)
private abbrev ik (U:Config G n):=(one (d:=d) (e:=e) (H:=H) (L:=L) i).contents.ray 0 U
-- abbreviations order?
omit hr hz he h hl hw in
private lemma ferries (U:Config G n)(j:ℕ):
    dawn (d:=d) (e:=e) U j - rk (L:=L) (d:=d) (e:=e) (H:=H) U j=∑ i : V,(dawn (d:=d) (e:=e) U j-(one (d:=d) (H:=H) (L:=L) (e:=e) i).contents.ray (j+1) U):=by
  have hi i(hh : ¬e.only j i): dawn (d:=d) (e:=e) U j=(one (d:=d) (L:=L) (H:=H) (e:=e) i).contents.ray (j+1) U:= by
    unfold dawn one dress Bands.ray tagR; simp only; unfold Primary.copying Primary.sales Primary.grows Primary.fires
    change earns i (e.scribe d) j → False at hh; change _= Poly.send _ (masked _ (if earns i (e.scribe d) j then _ else _) (if earns i (e.scribe d) j then _ else _) _); rw [if_neg hh,if_neg hh]
  cases hp:e.shaft j with
  | none=>
    have ht : dawn (d:=d) (e:=e) U j=rk (L:=L) (d:=d) (e:=e) (H:=H) U j:= by unfold dawn rk; rw [(grass H hp (L:=L) (d:=d)).1,(grass H hp).2];rfl
    have he (i:V):_ =(0:Poly R):= sub_eq_zero.mpr (hi i (e.nobody hp _))
    simp_rw [← ht,sub_self,he,sum_const_zero]
  | some s=>
    have hh := from_shaft e hp
    have hr i (he:i≠s): ¬e.only j i:=fun hu=>he (Option.some.inj ((e.shaft_only hu).symm.trans hp))
    rw [Finset.sum_eq_single s (fun i _ hE=> sub_eq_zero.mpr (hi i (hr i hE))) (by simp)]
    unfold rk one dress; rw [(blossom H hp (L:=L) (d:=d)).1,(blossom H hp).2]; rfl

-- full header identity after all spray (K handled once!)
variable {f:ℕ→ℝ}{u v Y : ℝ}(hb:e.Grant P.p w a u v Y f)
include hb
lemma blowing {M : ℕ} [Nonempty V](hO : Occupancy ζ M) (ha : P.p.supportExponent+1+1 ≤ a) {K:ℝ} (hK:∀ i,expense P.p.B a ((L i).footprint (ζ i)) (k i) ≤ K)
    {iu iv ik ib id' : ℝ}(hq:d.Budget w iu iv ik ib id'):
    Join P.p (e.log P.p) ((q).log P.p) w ζ (F) (bracken d e k H X m) (M*siteFactor P.p.B*δ):= by
  let t:=e.scribe d
  have hg : P.p.supportExponent+1≤a:=by linarith
  have hy := stored hr hz he h hl hw hb hg hK
  obtain ⟨HK,Hf,HM,hi⟩:= restore hr hz he h hl hw hO ha (budget_nonneg (hl.2 (Classical.arbitrary V)))
  have ht:= living hw (primed H hr hz he h) hy (p:=P.p) (by linarith)
  have hQ:= living hw h hb (p:=P.p) (by linarith)
  refine ⟨HK,Hf,HM,fun U=>?_⟩
  let T:=q
  let hand (s:V):=one (L:=L) (d:=d) (H:=H) (e:=e) s
  let g (i:V):=(T.pure i)-e.pure i
  let μ:=dawn (e:=e) (d:=d) U; let r:=rk (e:=e) (d:=d) (H:=H) (L:=L) U
  let m0 (i:V) (j:ℕ):=(hand i).contents.ray j U
  let W i:=(jointFeed i d e L H hr).text U
  let Y0 (i:V):=Poly.send (R.fire i) (petition (X:=X) e H d i 0)
  have hμ : Summable μ:= (hQ U).1
  have hG:= funds hb (show P.p.supportExponent ≤ a from by linarith) hq -- unknown p argument
  have hA:= authorized hz h he
  have hm i:Summable (m0 i):= by -- using .log_bounds
    have hx:StemPay i t H (L i) (k i) w m δ:=demand hr hl hw hg i
    have hy:= hx.log_bounds hw (hr i) hA hG; dsimp only at hy
    let Z:=read P (hand i) ζ
    have hZ:Z.Principle P.p:=by
      have hf:=Primary.colored i t H (L i) (hr i) hA
      exact ⟨hf.rays,hf.home,hf.regular,h.vertical⟩
    obtain ⟨g,hg,hfg⟩:= hy.bulk
    have hF: Z.Grant P.p w P.p.supportExponent (u+δ) (v+δ+w i*P.p.mass ((L i).footprint (ζ i)) (stageCost k w δ i)) Y g:= by
      refine ⟨hy.allowance, fun i=>(hg i).1,fun i=>(hg i).2,hfg, label_budget hw (fun _=>norm_nonneg _) (show P.p.supportExponent ≤ a from by linarith) hb.captions⟩
    exact (living hw hZ hF (p:=P.p) le_rfl U).1
  have hr' : Summable r:=by
    have hy : Injective (fun i:ℕ=>(numbering (V⊕ℕ)).symm (Sum.inr i)):= (numbering (V⊕ℕ)).symm.injective.comp Sum.inr_injective
    convert (ht U).1.comp_injective hy using 1
    any_goals rfl
    funext i; simp only [comp_apply,sprayed,birth,shuffle,Equiv.apply_symm_apply,Sum.elim_inr]; rfl
  have hN i:= funded i t H (L i) (hr i) hA hG (demand hr hl hw hg i)
  have hd i : (tsum μ)=(tsum fun j : ℕ=>m0 i (j+1))+Y0 i + m0 i 0+ W i:= by
    have hc:= (hN i).log U
    have hu : (∑ j:V, Poly.send (R.fire j) ((hand i).contents.units j))=(∑ j,Poly.send (R.fire j) (t.contents.units j))+Y0 i:= by
      change ∑ j:V, Poly.send (R.fire j) (_ + if j=i then _ else _) =_
      have hi (m:R.Mode)(x y:ℂ): Poly.send m (x+y)= Poly.send m x+Poly.send m y:=by ext; simp only [Poly.part_plus,Poly.part_send];split <;> simp
      simp_rw [hi,sum_add_distrib]; congr 1
      rw [Finset.sum_eq_single i (fun j _ hj=>by rw [if_neg hj]; exact Poly.send_zero _) (by simp),if_pos rfl]; rfl
    change _+tsum μ +_= (∑ j,Poly.send (R.fire j) ((hand i).contents.units j))+tsum (m0 i)+t.captions.chord+W i at hc
    have he: tsum (m0 i)=m0 i 0+∑' j:ℕ, m0 i (j+1):= by simpa only [Finset.sum_range_one] using (hm i).sum_add_tsum_nat_add 1|>.symm
    rw [hu,he] at hc
    let LBB:= (∑ j,Poly.send (R.fire j) (t.contents.units j))
    exact add_left_cancel (a:= LBB+t.captions.chord) (calc
      _= LBB+tsum μ+t.captions.chord:=by abel
      _= _:=hc.trans (by abel))
  have h' : tsum μ-tsum r=∑ i,(m0 i 0+Y0 i + W i):= by
    have hl i : Summable (fun j=>μ j -m0 i (j+1)):= hμ.sub ((summable_nat_add_iff 1).2 (hm i))
    rw [← hμ.tsum_sub hr', show (fun i=> μ i-r i)=(fun j=> ∑ i:V,(μ j-m0 i (j+1))) from funext (fun j=> ferries U j), Summable.tsum_finsetSum (f:=fun i j=> μ j-m0 i (j+1)) (fun i _=> hl i)]
    refine Finset.sum_congr rfl fun i _=>?_ ; rw [hμ.tsum_sub ((summable_nat_add_iff 1).2 (hm i)),hd i]; abel
  have hfy : (∑' i,T.birth P.p i U)=(∑ i:V, m0 i 0)+tsum r := by
    let g:=Sum.elim (fun i=> m0 i 0) r
    have hu:Summable (fun i=>m0 i 0):=(hasSum_fintype _).summable
    have he:(∑' i,shuffle (fun i=>m0 i 0) r i)=∑' i,g i:= (numbering _).tsum_eq g
    rw [show (fun i=>T.birth P.p i U)=shuffle (fun i=>m0 i 0) r from ?_,he,Summable.tsum_sum (f:=g) hu hr',tsum_fintype]; swap
    · funext i; cases hh:numbering (V⊕ℕ) i with
      | inl j=> simp only [T,sprayed,birth,shuffle,comp_apply,hh,Sum.elim_inl]; rfl
      | inr j=> simp only [T,sprayed,birth,shuffle,comp_apply,hh,Sum.elim_inr]; rfl
    rfl
  have hUs i : Poly.send (R.fire i) (T.pure i)= Poly.send (R.fire i) (e.pure i)+Y0 i := by
    ext; simp only [T,sprayed,Y0,Poly.part_plus,Poly.part_send]; split <;> simp
  change e.log P.p U = T.log _ _+_
  unfold log; simp_rw [hfy,hUs,Finset.sum_add_distrib]; rw [hi U]; change _+tsum μ+_= _
  rw [sub_eq_iff_eq_add.mp h']; simp_rw [Finset.sum_add_distrib]; unfold W T Y0; abel
end YM.RG3.Script.Edition
