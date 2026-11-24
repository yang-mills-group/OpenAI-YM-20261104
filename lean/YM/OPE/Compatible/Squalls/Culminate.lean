import YM.OPE.Compatible.Squalls.Crane
/-! # Vol Principal poll exact hyper. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics WardBin
open scoped Topology BigOperators Classical ContDiff
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s s' b b' U U' D:ℝ}
namespace Script
open Page
lemma polis (P:(r:ℕ)→Script (Shade G) r)(k d:ℕ)(hs:k≤d)(h:(P k).sorted)(hg:∀ m,∃ c,soot m (P k) c)(hv:∀ (x:Fin k→fieldX (Shade G))(Y:Fin k→ℕ),radiantX x Y→∀ v :ℕ,v≤d→summitX P x Y v=0): Bells (P k) (d+1-k):=by
     intro a l hl; let v i:= tasteE l i; let D(i:Fin k):=(v i).length; choose pX Hp using fun i=> clad (a i) (v i); let V i:= ledge (pX i)
     have hu(i:Bin k)(t:Ink (Shade G) k):wordX V (syn i t)= if t=a then tasting l (translit i) else 0:=by
         split
         next h => subst t; rw [topping]; unfold V wordX; refine prod_congr rfl fun j _=>?_ ; change ledge (pX _) ((stepOut i j),a j)=_; rw [Hp,if_pos rfl]; rfl
         next h => obtain ⟨j,hj⟩:=not_forall.mp (show ¬ ∀ j,t j=a j from fun g=>h (funext g)); exact prod_eq_zero (mem_univ j) (by change ledge (pX _) ((stepOut i j),t j)=_; rw [Hp,if_neg hj])
     let e:Ink (Shade G) k × Bin k≃Page (Shade G) k:= Equiv.trans (Equiv.prodComm ..) (blurb ..); let p:=P k
     have he: wholeX p V=well (sliceP p a) (tasting l):=by
         let f(i):= p i*wordX V i; have hS: Summable (f ∘ e):= e.summable_iff.mpr (wordSum (hg _).choose_spec (fun i:Fin k=> low_quiet (ledgeL (pX i))) le_rfl)
         change (∑' i,f i)=_; rw [← e.tsum_eq f]; change (∑' i,(f ∘ e) i)=_; rw [hS.tsum_prod,tsum_eq_single a]
         · refine tsum_congr fun i=>?_; change p (syn i a)*wordX V (syn i a)=_; rw [hu,if_pos rfl];rfl
         intro b h; simp_rw [show ∀ i:Bin k,(f ∘ e) (b,i)=0 from fun i=> by change _*wordX V (syn i b)=0;rw [hu,if_neg h,mul_zero],tsum_zero]
     have hm:(∑ i, (D i+1))=l.length+k:=by rw [sum_add_distrib,(show ∑ i,D i=l.length from tram l)]; simp
     exact he.symm.trans (plazaOne _ _ D (fun i=> ledgeL (pX i)) hm h fun x hu=> hv x _ hu _ (by omega))
lemma Poll_income {p:Script W (r+1)} (h:Bells p d)(hx:soot m p U)(hp:d≤m):Poll (silt p) d:=by
    intro i l hl; rw [show crop (silt p) i=midland (sliceP p i) from funext fun j=>by unfold crop; rw [from_rows,upland,header,if_pos rfl,flattenZ],mid_price (slices hx i) _ (hl.le.trans hp)]; exact wells (h _) (charm_flavor _ (fall_charm l)) hl (hl.le.trans hp) (slices hx _)
variable {R T:PathData G}{p q: Clip}
abbrev polyV (R:PathData G)(p:Clip)(m:ℕ):= silt (oathX R p m)
abbrev trailV (R:PathData G)(m:ℕ):= silt (oathY R m)
lemma silt_sub {p q:Script W n}(h:Summable p)(hv:Summable q):silt (p-q)=silt p-silt q:=by
    rw [sub_eq_add_neg,silt_add (q:=-q) h hv.neg,show -q=(-1:ℝ) • q by simp,silt_scale,neg_smul,one_smul,sub_eq_add_neg]
lemma mercy (h:R.Bounds p s b U)(hk:T.Bounds q s' b' U')(hn:n ≤3): Poll (polyV R p (n+1)-polyV T q (n+1)) (4-n):=by
    let A(r):=oathX R p r; let B(r):=oathX T q r; let Z(r):=A r-B r
    have he(i m): ∃ c,Earn i m (oathV R p) (A i) c:=by obtain ⟨c,hg⟩:= oath_earn G p s b h.width i m; exact ⟨c,hg R U h⟩
    have hF(i m): ∃ c,Earn i m (oathV T q) (B i) c:=by obtain ⟨c,hg⟩:= oath_earn G q s' b' hk.width i m; exact ⟨c,hg T U' hk⟩
    have hs(i): (Z i).sorted:=fun j=>congr_arg₂ (fun u v:Script (Shade G) i=> u-v) ((he i 0).choose_spec.tandem j) ((hF i 0).choose_spec.tandem j)
    have hg(i m): ∃ c,soot m (Z i) c:= ⟨_,Sack.subsumes (he i m).choose_spec.credit (hF i m).choose_spec.credit (fun i=> zero_le_one.trans (payer m _))⟩
    have hh(i) (hx:i ≤ 4): Bells (Z i) (5-i):= polis Z i 4 hx (hs i) (hg i) (fun x Y hY v hx=> by
        rw [show Z=(A+ (-1:ℝ) • B) from by unfold Z; rw [neg_smul,one_smul]; rfl -- not def
          , keyAdd A ((-1:ℝ) • B) _ _ _ (fun i=>low_quiet (hY i)) (fun i m=> ⟨_,(he i m).choose_spec.credit⟩) (fun i m=> ⟨_,((hF i m).choose_spec.credit.scale_line (-1:ℝ))⟩), keyScale]; unfold A B; rw [vatic h hY hx,vatic hk hY hx,neg_one_mul,add_neg_cancel])
    unfold polyV; rw [← silt_sub (safeEarn (he _ 0).choose_spec) (safeEarn (hF _ 0).choose_spec),← show 5-(n+1)= 4-n from by omega]; exact Poll_income (hh _ (by omega)) (hg (n+1) 5).choose_spec (by omega)
lemma mercyL (h:R.Bounds p s b U)(hn:n ≤3): Poll (trailV R (n+1)) (4-n):=by
    have hg(i m):∃ c,Earn i m (oathL R) (oathY R i) c:=by obtain ⟨c,hc⟩:=oathLoop G s h.width i m; exact ⟨_,hc p R b U h⟩
    rw [← show 4+1-(n+1)=4-n by omega]; exact Poll_income (polis (oathY R) (n+1) 4 (by omega) (hg _ 0).choose_spec.tandem (fun m=>⟨_,(hg _ m).choose_spec.credit⟩) (fun _ _ he _ hp=>vatic_zero h he hp)) (hg _ 5).choose_spec.credit (by omega) -- rfl
end Script
end YM.OPE.Flume
