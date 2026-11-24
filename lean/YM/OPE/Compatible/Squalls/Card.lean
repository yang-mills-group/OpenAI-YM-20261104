import YM.OPE.Compatible.Squalls.Burnish
/-!
# Engineering moment reading universal (off-shell) -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics WardBin
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable [Fintype I]{x:I→fieldX (Shade G)} {k:I→ℕ}{R:PathData G}{p:Clip}
-- full opacity
lemma lofty (h:R.Bounds p s b U)(he:radiantX x k)(w:Signed)(hy:m≤4): summitX (loftX R p w) x k m= if m=4 then (∑ i, ‖CurlX x k w i‖^2)/2 else 0:=by
    let A(z:PlaqAxes):= waistX R p w z; let B:=∑ j:PlaqAxes,A j; let C:= paymentAtoms R.cubic w; let D:=paymentAtoms R.quartic w; have hv : loftX R p w=B + C + D:= by ext1 i; unfold loftX B; rw [Pi.add_apply, Pi.add_apply,Finset.sum_apply]
    have hx(j:PlaqAxes)(i t): ∃ U,soot t (A j i) U:=by obtain ⟨y,hy⟩:=wage_paid G p s b h.width i t; exact ⟨_,hy R U h w j⟩
    have hF(u:I): Quiet (x u) (k u):= low_quiet (he u)
    have hp (i t):∃ U,soot t (B i) U:=by choose y h using fun j:PlaqAxes=>hx j i t; unfold B; rw [Finset.sum_apply]; exact ⟨_,Sack.finGather _ _ _ (fun i _=>h i) (fun i=>zero_le_one.trans (payer t i))⟩
    have hc (i t):∃ U, soot t (C i) U:=by obtain ⟨A,-,H⟩:= emp ℕ G 3 i s t h.width; exact ⟨_, (H w _ _ h.three).credit⟩
    have ho(i t): ∃ U,soot t ((B+C) i) U:= ⟨_,Sack.splits (hp i t).choose_spec (hc ..).choose_spec (fun i=>zero_le_one.trans (payer t i))⟩
    rw [hv,keyAdd (B+C) D _ _ _ hF ho (fun i t=>by obtain ⟨A,-,H⟩:= emp ℕ G 4 i s t h.width; exact ⟨_, (H w _ _ h.four).credit⟩),keyAdd B C _ _ _ hF hp hc,shoulder A _ _ _ hF (fun i _ i' m=> hx i i' m),show summitX C _ _ _=0 from sullen (by decide) h.three h.width he w hy,show summitX D _ _ _=0 from sullen (by decide) h.four h.width he w hy]; unfold A; simp_rw [gustPair h he w _ hy]; split
    next hm=>
       let v:= CurlX x k w; simp only [add_zero,sum_add_distrib,← Finset.mul_sum,← sum_div]; change _+1/2* (∑ z:PlaqAxes, ‖reachesQ R v z‖^2) = _; linarith only [toneSum h.metric v]
    next hm=> simp
lemma vatic (h:R.Bounds p s b U)(he:radiantX x k)(hy:m≤4): summitX (oathX R p) x k m=avgF*∑ w:Signed, if m=4 then (∑ i, ‖CurlX x k w i‖^2)/2 else 0:=by
    rw [show oathX R p=avgF • ∑ i,loftX R p i from funext fun i=>by unfold oathX; rw [Pi.smul_apply,Finset.sum_apply],keyScale,shoulder _ _ _ _ (fun i=>low_quiet (he i)) (fun j _ i m=>by obtain ⟨c,hg⟩:=repute G p s b h.width i m; exact ⟨_,(hg R U h j).credit⟩)]; apply congr_arg; apply Finset.sum_congr rfl; intro i _; exact lofty h he i hy
lemma vatic_zero (h:R.Bounds p s b U)(he:radiantX x k)(hy:m≤4): summitX (oathY R) x k m=0:=by
    rw [show oathY R=avgF • ∑ i,paymentAtoms R.loop i from funext fun i=>by unfold oathY; rw [Pi.smul_apply,Finset.sum_apply],keyScale, shoulder _ _ _ _ (fun i=>low_quiet (he i)) (fun j _ i m=>by obtain ⟨c,-,H⟩:= emp ℕ G 2 i s m h.width; exact ⟨_,(H j R.loop _ h.two).credit⟩)]; simp_rw [singBlank he h hy,sum_const_zero,mul_zero]
end Script
end YM.OPE.Flume
