import YM.OPE.Compatible.Squalls.Air
/-! # Startup universal top. No POL sift yet -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Planned.PrimaryIntegral295.Carrier Asymptotics WardBin
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J W E X:Type*}{i j n r d m:ℕ}{G:Gauge}{s b U D:ℝ}
namespace Script
open Page
variable [Fintype I]{x:I→fieldX (Shade G)} {k:I→ℕ}{R:PathData G}{p:Clip}
lemma sunrise (h:radiantX x k) (z:PlaqAxes) (r:Signed) (hm:m ≤4): summitX (cardingF G z r) x k m = if m=4 then ‖CurlX x k r z‖^2/2 else 0:=by
    have he:= (accompaniment (ledgerF z r G 1) (fun _ _=>litD z r) zero_lt_one (lumenD G) x k (fun i=>low_quiet (h i)) m).tsum_eq; unfold cardingF; rw [← he,tsum_fintype]; convert! priceShot h z r hm using 1; simp
-- row δ coefficient. candidate vector Σ *
abbrev reachesQ (R:PathData G)(u:PlaqAxes→G.Color)(p:PlaqAxes):=∑ i,R.symbol0 p i • u i
lemma duet_summed (h:R.Bounds p s b U)(z:PlaqAxes)(u:PlaqAxes→G.Color) (i:G.ColorIndex) : (∑' j,FareU R z j * (u (Claw R z j).plaq) i) = reachesQ R u z i:=by
    let F(a:PlaqAxes):=R.symbol0 z a*u a i; have ht:reachesQ R u z i= ∑ a,F a:=by change chin i (∑ a: PlaqAxes,R.symbol0 z a • u a)=_; rw [map_sum]; exact sum_congr rfl fun a _=> map_smul ..
    have he(a:PlaqAxes): F a=∑' j,if (Claw R z j).plaq=a then FareU R z j*u a i else 0:=by
       unfold F PathData.symbol0; rw [← tsum_mul_right]; refine tsum_congr fun j=> ?_; by_cases he:(Claw R z j).plaq=a
       · simp only [if_pos he] -- likely simp didn't match
       erw [if_neg he,if_neg he, zero_mul]
    rw [ht]; simp_rw [he]; rw [← Summable.tsum_finsetSum]; swap
    · intro j _; have hh:= (h.symTerms z j).mul_right (u j i); apply hh.congr; intro n; change (if (Claw R z n).plaq=j then FareU R z n else 0)*_=_; split; rfl;simp
    apply tsum_congr; intro j; rw [Finset.sum_ite_eq];simp
lemma cloud_pair (h:R.Bounds p s b U)(he:radiantX x k)(w:Signed)(z:PlaqAxes)(i:G.ColorIndex)(hx:m ≤ 4): summitX (twin R w z i) x k m= if m=4 then (reachesQ R (CurlX x k w) z i)^2 else 0:=by
    have H:= accompaniment (duet_cost h w z i) (duet_funds R w z i) (div_pos h.width (by norm_num)) (lumenD G) x k (fun i=>low_quiet (he i)) m; unfold twin; rw [← H.tsum_eq,H.summable.tsum_prod]; simp_rw [twinShot he R z _ _ i w hx] -- fix args
    split
    next h' =>
       let u:=CurlX x k w; let f(i':ℕ):=FareU R z i'*u (Claw R z i').plaq i
       have he(a b:ℕ): penny R z (a,b)*(CurlX x k w (Claw R z a).plaq i * CurlX x k w (Claw R z b).plaq i)= f a * f b:= mul_mul_mul_comm ..; simp_rw [he,tsum_mul_left,tsum_mul_right]; change (∑' i,f i) * (∑' i, f i)=(reachesQ R u z i)^2; rw [← duet_summed h z u]; ring -- f

    next h' => simp
lemma shoulder {A:I→fieldX W} (T:J→(r:ℕ)→Script W r)(s:Finset J)(a:I→ℕ)(x:ℕ)(h:∀ i,Quiet (A i) (a i))(hv:∀ t∈s,∀ i m,∃ z,soot m (T t i) z): summitX (∑ i∈s,T i) A a x=∑ i∈s,summitX (T i) A a x:=by
    induction s using Finset.induction_on with
    | empty=> simp [summitX,slopeX,wholeX]
    | insert i s hi ih=>
       rw [sum_insert hi,sum_insert hi, keyAdd (T i) (∑ j∈s,T j) _ _ x h (hv i (mem_insert_self ..)) (?_), ih (fun j hj=>hv _ (mem_insert_of_mem hj))]
       intro k m; simp only [Finset.sum_apply]; choose z hz using fun j:s=>hv j.val (mem_insert_of_mem j.property) k m; rw [← Finset.sum_attach s]; exact ⟨_,Sack.finGather _ _ _ (fun j _=> hz j) (fun j=>zero_le_one.trans (payer m j))⟩
lemma gustPair (h:R.Bounds p s b U)(he:radiantX x k)(w:Signed)(z:PlaqAxes)(hy:m≤4): summitX (waistX R p w z) x k m=
   if m=4 then p.direct*(‖CurlX x k w z‖^2/2)+1/2* ‖reachesQ R (CurlX x k w) z‖^2 else 0:=by
    let A:= cardingF G z w; let Z(i:G.ColorIndex):= twin R w z i; let Y:= (∑ j,Z j)
    have ht(d i):∃ c, soot i ((p.direct • A) d) c:=by
       obtain ⟨F,hF,W⟩:=sphereTurns (I:=Unit) G _ 1 (lumenD G) zero_lt_one i d 1; exact ⟨_,Sack.scale_line (W _ _ _ (ledgerF z w G 1) fun i j a=>litD z w a).credit _⟩
    have hp(j:G.ColorIndex)(d i):∃ z, soot i (Z j d) z:=by
       obtain ⟨F,hF,W⟩:=sphereTurns (I:=ℕ×ℕ) G _ (s/2) (lumenD G) (div_pos h.width (by norm_num)) i d 2; exact ⟨_,(W _ _ _ (duet_cost h w z j) (duet_funds R w z j)).credit⟩
    have hg(d i):∃ c, soot i ((((1/2):ℝ) • Y) d) c:=by
       choose c hx using fun j=>hp j d i; unfold Y;rw [Pi.smul_apply, Finset.sum_apply]; exact ⟨_,Sack.scale_line (Sack.finGather _ _ _ (fun j _=>hx j) (fun j=>zero_le_one.trans (payer i j))) _⟩
    rw [show waistX R p w z=p.direct • A+(1/2:ℝ) • ∑ i,Z i from funext (fun d=>by unfold waistX; rw [Pi.add_apply,Pi.smul_apply,Pi.smul_apply,Finset.sum_apply])]; rw [keyAdd _ _ _ k m (fun i=>low_quiet (he i)) ht hg,keyScale,keyScale,shoulder _ _ _ _ (fun i=>low_quiet (he i)) (fun i _=> hp i)]
    unfold Z A; rw [sunrise he z w hy]; split
    next h' => simp_rw [cloud_pair h he w z _ hy, if_pos h']; rw [← real_inner_self_eq_norm_sq,PiLp.inner_apply]; rw [← real_inner_self_eq_norm_sq,PiLp.inner_apply]; simp [pow_two]
    next h' => simp_rw [cloud_pair h he w z _ hy, if_neg h']; simp
end Script
end YM.OPE.Flume
