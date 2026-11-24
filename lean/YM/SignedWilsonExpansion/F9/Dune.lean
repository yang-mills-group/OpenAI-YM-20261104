import YM.SignedWilsonExpansion.F9.Stair
/-!
# F9 pricing our analytic epochs -- actual common-step clocks billed across a trimmed Course

A visit `PadRank` together with its additional exact relative calendar.Arc need not bounded
uniformly without paying scatter.Fences. On `y`,`y.Age`, can substitute with polynomial prices.
Epoch costs occur in F9 with virtual regulator, so require cross-month accounting rather than
uniformly post-hoc along each regulator only. See `Ferry` for same columns at the encounter.
-/
set_option autoImplicit false
set_option maxHeartbeats 670000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{e m c N i j :ℕ}
variable {B Z Y η t a:ℝ}{E W U:Credit}
local notation "Fz" => PowerSeries.X
structure Canopy (R: Realm G e E)(m c:ℕ)(Z:ℝ): Prop where
   arch : R.anchor≤m
   order : m ≤ c
   pad : PadRank R m c Z
   span : R.draws.S.scale c-R.draws.S.scale m ≤ Z
section
variable {R:Realm G e E}(Q:Canopy R m c Z)
include Q
lemma Canopy.cut (u:m ≤ i)(v:i≤ j)(p:j≤c): Canopy R i j Z:=⟨Q.arch.trans u,v,⟨fun i p' t=>Q.pad.year _ (u.trans p') (t.trans p), (show ((j-i:ℕ):ℝ)≤(c-m:ℕ) by exact_mod_cast (show j-i ≤ c-m by omega)).trans Q.pad.lengthS⟩,(sub_le_sub (scales R.draws.S p) (scales R.draws.S u)).trans Q.span⟩
lemma Canopy.positive : 1≤ Z:=(R.depth m Q.arch).trans (Q.pad.year m le_rfl Q.order)
lemma Canopy.older (V:Credit)(p:m≤ i)(t:i≤ c): R.cash V i≤ V.buy Z:= V.elder (R.depth _ (Q.arch.trans p)) (Q.pad.year i p t)
lemma Canopy.WindowSize (u:c≤N) : (@WindowS.Age _ _ _ (⟨R,m,c-m,N,N,c,Q.arch,(by have:=Q.order;omega),u,u⟩:WindowS G e E))≤3*Z:=by
   have hv:=Q.order; change R.y m+(R.draws.S.scale (m+(c-m))-R.draws.S.scale m)+((c-m:ℕ):ℝ)≤ _; rw [Nat.add_sub_of_le hv]; linarith only [Q.pad.year m le_rfl hv,Q.pad.lengthS,Q.span]
lemma Canopy.bare : Escort R m c (fun _=>0):=⟨Q.arch,Q.order,fun _ _ _=>le_rfl,fun _ _ _=>zero_le_one, fun i _ _=>by unfold thinLevel; simp⟩ -- Φ integer covariance weight chosen 0, pay high moments on local arrival V.
omit Q
lemma Canopy.advance (p:R.anchor≤ m)(v:m≤ c)(a:R.y m≤Z)(w:R.draws.S.scale c-R.draws.S.scale m≤ Z) : Canopy R m c (3*Z):=by
   have hz : 1≤Z:= (R.depth _ p).trans a; have he : ((c-m:ℕ):ℝ)≤Z:= (winterH R.draws.S v).trans w
   refine ⟨p,v,?_ ,by linarith⟩; refine ⟨fun i t g=>?_ ,by linarith⟩
   linarith only [R.age m i p t,a,w,hz,scales R.draws.S g]
end
-- clock dialects, coarse-to-fine means coarser pulled to fine.Cup.Clock θ
noncomputable abbrev toward (A:Levels G)(Ñ:ChartRatio G)(N m c:ℕ):Cost→+*Cost:= Bank.reel (relativeF A Ñ N m (c-m))
noncomputable abbrev rear (A:Levels G)(Ñ:ChartRatio G)(N m c:ℕ):Cost→+*Cost:= Bank.reel (relativeC A Ñ N m (c-m))
section dial
variable (x:Cost)(h:m≤c)(g:G.Simple)(p:LocalRatio Ñ)(v:c ≤ N)
include h g p v
lemma toward_rear : toward A Ñ N m c (rear A Ñ N m c x)=x:=by
    unfold rear toward
    rw [← RingHom.comp_apply, reel_chart,(direction g p (show m+(c-m)≤N by omega)).2, reel_one]
lemma rear_toward : rear A Ñ N m c (toward A Ñ N m c x)=x:=by
    unfold rear toward; rw [← RingHom.comp_apply,reel_chart,(direction g p (show m+(c-m)≤N by omega)).1,reel_one]
lemma rear_head : constantCoeff (rear A Ñ N m c (Fz:Cost))=0 ∧ coeff 1 (rear A Ñ N m c Fz)=1:=by unfold rear; rw [reel_X]; constructor; simp; exact (coeff_succ_mul_X 0 (relativeC A Ñ N m (c-m))).trans ((coeff_zero_eq_constantCoeff_apply _).trans (angularC g p (by omega)))
lemma toward_head : constantCoeff (toward A Ñ N m c (Fz:Cost))=0 ∧ coeff 1 (toward A Ñ N m c Fz)=1:=by unfold toward; rw [reel_X]; constructor; simp; exact (coeff_succ_mul_X 0 (relativeF A Ñ N m (c-m))).trans ((coeff_zero_eq_constantCoeff_apply _).trans (angularF g p (by omega)))
omit h g p v in
lemma toward_join (x:Cost) (A:Levels G)(Ñ:ChartRatio G)(p:m≤ i)(t:i≤c): toward A Ñ N m c x=toward A Ñ N m i (toward A Ñ N i c x):=by unfold toward; rw [← RingHom.comp_apply,reel_chart,show c-m=i-m+(c-i) by omega,stageF,Nat.add_sub_of_le p]
omit h g p v in
lemma rear_join (x:Cost) (A:Levels G)(Ñ:ChartRatio G)(p:m≤ i)(t:i≤c): rear A Ñ N m c x=rear A Ñ N i c (rear A Ñ N m i x):=by unfold rear; rw [← RingHom.comp_apply,reel_chart,show c-m=i-m+(c-i) by omega,stageC,Nat.add_sub_of_le p]
omit h g p v in
lemma toward_next (A:Levels G)(Ñ:ChartRatio G)(x:Cost) : toward A Ñ N m (m+1) x= Bank.reel (ratioHigh A Ñ N m) x:=by unfold toward relativeF; simp only [Nat.add_sub_cancel_left, palmB, chart_one,Nat.add_zero]
end dial
-- pricing coeff calculations.Style symmetric slots.
abbrev FitS (e:ℕ)(x:Cost)(z:ℝ):Prop:= ∀ i, i≤e→ ‖coeff i x‖≤z
variable {u:ℕ}{x y:Cost}
lemma FitS.nn (p:FitS e x Z): 0≤ Z:= (norm_nonneg _).trans (p 0 (Nat.zero_le _))
lemma FitS.more (p:FitS e x Z){Q:ℝ}(q:Z≤Q): FitS e x Q:=fun i h=>(p i h).trans q
lemma FitS.plus (p:FitS e x B)(q:FitS e y Z):FitS e (x+y) (B+Z):=by intro i h; rw [map_add]; exact (norm_add_le ..).trans (add_le_add (p i h) (q i h))
lemma FitS.minus (p:FitS e x B)(q:FitS e y Z):FitS e (x-y) (B+Z):=by intro i h; rw [map_sub]; exact (norm_sub_le ..).trans (add_le_add (p i h) (q i h))
lemma FitS.inverse (p:FitS e x B): FitS e (-x) B:=by intro i h; rw [map_neg,norm_neg];exact p i h
lemma FitS.product (p:FitS e x B)(q:FitS e y Z):FitS e (x*y) ((e+1:ℕ)*(B*Z)):=by
   intro i h; rw [coeff_mul]; let S:= Finset.antidiagonal i; refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun _=> B*Z) (s:=S) fun j hj=> ?_) ?_)
   · have hv:= Finset.mem_antidiagonal.mp hj; rw [norm_mul]; exact mul_le_mul (p j.1 (by omega)) (q j.2 (by omega)) (norm_nonneg _) p.nn
   rw [Finset.sum_const,nsmul_eq_mul,Finset.Nat.card_antidiagonal]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (mul_nonneg p.nn q.nn)
lemma FitS.spray (p:FitS e x B):FitS e (a • x) (|a| * B):=by intro i h; rw [map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (p i h) (abs_nonneg a)
lemma FitS.zero : FitS e 0 0:=by simp [FitS]
lemma FitS.C (a:ℝ) : FitS e (PowerSeries.C a) |a|:=by intro i _; rw [coeff_C]; split; exact le_rfl; simp
lemma FitS.X : FitS e Fz 1:=by intro i _; rw [coeff_X]; split; simp; simp
lemma FitS.pow (p:FitS e x B)(i:ℕ): FitS e (x^i) ((((e+1:ℕ):ℝ)*B)^i):=by
   induction i with
   | zero=> rw [pow_zero,pow_zero]; exact (show FitS e 1 1 by simpa only [map_one,abs_one] using FitS.C (e:=e) 1)
   | succ i ih=> rw [pow_succ,pow_succ]; exact (ih.product p).more (le_of_eq (by ring))
lemma FitS.ringClock (p:FitS e x B)(q:FitS e y Z)(h:1≤ B): FitS e (Bank.reel x y) ((e+1:ℕ)*(Z*(((e+1:ℕ):ℝ)*B)^e)):=by
   intro i hi; rw [reelQuote]; let S:=Finset.range (i+1); let Q:=Z*(((e+1:ℕ):ℝ)*B)^e
   refine (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (g:=fun _=> Q) (s:=S) fun j hj=> ?_) ?_)
   · have v:= Finset.mem_range.mp hj; let t:=(((e+1:ℕ):ℝ)*B); have hx:1≤t:= one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (by omega)) h
     rw [norm_mul]; exact mul_le_mul (q j (by omega)) (((p.pow j) (i-j) (by omega)).trans (pow_le_pow_right₀ hx (by omega))) (norm_nonneg _) q.nn
   rw [Finset.sum_const,nsmul_eq_mul,Finset.card_range]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) (by unfold Q; have hz:=q.nn; have he:0≤B:=p.nn; positivity)

abbrev orbitMark (I:WindowS G e E) (b:Bool):= if b then relativeF I.robe.draws I.robe.paid I.n I.base I.span else relativeC I.robe.draws I.robe.paid I.n I.base I.span
def storm (G:Gauge)(e i:ℕ)(E:Credit)(b:Bool)(U:Credit): Prop:= ∀ I:WindowS G e E, ‖coeff i (orbitMark I b)‖≤ U.buy I.Age
lemma stormHigh (G:Gauge)(e i:ℕ)(E:Credit)(b:Bool)(h:i≤ e): ∃ C:Credit, storm G e i E b C:=by
   let Y(I:WindowS G e E):= ({ I with N:=I.n, n:=I.N,hd:=I.hg,hg:=I.hd }: WindowS G e E)
   let P(i:WindowS G e E):= orbitMark i b
   have he: Weft WindowS.Age WindowS.cab P (fun i=> orbitMark (Y i) b) i:=by cases b; exact Bank.descend G e i E h; exact Bank.ascend G e i E h
   rcases he with ⟨w,f,hf,H⟩; refine ⟨⟨w,1+f,by linarith⟩,fun T=>?_⟩; refine (H T).main.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (pow_nonneg (zero_le_one.trans T.warm) w))
lemma stormCourse (G:Gauge)(e:ℕ)(E:Credit):∃ C:Credit,∀ (I:WindowS G e E)(b:Bool),FitS e (orbitMark I b) (C.buy I.Age):=by
   let t:= (Fin (e+1)) × Bool; obtain ⟨W,w⟩:= uniformPays (P:=fun (i:t) V=>storm G e i.1.val E i.2 V) Finset.univ (fun i _=> stormHigh G e i.1 E i.2 (Nat.le_of_lt_succ i.1.isLt)) (fun _ _ _ _ v p j=> (p j).trans (v _ j.warm)); exact ⟨W,fun I b i h=>w ((⟨i,by omega⟩:_),b) (Finset.mem_univ _) I⟩
def StormC (G:Gauge)(e:ℕ)(E:Credit):= (stormCourse G e E).choose.usingC ⟨1,3,by norm_num⟩
namespace Canopy
variable {R: Realm G e E}(g:Canopy R m c Z)
include g
lemma study (w:c≤N) : FitS e (relativeF R.draws R.paid N m (c-m)) ((StormC G e E).buy Z) ∧ FitS e (relativeC R.draws R.paid N m (c-m)) ((StormC G e E).buy Z):=by
   let L:=WindowS.mk R m (c-m) N N c g.arch (by have:=g.order;omega) w w
   have ht b:= (stormCourse G e E).choose_spec L b; unfold StormC; rw [Credit.stock_up, show Credit.buy ⟨1,3,by norm_num⟩ Z=3*Z from by rw [Credit.buy,pow_one]]; have hZ:= Credit.elder (stormCourse G e E).choose L.warm (g.WindowSize w)
   exact ⟨(ht true).more hZ,(ht false).more hZ⟩
omit g in
def pageS (G:Gauge)(e:ℕ)(E:Credit):= let B : Credit:=⟨0,((e+1:ℕ):ℝ),Nat.one_le_cast.mpr (by omega)⟩; (B.prodC ((B.prodC (StormC G e E)).powC e))
lemma direction_cost {t':ℕ} (q:c≤ N)(h:FitS t' x a)(u:t'≤ e): FitS t' (toward R.draws R.paid N m c x) ((pageS G e E).buy Z*a) ∧ FitS t' (rear R.draws R.paid N m c x) ((pageS G e E).buy Z*a):=by
   let f:= (StormC G e E).buy Z; have hb:1≤ f:= Credit.purchase _ g.positive; let w:=(((e+1:ℕ):ℝ)*f); have hw:1≤ w:=one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr (by omega)) hb
   have he : (((t'+1:ℕ):ℝ)*(a*(((t'+1:ℕ):ℝ)*f)^t')) ≤ (pageS G e E).buy Z*a:=by
       have hp:((t'+1:ℕ):ℝ)≤(e+1:ℕ):=by exact_mod_cast (show t'+1≤e+1 by omega)
       have hv:0≤f:=zero_le_one.trans hb; have ha:=h.nn
       have h0:(((t'+1:ℕ):ℝ)*f)^t'≤ w^e:= (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hp hv) _).trans (pow_le_pow_right₀ hw u)
       refine (mul_le_mul hp (mul_le_mul_of_nonneg_left h0 ha) (by positivity) (by positivity)).trans_eq ?_; unfold pageS; rw [Credit.products, Credit.power,Credit.products]; change _= (↑(e+1)*Z^0*((↑(e+1)*Z^0)*f)^e)*a; unfold w; push_cast; ring
   obtain ⟨wQ,wR⟩:= g.study q
   exact ⟨(FitS.ringClock (fun i (v:i≤t')=> wQ i (v.trans u)) h hb).more he,(FitS.ringClock (fun i (v:i≤t')=>wR i (v.trans u)) h hb).more he⟩
end Canopy
end YM.WilsonCoeffUV.Mer.Xa
