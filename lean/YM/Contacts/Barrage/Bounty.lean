import YM.Contacts.Barrage.Loan
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
namespace Oasis
variable (e:Oasis G){i n m q:ℕ}{α:Type}{c:ℝ}
theorem cash_n (i:ℕ)(n:ℕ) (h:i≤n): (e.M.H n i).metric.strip (e.T.α (e.J i)) (purse e.T (e.J i)) := strip_mono (e.lamp.rows n i h).2.1 le_rfl (le_max_right ..)
abbrev κ (e:Oasis G)(i: ℕ):= rentCheque e.T (e.J i)
abbrev flag (e:Oasis G)(i:ℕ):=sight e.T (e.J i)
abbrev price (e:Oasis G)(i:ℕ):=purse e.T (e.J i)
lemma matures (i:ℕ):e.J i=e.J (i+1)∨ e.J i=e.J (i+1)-1:= by have hp:e.J i≤e.J (i+1):= e.a.fits.mono (Nat.le_succ i); have ht:e.J (i+1) ≤ e.J i+1:= e.a.fits.stepSlow i; omega
theorem silk (i:ℕ) : 2 * e.flag i≤ e.κ (i+1):= by
   have ht : 4 ≤ e.J (i+1):= e.a.clock.adm _; have he: (e.flag i:ℝ)*3 ≤ e.κ (i+1):= by rcases e.matures i with h|h; rw [flag,h]; apply (shelf_span e.T _).1; unfold κ; rw [show e.J (i+1)=e.J i+1 by omega]; apply (shelf_span e.T (e.J i)).2
   apply NNReal.coe_le_coe.mp; push_cast; linarith only [he, NNReal.coe_nonneg (e.flag i)]
lemma before (i:ℕ):e.flag i≤ e.κ i:= NNReal.coe_le_coe.mp (show (e.flag i:ℝ) ≤ _ from by have hh: (e.flag i:ℝ)*3 ≤ (e.κ i:ℝ):=(shelf_span e.T _).1; linarith only [hh, NNReal.coe_nonneg (e.flag i)])
theorem prescience (i:ℕ) : ((e.flag i):ℝ)/(e.L i).val ≤ e.flag (i+1) := by
   rcases e.matures i with h|h; · rw [flag,h]; exact div_le_self (by positivity) (by exact_mod_cast (show 1 ≤(e.L i).val from (e.L i).property))
   have hm: tint e.T (e.J (i+1)) ≤ (e.L i).val:= e.funded.halo i; unfold tint at hm; have hp:0 < (e.flag (i+1):ℝ):= NNReal.coe_pos.mpr (sight_pos ..); apply (div_le_iff₀ (side_pos _)).mpr; rw [mul_comm]; apply (div_le_iff₀ hp).1; unfold flag; rw [h]; exact (Nat.le_ceil ..).trans ((Nat.cast_le (α:=ℝ)).2 hm)
lemma marched (i:ℕ) (hl: q≥5) (hk:q≤ e.J (i+1)) (h:i<n)(l:List Axis)(ht:l.length ≤3): (advanceC (e.L i) (e.M.towers n i).A0 l).strip (e.κ (i+1):ℝ) (e.price (i+1)/(e.L i).val^(1+l.length:ℕ)):= by -- rhs cast Nat/Real
   apply strip_mono ( ((e.lamp.costs n i h).2.2.2 l (ht.trans (by change 3≤e.J (i+1)-2; omega))).1) le_rfl; gcongr; exact le_max_right ..
lemma bare_a (i:ℕ) (h:i<n) : (e.M.towers n i).A0.strip (e.κ (i+1)) (e.price (i+1)):= by
    refine strip_mono ( ((e.lamp.costs n i h).2.2.2 [] (by simp)).1) le_rfl ?_; have hf:0≤e.price (i+1):= (purse_pos ..).le; apply le_trans (b:= e.price (i+1)/(e.L i).val^(1+List.length ([]:List Axis))) ?_ (div_le_self hf (one_le_pow₀ (by exact_mod_cast (show 1 ≤ (e.L i).val from (e.L i).property)))); gcongr; exact le_max_right ..
lemma portfolio_n (i:ℕ)(n:ℕ) (h:i≤n): (krow (e.M.H n i).metric).strip (e.κ i) (e.Z i) := strip_mono ((kin_bill e.T (e.J i)).choose_spec.2 _ (e.cash_n i _ h)) le_rfl (((e.funded.owns i).need (e.J i) (e.a.fits.mono (Nat.le_succ i))).2)
private def crude (e:Oasis G)(i:ℕ):= (Fintype.card (Breed 1 (TypeFace 1)):ℝ)*(e.Z i+e.Z i)
private lemma crude_price (i:ℕ)(h:i≤n)(he:i ≤ m): Rooted (terrain (e.flag i) (TypeFace 1)) (economy e.a e.M n m i) (e.crude i):= by
    refine arrive_both (R:=portfolio _ _) (a:=_) (strip_minus (e.portfolio_n i n h) (e.portfolio_n i m he)) (add_nonneg (e.z_pos i).le (e.z_pos i).le) ?_; have he: (e.flag i:ℝ)*3 ≤ (e.κ i:ℝ):= (shelf_span e.T _).1; linarith only [he, NNReal.coe_nonneg (e.flag i)] -- arg b?
def logShelf (e:Oasis G)(i:ℕ):= terrain (e.flag i) (TypeFace 1)
private def crudeStep (e:Oasis G)(i:ℕ):ℝ:= let p:= beamPrice (e.flag i) (e.price (i+1)); Fintype.card (Co (e.L i) (TypeFace 1))*p*(Fintype.card (TypeFace 1)*p)
private lemma ageGate (i:ℕ)(h:i<n)(he:i < m)(hp:Rooted (e.logShelf (i+1)) (economy e.a e.M n m (i+1)) c): Rooted (e.logShelf i) (economy e.a e.M n m i) (e.crudeStep i*c):= by
   let A (n:ℕ):=(e.M.H n i); let B(n:ℕ):=(e.M.H n (i+1)); let R(k:ℕ):= (e.M.towers k i).A0; have hR n (hn:i<n): (R n).strip (e.flag i) (e.price (i+1)) := strip_mono (e.bare_a i hn) (by have he:= (NNReal.coe_le_coe.mpr (e.silk i)); push_cast at he; linarith only [NNReal.coe_nonneg (e.flag i), he]) le_rfl
   let f:=e.a.clock.op i; have hv : ((e.flag i):ℝ)/(e.L i).val ≤ e.flag (i+1):= e.prescience i
   let u:= e.price (i+1); have hx:=steadfast (F:=(B n).metric) (M:=(A n).metric) (G:=(B m).metric) (K:=(A m).metric) (L:=e.L i) (released e.lamp h) (released e.lamp he) (released e.lamp h.le) (released e.lamp he.le) (R:=R n) (R':=R m) (side_diverges e.a.S i) f (fun _=>rfl) (fun j P Q hP hQ=> by
      have h' : R n=P:= eq_of_heq hP; have h1 : R m=Q:= eq_of_heq hQ; rw [← h',← h1]; exact ⟨(e.lamp.crossings _ _ j h).trial,(e.lamp.crossings _ _ j he).trial⟩) (fun j=> (e.lamp.all _ _ h j).symmetric.1) (fun j=>(e.lamp.all _ _ h.le j).symmetric.1) hp hv (hR n h) (hR m he) (purse_pos ..).le
   let p:=beamPrice (e.flag i) u; let a:ℝ := Fintype.card (Co (e.L i) (TypeFace 1))*p; let b:ℝ:= Fintype.card (TypeFace 1)*p; have heq (k:Fin 2) : Weirs (access (e.L i) (e.flag i)) (![install (R n),install (R m)] k) a b:= by fin_cases k; exact ledgers (hR n h) (purse_pos ..).le; exact ledgers (hR m he) (purse_pos ..).le
   change Rooted _ (keconomic (A n).metric (A m).metric) ((a*b)*c); rw [hx]; refine all_root hp (influx hv) heq (fun i=> ?_) (mul_nonneg (mul_nonneg (heq 0).left (heq 0).right) hp.cash); letI : DecidableEq (Fin 2):= fun a b=> Classical.propDecidable _; simp only [Finset.prod_const,Finset.card_erase_of_mem (Finset.mem_univ _), card_univ,Fintype.card_fin, Nat.reduceSub,pow_one]; exact (mul_right_comm ..).le
lemma η_le (i n:ℕ)(h:i≤n): e.η i n≤1:= by induction h with|refl=>rw [self_η]|@step m h ih=>unfold η at *; rw [Schedule.scale_succ]; apply le_trans _ ih; apply Real.exp_le_exp.mpr; nlinarith [Real.log_nonneg (show 1 ≤ ((e.a.S.block m).val:ℝ) from (by exact_mod_cast (show 1 ≤ (e.L m).val from (e.L m).property)))] -- binder
lemma earnings (i n:ℕ)(h:i≤n): earn e.a.S i n≤e.η i n := by rw [show earn e.a.S i n= e.η i n * e.η i n from (by unfold earn η; rw [←Real.exp_add]; congr 1; ring)]; apply mul_le_of_le_one_right ((e.η_pos ..).le) (e.η_le i n h)
private def pensionB (e:Oasis G)(i:ℕ)(b:ℝ):Prop:= ∀ n m,i≤ n→ i ≤ m → Rooted (e.logShelf i) (economy e.a e.M n m i) (b*e.η i (min n m))
private lemma matureB (i:ℕ)(h : 5 ≤ e.J (i+1)): pensionB e i (1+e.crude i):= by
   intro n m hn hm; by_cases he:min n m=i; · rw [he,e.self_η,mul_one]; exact (e.crude_price i hn hm).weaken (fun _=>le_rfl) (le_add_of_nonneg_left zero_le_one)
   have ht := e.funded.here.tariff e.M n m i e.lamp h (by omega) (by omega); refine ht.weaken (fun _=> le_rfl) ((e.earnings _ _ (by omega)).trans ?_); exact le_mul_of_one_le_left ((e.η_pos ..).le) (le_add_of_nonneg_right (e.crude_price (m:=m) i hn hm).cash)
private lemma firstB (i:ℕ): ∃ h≥0,pensionB e i h:= by
   obtain ⟨p,hp⟩:= eventually_atTop.mp (e.a.fits.deep.eventually_ge_atTop 5); let q:= max p i; have hf k: 0 ≤ e.crude k:= (e.crude_price k (n:=k) (m:=k) le_rfl le_rfl).cash
   have hb: i ≤ q:= le_max_right ..; induction hb using Nat.decreasingInduction with
   | self=> exact ⟨_, add_nonneg zero_le_one (hf q),e.matureB q (hp (q+1) ((le_max_left ..).trans (Nat.le_succ q)))⟩
   | of_succ k ht ih=>
     obtain ⟨x,hx,hh⟩:= ih; let u:= e.crudeStep k * (x*e.turn k); let f:= max 0 u; have he : 0 ≤ f:= le_max_left ..
     refine ⟨e.crude k+f, add_nonneg (hf _) he,fun n m hn hm=> ?_⟩; by_cases hu : min n m=k; · simp_rw [hu,e.self_η, mul_one]; exact (e.crude_price _ hn hm).weaken (fun _=>le_rfl) (le_add_of_nonneg_right he)
     have ho:= e.ageGate k (n:=n) (by omega) (m:=m) (by omega) (hh n m (by omega) (by omega)); refine ho.weaken (fun _=>le_rfl) ?_; set M:=min n m; rw [η_spin]; refine le_trans (b:=f*e.η k M) (le_trans (b:=u*e.η k M) ?_ (mul_le_mul_of_nonneg_right (le_max_right ..) (e.η_pos ..).le)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hf k)) (e.η_pos ..).le); exact le_of_eq (by unfold u; ring)
lemma pension_bill : e.Permit (fun i x=> ∀ n m,i≤n→i ≤ m→ Row.strip (portfolio (e.M.H n i).metric (e.M.H m i).metric) (e.flag i) (x*e.η i (min n m))) := by
   have hm:=e.fair_z; have hh:= e.a.fits.deep.eventually_ge_atTop 5; obtain ⟨p,hp,hq⟩:= Oasis.permit.exists e (P:=pensionB e) (e.firstB) (fun i=>1+e.crude i) (hh.mono fun i hp=> e.matureB i (hp.trans (e.a.fits.mono (Nat.le_succ i)))) ((e.fair_const 1 zero_le_one).add ((e.fair_const _ (Nat.cast_nonneg _)).mul (hm.add hm)))
   exact ⟨p,hp,fun i n m hn hm=> from_both (hq i n m hn hm)⟩
-- gather stage incident. Width for nonlinear transfer leaf price polynomial-log
open Balance
abbrev haloSpan (i:ℕ): ℝ≥0:= 2*e.ξ i
lemma light_open (i:ℕ): e.haloSpan i≤ gate e.T (e.J (i+1)):= by obtain ⟨t,b,hp,hv,hc,hd,he,hy⟩:= (e.funded.owns i).escape; exact he.trans hv
lemma gateR (i:ℕ): gate e.T (e.J (i+1)) ≤ min (e.flag i/8) (e.flag (i+1)/8):= by
    unfold gate; refine le_min (div_le_div_of_nonneg_right ((min_le_right ..).trans ?_) (by positivity)) (div_le_div_of_nonneg_right ((min_le_right ..).trans (min_le_left ..)) (by positivity)); rcases e.matures i with h|h; rw [flag,h]; exact min_le_left ..; rw [flag,h]; exact min_le_right ..
lemma halos (i:ℕ): e.haloSpan i ≤ e.flag i/8 := (e.light_open i).trans ((e.gateR i).trans (min_le_left ..))
lemma tent (i:ℕ) : e.haloSpan i ≤ 1:= (e.light_open i).trans (le_trans (div_le_self (by positivity) (by norm_num)) (min_le_left ..))
variable (E:∀ n, RackCore e.a e.M n)
def provisional (i n:ℕ) : Stairs G (e.L i):= if h: i < n then ((E n).heir i h).V else fun _ _ _=>0
abbrev atlas (i n:ℕ) := Origin.stretch (e.R i) e.a.clock.kernel G (e.provisional E i n)
structure Curtain (i n:ℕ)(x:ℝ): Prop where
    directory : (e.provisional E i n).strip (e.haloSpan i) x
    resource : (e.atlas E i n).strip (e.haloSpan i) x
structure Spire (i n m:ℕ)(x:ℝ): Prop where
    directory : (minusRows (e.provisional E i n) (e.provisional E i m)).strip (e.haloSpan i) x
    resource : (minusRows (e.atlas E i n) (e.atlas E i m)).strip (e.haloSpan i) x
lemma ensures (i n:ℕ)(hn:i<n): Curtain e E i n (e.Z i):= by
   obtain ⟨s,v,hs,hv,he,x,ht,H⟩:= (e.funded.owns i).escape; let V: Awake G (e.R i) e.a.clock.kernel (e.M.H n (i+1)) (e.M.H n i) (e.M.towers n i).A0 (e.T.η (e.J (i+1))):= awakened e.lamp hn
   have heq:= H V.alive _ (e.cash_n (i+1) n hn) (fun p=> ⟨V.handy p,V.gap p⟩) ((E n).heir i hn); constructor; · rw [provisional,dif_pos hn]; exact strip_mono heq.wheel (by exact_mod_cast ht) x
   unfold atlas; rw [provisional,dif_pos hn]; exact strip_mono heq.tilt (by exact_mod_cast ht) x
lemma buys : e.Permit (fun i b=> ∀ n m,i<n→i < m→ Spire e E i n m (b * e.η i (min n m))):= by
   obtain ⟨p,hp,hv⟩:=e.pension_bill; let y:= hp.next.mul (e.fair_z.admits (q:=e.turn) (fun i=>(Real.exp_pos _).le) (Eventually.of_forall e.turn_bound)); refine ⟨_,e.fair_z.mul y, fun i n m hn hm=>?_⟩; obtain ⟨s,b,hs,hb,he,hg,ha,H⟩:= (e.funded.owns i).escape; have ht(n:ℕ)(h:i<n): Awake G (e.R i) e.a.clock.kernel (e.M.H n (i+1)) (e.M.H n i) (e.M.towers n i).A0 (e.T.η (e.J (i+1))):= awakened e.lamp h
   let f(m:ℕ)(h:i < m):=(E m).heir i h; let x:=p (i+1)*e.η (i+1) (min m n); have hx:0≤ x:= mul_nonneg (hp.bank _) ((e.η_pos _ _).le); have hh: s≤ e.flag (i+1) := ((hb.trans (e.gateR i)).trans (min_le_right ..)).trans (div_le_self (by positivity) (by norm_num))
   obtain ⟨hK,hY⟩:= (H (ht m hm).alive _ (e.cash_n (i+1) m hm) (fun p=> ⟨(ht m hm).handy p,(ht m hm).gap p⟩) (f m hm)).charge (f n hn) (e.cash_n (i+1) n hn) (fun p=>⟨(ht n hn).handy p,(ht n hn).gap p⟩) x hx (strip_mono (hv (i+1) m n hm hn) (by exact_mod_cast hh) le_rfl)
   have hu: b*x≤ (e.Z i*(p (i+1)*e.turn i))*e.η i (min n m):= by refine (mul_le_mul_of_nonneg_right hg hx).trans_eq ?_; unfold x; rw [η_spin,min_comm m n]; change e.Z i*_=_; ring
   constructor; · unfold provisional; rw [dif_pos hm,dif_pos hn]; exact strip_mono hK (by exact_mod_cast ha) hu
   unfold atlas provisional; rw [dif_pos hm,dif_pos hn]; exact strip_mono hY (by exact_mod_cast ha) hu
end Oasis
end Reserve
end
end YM.Contacts.Barrage
