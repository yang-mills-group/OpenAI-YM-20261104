import YM.Contacts.Barrage.Horde
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}
namespace Reserve
open Origin Slope Ion Resetter Lumen Next.Free Extension.UV.Linear
-- custody Reader
namespace Oasis
open Balance Spark
variable (e:Oasis G) {b:Bed} (x:G.ColorIndex)(E:∀ n,RackCore e.a e.M n){i j n r k l v:ℕ}{H:ℕ→ℕ→Prop}
-- tail credits
lemma stock (i:ℕ)(α β:Type) : Ripple (terrain (e.ξ (i+1)) α) (terrain (e.haloSpan i) β) (access (e.L i) (e.haloSpan i)):= influx (e.reaches i)
abbrev early (i n:ℕ):= clan e.Q (e.R i) e.a.clock.kernel (e.incident x E (i+1) n)
abbrev Satisfies (r:ℕ)(P:∀ i,ℕ→Field (Fin r) (Node (e.Wd i))) := Balance.Stable e Nat.lt (e.pier e.Wd) P
def Dawn (k i r:ℕ): Prop := ∀ j v,Past i r j v→Income e x E k j v
variable (h:e.Dawn x E k i r)
def seedling (j w r:ℕ) := let P:=e.R j;
    @Sub.sub (Field (Fin r) (Node (Mixed G P))) _ (if r=w then Spark.sparkles P e.Q r else 0) (show Field (Fin r) (Node (Mixed G P)) from (if r=w+2 then fireworks P e.a.clock.kernel G r else 0))
lemma seedling_stance (r j:ℕ) : e.Satisfies r (fun i _ => e.seedling i j r):= by
   let P i:= Spark.sparkles (e.R i) e.Q r; let U i:=fireworks (e.R i) e.a.clock.kernel G r
   have he: ∀ᶠ i in atTop,Rooted (e.pier e.Wd i) (P i) (e.Z i) ∧ Rooted (e.pier e.Wd i) (U i) (e.Z i):= by
     refine (e.a.fits.deep.eventually_ge_atTop r).mono fun i hi=>?_; have ht:= (e.funded.owns i).oil r (hi.trans (e.a.fits.mono (Nat.le_succ i))); exact ⟨ht.1.weaken (terrain_le (e.tent i)) le_rfl, ht.2.1.weaken (terrain_le (e.tent i)) le_rfl⟩
   unfold seedling; apply Balance.Stable.sub (R:=fun i _=>if r=j then P i else 0)
   · by_cases h:r=j; swap; · simp_rw [if_neg h]; exact Balance.Stable.zero
     simp_rw [if_pos h]; refine Balance.Stable.all _ (Oasis.permit.exists e (fun i=>?_ ) _ (he.mono fun _ hu=> hu.1) e.fair_z); let hp: Rooted (terrain _ _) (P i) _:= aboard_summed (Spark.templates G (e.R i)) (e.haloSpan i) _; exact ⟨_,hp.cash,hp⟩
   by_cases h:r=j+2; swap; · simp_rw [if_neg h]; exact Balance.Stable.zero
   simp_rw [if_pos h]; refine Balance.Stable.all _ (Oasis.permit.exists e (fun i=>?_ ) _ (he.mono fun _ hu=> hu.2) e.fair_z); let hp: Rooted (terrain _ _) (U i) _:= aboard_summed _ (e.haloSpan i) _; exact ⟨_,hp.cash,hp⟩
abbrev plant (i:ℕ) : Cross (e.L i) (Dye G) (e.Wd i):= adopt (Cellar G (e.L i)) (Dye G)
lemma givens (j n:ℕ)(h:i≠0) (r:ℕ): e.early x E j n i r=e.seedling j i r-lifts (e.plant j) (e.incident x E (j+1) n i r):= by
   unfold early clan compote; rw [if_neg h]; let P:=e.R j; let u:Field (Fin r) (Node (e.Wd j)):= if r=i then Spark.sparkles P e.Q r else 0; let v:Field (Fin r) (Node (e.Wd j)):= if r=i+2 then fireworks P e.a.clock.kernel G r else 0; let Z:=lifts (e.plant j) (e.incident x E (j+1) n i r); change u+-(v+Z)= (u-v)-Z; abel
lemma constFl (w r:ℕ) : Balance.Stable e H (e.pier (fun _=> Dye G)) (fun i (_:ℕ)=> flare G w r):= by
   let p:= flare_cost G 1 w r; have hp : 0 ≤ p:= (flare_purse G 1 |>.shelter w r).cash; apply Balance.Stable.all (fun _=>flare G w r) ⟨_,e.fair_const p hp, fun i=> ((flare_purse G 1).shelter w r).weaken (terrain_le (e.tent i)) le_rfl⟩
lemma pastTrans {p q w z:ℕ}(hx:Past i r p q)(hp:Past p q w z): Past i r w z:= by unfold Past at *; omega
lemma earlier {k i r:ℕ}{e:Oasis G}{E:∀ n,RackCore e.a e.M n}{x:G.ColorIndex}(h:e.Dawn x E k i r)(hv:Past i r j v):
   e.Satisfies v (fun m n=> e.early x E m n j v) := by
   by_cases he:j=0; · apply Balance.Stable.cong Balance.Stable.zero; intro k n hz; subst j; rw [early,clan,compote,if_pos rfl]
   apply (Balance.Stable.sub (e.seedling_stance v j) ((e.adoptDue).lift (fun p=> e.stock p (Dye G) (e.Wd p)) ((e.shifts ((h j v hv).law)).further fun p z=> bath_terrace z))).eq; exact fun _ _=> (e.givens x E _ _ he _).symm
abbrev beet (i n:ℕ) := gathering (plane (e.line E i n)) (e.early x E i n)
lemma beet_zero (z i r:ℕ)(h:i<n)(he:j=0 ∨ j+2<r) : e.beet x E i n z j r=0:= by
   let hp:= (e.wild x E (i+1) n h); exact ((clan_shape G e.Q _ hp.blazing.frame.toShaped).bounded _ z).thin j r he
include h in
lemma dewroot : ∀ (d l w:ℕ), (Past i r w l ∨ (w=i∧l=r∧d≠0)) → e.Satisfies l (fun v n=> beet e x E v n d w l) := by
   intro d; induction d using Nat.strongRecOn with| _ d ih=>
   intro l w hw; unfold Past at hw; cases d; · simp only [beet,gathering_start]; exact earlier h (by unfold Past; omega)
   rename_i d; simp_rw [beet,gathering_next]; apply Balance.Stable.smul; unfold wake; refine (e.racket E |>.degree (x:=fun i n=> beet e x E i n d w (l+2)) (ih d (by omega) _ _ (by unfold Past; omega))).add (Balance.Stable.sum (antidiagonal w) ?_); intro p hp; apply Balance.Stable.sum (antidiagonal d); intro q hq; unfold listPay; apply Balance.Stable.sum (antidiagonal l); intro j hj;
   have hp:= mem_antidiagonal.mp hp; have hq:=mem_antidiagonal.mp hq; have hj:=mem_antidiagonal.mp hj; by_cases he:p.1=0; · exact Balance.Stable.cong Balance.Stable.zero (fun i n h=> (light_close_left _ (e.beet_zero x E _ i _ h (Or.inl he))).symm)
   by_cases hk:p.2=0; · exact Balance.Stable.cong Balance.Stable.zero (fun i n h=> (light_close_right _ (e.beet_zero x E _ i _ h (Or.inl hk))).symm)
   exact (e.racket E).list (ih _ (by omega) _ _ (by unfold Past; omega)) (ih _ (by omega) _ _ (by unfold Past; omega))
def drove (i n w r:ℕ) := (∑ j∈Finset.range (3*w),e.beet x E i n (j+1) w r)+ e.seedling i w r
lemma drove_income (h:e.Dawn x E k i r) : e.Satisfies r (fun j n=> e.drove x E j n i r) := Balance.Stable.add (Balance.Stable.sum _ (fun j _=> e.dewroot x E h (j+1) r i (Or.inr ⟨rfl,rfl,by omega⟩))) (e.seedling_stance r i)
lemma earnedDrive (j n:ℕ)(hi:i≠0)(r:ℕ): massaged (plane (e.line E j n)) (e.early x E j n) i r=e.drove x E j n i r - lifts (e.plant j) (e.incident x E (j+1) n i r):= by unfold massaged drove beet; rw [sum_range_succ', gathering_start,e.givens x E _ _ hi]; abel
lemma hail {F:Field (Fin r) (Node (Dye G))}[NeZero r]{b:ℝ} (i n)(hi:i<n)(hp: Rooted (terrain (e.ξ (i+1)) _) F b)(hf:∀ z:Cover,Mirrored (backpack z) F): hoist (plane (e.out E i n)) (lifts (e.plant i) F)=lifts (e.atlas E i n) F:= by
   let s:=e.haloSpan i; let P:=e.R i; let R:=e.out E i n; let v:=e.atlas E i n; let S(k:Side):=sprig P e.a.clock.kernel k; let f(k:Side):=k*P.L; let W(k:Side):=printShadow F (f k); let Z(k:Side):= hoist (installed (S k).ratio (adopt (Cellar G P.L) (Dye G))) (W k); let H(k:Side):=hoist (Row.acts R k) (Z k); let X(k:Side):=hoist (installed (S k).ratio v) (W k);
   have ht(k:Side): Shadow (lower (f k)) F (W k):= printFeeds (heritage hf (f k)); have h₁ : Row.strip (e.plant i) (e.haloSpan i) 1:= adopt_cost _ _ _; have he:=ledgers (R:=e.plant i) h₁ zero_le_one; let l:= e.ξ (i+1); have hx : Ripple (terrain l (Dye G)) (terrain s (e.Wd i)) (access (e.L i) s):= influx (e.reaches i); have hk:= hoist_pay hx he hp; have hu:= ledgers (e.ensures E i n hi).resource (e.z_pos i).le; have hR:= flight_stem (e.shine_due E i hi) (add_nonneg zero_le_one (e.z_pos i).le);
   refine receives (A:=H) (B:=X) (hoist_pay fareFoot hR hk) (hoist_pay (influx (e.reaches i)) hu hp) (fun m=>?_ ) (fun m=>funext fun y=>?_ )
   · exact ⟨hoist_period fareFoot hR hk (hoist_period hx he hp (ht m) (st_new (S m).ratio (e.plant i))) (row_ship R m), hoist_shape,hoist_period (influx (e.reaches i)) hu hp (ht m) (st_new (S m).ratio v),hoist_shape⟩
   let U:= R.acts m*ᵥ y; let V:= installed (S m).ratio v; let z:= V*ᵥ y
   calc
      design (H m) y = design (Z m) U:= hoist_read _ _ _
      _ = design (W m) (shave (S m) G *ᵥ U):= by rw [← offspring_paid (S m)]; exact hoist_read _ _ _
      _ = design (W m) z:= by
          rw [shaved,(show U=weave (S m) (y,z) from ?_),blooms]; unfold U; rw [show R.acts m=Forge.sky (S m) G V from skytop (G:=G) (S m) v]; exact sky_pass ..
      _ = _:= (hoist_read _ _ _).symm
lemma constFlR (w r:ℕ)(j:ℕ) : Rooted (terrain (e.ξ j) (Dye G)) (flare G w r) (flare_cost G 1 w r):= ((flare_purse G 1).shelter w r).weaken (terrain_le (e.ξ_one j)) le_rfl
-- law payload formula for direct estimate conditional, no self-application bound
abbrev bedLift (i n) (F:Field (Fin r) (Node (Dye G))) := lifts (e.atlas E i n) F
def brunt (u n i r:ℕ):= e.bedLift E u n (flare G i r)- hoist (plane (e.out E u n)) (e.drove x E u n i r)
lemma flare_fluint (i r k:ℕ): Balance.Stable e H (e.Bx k) (fun _ _=> flare G i r):= e.removed (γ:=fun _=> Dye G) k (e.constFl i r)
include h
lemma brunt_law : Balance.Stable e Nat.lt (e.Bx k) (fun u n=>brunt e x E u n i r):= by
   have hp:= e.shifts (e.flare_fluint (H:=Nat.le) i r k); exact e.removed (γ:=fun _=> Dye G) k (((e.atrDue E).lift (fun j=> e.stock j (Dye G) (Dye G)) (hp.further (k:=fun i=> terrain (e.ξ (i+1)) (Dye G)) (fun w y=> bath_terrace y))).sub ((e.shines E).lift (fun _=> fareFoot) (e.drove_income x E h)))
lemma piloted {c:ℝ} (hg:i ≠ 0) (j n:ℕ)(hj:j<n)(hr:0<r) (hw:Rooted (terrain (e.ξ (j+1)) _) (dust e x E (j+1) n i r) c) : entry e x E j n i r= e.bedLift E j n (dust e x E (j+1) n i r)+e.brunt x E j n i r:= by
   letI : NeZero r:= ⟨hr.ne'⟩; let W:=e.incident x E (j+1) n; let X:=W i r; let V:=flare G i r; let d:= e.drove x E j n i r; obtain ⟨p,hp,hc⟩:= (e.drove_income x E h).1; obtain ⟨t,ht,hR⟩:= (e.adoptDue).coag; obtain ⟨f,hf,H⟩:= (e.atrDue E).coag; let Y:=lifts (e.plant j) X; let S:= hoist (α:=Node (e.Wd j)) (r:=r) (plane (e.out E j n));
   have hy:= e.constFlR i r (j+1); have hx: Rooted _ X _:= (by rw [show X=(X-V)+V by abel]; exact hw.add hy : Rooted (terrain (e.ξ (j+1)) _) X (c+flare_cost G 1 i r));
   obtain ⟨v,hv,hU⟩:= (e.shines E).coag; let hY:= hoist_pay (e.stock j _ _) (hR j n hj) hx; let T:= e.bedLift (r:=r) E j n
   unfold entry caravan kiss; rw [if_neg hr.ne', mintage,if_neg hg]; change - S (massaged (plane (line e E j n)) (early e x E j n) i r)= T (X-V)+(T V-S d); rw [earnedDrive e x E j n hg r]; change - S (d-Y)= _; have h₁ : S (d-Y)=S d-S Y := hoist_sub fareFoot (hU j n hj) (hc j n hj) hY; have h₂ : T (X-V)=T X-T V:= hoist_sub (e.stock j _ _) (H j n hj) hx hy; have h₃:S Y=T X:= e.hail E j n hj hx (fun p=> (e.wild x E _ _ hj).blazing.frame.here p i r); rw [h₁,h₂,h₃]; abel
end Oasis
end Reserve
end
end YM.Contacts.Barrage
