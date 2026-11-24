import YM.Contacts.Barrage.Frame
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
open Balance
variable {e:Oasis G}{x:G.ColorIndex}{E:∀ n,RackCore e.a e.M n}{i j n m r s k u:ℕ}{H:ℕ→ℕ→Prop}{a b:ℕ→ℝ}
-- mechanical collector.
lemma permit_all {ι:Type*}{P:ℕ→ι→ℝ→Prop} (hk:∀ i k, Monotone (P i k))(s:Finset ι)(h:∀ i∈s,e.Permit (fun v b=>P v i b)): e.Permit fun i b=> ∀ j∈s,P i j b := by
   induction s using Finset.induction with | empty=> exact ⟨_,e.fair_z,fun _ _ h=> (Finset.notMem_empty _ h).elim⟩|insert i v hi ih=>
   obtain ⟨p,hp,hq⟩:= ih fun _ h'=> h _ (mem_insert_of_mem h'); obtain ⟨q,hg,hH⟩:= h i (mem_insert_self _ _); refine ⟨_,hp.add hg,fun n j hj=> ?_⟩; rcases mem_insert.mp hj with h|h; · subst j; exact hk _ _ (le_add_of_nonneg_left (hp.bank n)) (hH n)
   exact hk _ _ (le_add_of_nonneg_right (hg.bank n)) (hq n _ h)
variable (h:e.Dawn x E k i (r+2)) (hk:3≤k) (ht:r ≤ i) (hx:i≠0)
-- Fdd
include h ht
lemma minor (j:ℕ)(hj:j<r+2): Balance.Stable e Nat.lt (fun i=> e.facet (fun _=> Dye G) (i+1)) (fun v n=> dazzle (dust e x E (v+1) n) (i-r) j):= by
   by_cases hh: 2 ≤ i-r+j; swap; · simp_rw [dazzle,if_neg hh]; exact Balance.Stable.zero
   simp_rw [dazzle,if_pos hh]; let t:=i-r+j-2; have hp : Past i (r+2) t j:=Or.inl (by unfold t; omega); exact Balance.Stable.further (e.shifts ((h _ _ hp).law.sub (e.flare_fluint t j k))) (fun _ _=> bath_terrace _)
omit h ht
lemma display (ht:r ≤ i)(F:bore G): dazzle F (i-r) (r+2)=F i (r+2):= by rw [dazzle, if_pos (by omega),show i-r+(r+2)-2=i from by omega]
lemma separate {α:Type}(F U:House α)(i r:ℕ): dazzle (F-U) i r=dazzle F i r-dazzle U i r:= by unfold dazzle; split; rfl; rw [sub_zero]
variable (hh : ∀ j,e.towerQ E k r j (a j) (b j)) (hy:e.Fair b)(hj:e.Fair a)(hσ:∀ᶠ j in atTop,a j=(e.drift j)^2)
include h ht hh hy
lemma lead_A : e.Permit (fun j t=> ∀ n,j<n→∀ y,Rooted (e.Bx k (j+1)) (e.dust x E (j+1) n i (r+2)) y→ Rooted (e.Bx k j) (e.bedLift E j n (e.dust x E (j+1) n i (r+2))) ((a j/e.fundHat k j)*y+t)):= by
    obtain ⟨p,hp,hq⟩:= permit_all (e:=e) (P:=fun v j b=> ∀ n,v<n→ Rooted (e.facet (fun _=> Dye G) (v+1)) (dazzle (e.dust x E (v+1) n) (i-r) j) b) (fun _ _ _ _ hi h v hh=>(h v hh).weaken (fun _=>le_rfl) hi) (Finset.range (r+2)) (fun j h'=> (minor h ht j (Finset.mem_range.mp h')).1)
    refine ⟨_,hy.mul hp,fun j n hn y H=>?_⟩; let Y:= dust e x E (j+1) n; have ht':=e.pilaster x E (j+1) n hn; rw [← display ht (dust e x E (j+1) n)] at H ⊢; exact hh j n hn Y (i-r) y (p j) (hp.bank _) ht'.pure (Amount.owed x e r (i-r) ht') H fun t ht=> hq j t (Finset.mem_range.mpr ht) _ hn
lemma lead_B : e.Permit (fun j t=> ∀ n m,j<n→j < m→∀ y,Rooted (e.Bx k (j+1)) (e.dust x E (j+1) n i (r+2)- e.dust x E (j+1) m i (r+2)) y→ Rooted (e.Bx k j) (e.bedLift E j n (e.dust x E (j+1) n i (r+2)-e.dust x E (j+1) m i (r+2))) ((a j/e.fundHat k j)*y+t*e.η j (min n m))):= by
    obtain ⟨p,hp,hq⟩:=permit_all (e:=e) (P:=fun v j b=> ∀ n m,v<n→v < m→ Rooted (terrain (e.ξ (v+1)) _) (dazzle (e.dust x E (v+1) n) (i-r) j-dazzle (e.dust x E (v+1) m) (i-r) j) (b*e.η v (min n m))) (fun _ _ _ _ hi h v w hv hh=> (h v w hv hh).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right hi (e.η_pos ..).le)) (Finset.range (r+2)) (fun j h'=> (minor h ht j (Finset.mem_range.mp h')).2)
    refine ⟨_,hy.mul hp,fun j n m hN hm y hF=>?_⟩; let Y:=e.dust x E (j+1) n-e.dust x E (j+1) m; let x' := p j*e.η j (min n m); have hp₀:= e.pendow x E (j+1) n m hN hm; change Rooted _ (Y i (r+2)) y at hF; change Rooted _ (bedLift e E j n (Y i (r+2))) _; rw [←display ht Y] at hF ⊢; rw [mul_assoc (b j) (p j)]; refine hh _ _ hN Y (i-r) y x' (mul_nonneg (by exact hp.bank j) (e.η_pos ..).le) hp₀.pure (Amount.owed x e r (i-r) hp₀) hF (fun t hu=>?_ ); unfold Y; rw [separate]; exact hq j t (Finset.mem_range.mpr hu) n m hN hm -- hp'
include hx
-- strict decomposition using below-rate input cap
lemma polar: e.Permit (fun j t=>∀ n,j<n→∀ y,Rooted (e.Bx k (j+1)) (e.dust x E (j+1) n i (r+2)) y→ Rooted (e.Bx k j) (e.entry x E j n i (r+2)) ((a j/e.fundHat k j)*y+t)):= by
   obtain ⟨p,hp,hq⟩:= lead_A h ht hh hy; obtain ⟨q,Hq,hv⟩:= (e.brunt_law x E h).1; refine ⟨_,hp.add Hq,fun j n H y ht=>?_⟩; rw [piloted e x E h hx j n H (by omega) (ht.weaken bath_terrace le_rfl),← add_assoc]; exact (hq _ _ H _ ht).add (hv _ _ H)
omit h ht hh hy hx
lemma vacuumed (hσ:∀ᶠ j in atTop,a j=(e.drift j)^2): Tendsto a atTop (𝓝 0) ∧ Tendsto (fun j=> a j*e.turn j) atTop (𝓝 0) := by
   have he:Tendsto e.drift atTop (𝓝 0):=tendsto_inv_atTop_zero.comp e.turn_tend; refine ⟨?_ , he.congr' (hσ.mono fun j hj=>?_ )⟩; · apply (show Tendsto (fun j=> (e.drift j)^2) atTop (𝓝 0) from (by simpa using he.pow 2)).congr' (hσ.mono fun j h=>h.symm)
   dsimp only; rw [hj]; unfold drift; have h:= e.turn_ge j; field_simp
include h ht hh hy hx hj
lemma productive (h':Balance.Base e Nat.le (e.Bx k) (fun j n=> e.dust x E j n i (r+2))) : Balance.Base e Nat.lt (e.Bx k) (fun j n=> e.entry x E j n i (r+2)):= by
    obtain ⟨p,hp,hH⟩:= e.shift_base h'; obtain ⟨s,hs,hS⟩:= polar h ht hx hh hy; have ha:e.Fair (fun i=>a i /e.fundHat k i):= hj.admits (fun b=> div_nonneg (hj.bank _) (zero_le_one.trans (e.fund_pos _ _))) (Eventually.of_forall fun i=> div_le_self (hj.bank i) (e.fund_pos ..)); exact ⟨_,(ha.mul hp).add hs,fun j n (h:j<n)=> hS j _ h _ (hH j n h)⟩
include hk hσ
lemma sand : Balance.Base e Nat.le (e.Bx k) (fun j n=> e.dust x E j n i (r+2)):= by
   obtain ⟨p,hp,hq⟩:= polar h ht hx hh hy; obtain ⟨t,Hq,hr⟩:= (strictTick hk h ht).1; let Q v:= e.Bx k v; let V v:=e.fundHat k v; let F:=e.dust x E; let R:=fun v n=>F v n i (r+2); let X:=fun j=> V j*p j+t j; have hX:= (e.fair_fund k|>.mul hp).add Hq; apply e.seal_gain id (fun j n b=> Rooted (e.Bx k j) (R j n) b) (fun i b _ _ hi h=> h.weaken (fun _=>le_rfl) hi) a (vacuumed hσ).1 hj.bank hX (fun y=> ?_) (fun j n hn b hb h0=> ?_);
   · unfold R F dust; simp only [id_eq,flares,sub_self,Pi.zero_apply]; exact (Rooted.tranquility _).weaken (fun _=>le_rfl) (hX.bank y)
   let U:=e.entry x E j n; let η:= p j; let B:=V j; let ζ:=e.paid x E i r j n; change Rooted _ (e.dust x E j n i _) _; rw [show e.dust x E j n i (r+2)=_ from e.withdrawn x E _ _ hn hx ht]; have he:= (withdraw_asset (E:=E) x hk (Nat.le_of_lt hn) (hq _ _ hn b h0)).sub (hr _ _ hn); convert he using 1; try rfl; change a j*b+ (B*η+t j)= B*(_/B*b+η)+t j; have hv: 0 < B:= zero_lt_one.trans_le (e.fund_pos ..); field_simp; ring
-- after value propagation, extra losses stage post allowed; same-column diff uses LEFT wires only
omit hσ hk hj
variable (hv:Balance.Base e Nat.le (e.Bx k) (fun j n=> e.dust x E j n i (r+2)))
include hv
lemma polarB : e.Permit (fun j t =>∀ n m,j<n→j < m→∀ y, Rooted (e.Bx k (j+1)) (e.dust x E (j+1) n i (r+2)-e.dust x E (j+1) m i (r+2)) (y*e.η (j+1) (min n m))→ Rooted (e.Bx k j) (e.entry x E j n i (r+2)-e.entry x E j m i (r+2)) (((a j*e.turn j)/e.fundHat k j*y+t)*e.η j (min n m))):= by
   obtain ⟨p,hp,hq⟩:= lead_B h ht hh hy; obtain ⟨t,ht,hr⟩:= (e.brunt_law x E h).2; obtain ⟨s,hs,hS⟩:= e.shift_base hv; let X j n:=e.dust x E (j+1) n i (r+2); let Q := (fun _:ℕ=> Dye G); let J j:= e.facet Q (j+1); have hJ i n (hN:i<n): Rooted (J i) (X i n) (s i):= (hS i n hN).weaken bath_terrace le_rfl; have hZ: Balance.Base e Nat.lt J X:= ⟨s,hs,hJ⟩;
   obtain ⟨d,hd,hD⟩:= (e.atrDue E).driftFee (fun i=>e.stock i (Dye G) (Dye G)) hZ; obtain ⟨w,hw,hW⟩:= (e.atrDue E).coag; let B j:=d j*e.xloose k j
   refine ⟨_,(hp.add (hd.mul (e.fair_loose k))).add ht, fun j n m hn hm y h'=>?_⟩; let ζ:=e.η j (min n m); let ℓ(K :ℕ):= e.bedLift (r:=r+2) E j K; let Y(n:ℕ):=brunt e x E j n i (r+2); let β:=e.fundHat k j
   rw [piloted e x E h hx j n hn (by omega) (hJ _ _ hn), piloted e x E h hx j m hm (by omega) (hJ _ _ hm)]; have hf:ℓ n (X j n-X j m)=ℓ n (X j n)-ℓ n (X j m):= hoist_sub (e.stock j _ _) (hW j n hn) (hJ j n hn) (hJ j m hm);
   let x' := e.xloose k j; have hu : Rooted (e.Bx k j) (ℓ n (X j n-X j m)) (a j/β* (y*e.η (j+1) (min n m))+p j*ζ):= hq j _ _ hn hm (y*e.η (j+1) (min n m)) h' -- needs input **y'**, lead_B signature y bound not normalized!
   have he: Rooted (e.Bx k j) (ℓ n (X j m)-ℓ m (X j m)) (x'*(d j*ζ)):= e.chuting k j (hD j n m hn hm); rw [hf] at hu; have hz: Rooted _ (Y n-Y m) _:= hr j n m hn hm; change Rooted _ (ℓ n (X j n)+Y n - (ℓ m (X j m)+Y m)) _; convert (hu.add he).add hz using 1; abel; change _=_+(x'*(d j*ζ))+t j*ζ; unfold ζ β x'; rw [e.η_spin]; ring
include hσ hj hk
lemma atypia (hR: Balance.Base e Nat.lt (e.Bx k) (fun j n=> e.entry x E j n i (r+2))): Shade e Nat.le (e.Bx k) (fun j n=> e.dust x E j n i (r+2)):= by
   obtain ⟨p,hp,hP⟩:= polarB h ht hx hh hy hv; obtain ⟨t,ht',hr⟩:= (strictTick hk h ht).2; obtain ⟨f,hf,hF⟩:= withdraw_drift x E hR hk; obtain ⟨z,hz,hZ⟩:= hR; obtain ⟨g,hg,hG⟩:= hv; let w i:= e.turn i*a i; have hw:Tendsto (fun i=>a i * e.turn i) atTop (𝓝 0):= (vacuumed hσ).2
   let C j:= e.fundHat k j; let F j n:= e.dust x E j n i (r+2); let U(x:ℕ×ℕ):= min x.1 x.2; let M j:= C j*p j+ f j + t j; let β j:= M j + (g j+g j); let P (j:ℕ)(x: ℕ ×ℕ)(t:ℝ):= Rooted (e.Bx k j) (F j x.1-F j x.2) (t*e.η j (U x)); let H := (((e.fair_fund k).mul hp).add hf).add ht'; have hβ := H.add (hg.add hg); suffices HF : e.Permit (fun j b=> ∀ y:ℕ×ℕ,j ≤ U y → P j y b) by
       obtain ⟨v,hy,hU⟩:=HF; exact ⟨_,hy,fun j n m hn hm=> hU j (n,m) (le_min hn hm)⟩
   refine e.seal_gain U P (fun j n t s hi h=> h.weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right hi (e.η_pos ..).le)) (fun j=> a j*e.turn j) hw (fun i=> mul_nonneg (hj.bank i) (Real.exp_pos _).le) (p:=β) hβ (fun y=>?_ ) (fun j n hn v h0 h1=> ?_)
   · unfold P; rw [self_η, mul_one]; let u:=U y; exact ((hG u _ (show u ≤ y.1 from min_le_left y.1 y.2)).sub (hG u _ (show u ≤ y.2 from min_le_right y.1 y.2))).weaken (fun _=> le_rfl) (le_add_of_nonneg_left (H.bank u))
   · obtain ⟨n,m⟩:=n; change j < min n m at hn; unfold P; let h': j < n:= lt_of_lt_of_le hn (min_le_left ..); have hm:j < m:= lt_of_lt_of_le hn (min_le_right ..);
     let y:= e.η j (min n m); let Z n:=entry e x E j n i (r+2); let t₀:=a j*e.turn j; let V n:=e.withdraw x E j n r; have HH : Rooted (e.Bx k j) (V n (Z n-Z m)) (C j*((t₀/C j*v+p j)*y)):= withdraw_asset _ hk h'.le (hP j n m h' hm v h1); have he: Rooted (e.Bx k j) (V n (Z m)-V m (Z m)) (f j*y):= hF j n m h' hm;
     rw [show V n (Z n-Z m)=_ from e.withdraw_sub x E (hZ _ _ h') (hZ _ _ hm)] at HH; change Rooted _ (F j n-F j m) ((t₀*v+(M j+(g j+g j)))* y); let t' := paid e x E i r j; have hx(n':ℕ)(h':j<n') : F j n' = V n' (Z n') - t' n':= e.withdrawn x E j n' h' hx ht;
     rw [hx n h',hx m hm,show V _ _-t' n-(V _ _-t' m)= (V n (Z n)-V n (Z m)+(V n (Z m)-V m (Z m))) -(t' n-t' m) from (by abel)]; refine ((HH.add he).sub (hr j n m h' hm)).weaken (fun _=> le_rfl) ?_; have ht: 0<C j:= zero_lt_one.trans_le (e.fund_pos ..); refine le_trans (b:=(t₀*v+M j)*y) (le_of_eq ?_) (mul_le_mul_of_nonneg_right (add_le_add_right (le_add_of_nonneg_right (add_nonneg (hg.bank _) (hg.bank _))) (t₀*v)) (e.η_pos ..).le); change _+t j*y=_; unfold M; field_simp; ring
omit hk hσ
lemma oolite (hQ:Shade e Nat.le (e.Bx k) (fun j n=> e.dust x E j n i (r+2))) : Shade e Nat.lt (e.Bx k) (fun j n=> e.entry x E j n i (r+2)):= by
   obtain ⟨p,hp,hP⟩:= polarB h ht hx hh hy hv; obtain ⟨t,ht,hr⟩:=hQ; let V(i:ℕ):=(a i*e.turn i); have he:=hj.mul (e.fair_z.admits (q:=e.turn) (fun i=> (Real.exp_pos _).le) (Eventually.of_forall e.turn_bound)); have hh:= he.admits (q:=fun i=> V i/e.fundHat k i) (fun i=> div_nonneg (he.bank i) (zero_le_one.trans (e.fund_pos k i))) (Eventually.of_forall fun i=>div_le_self (he.bank i) (e.fund_pos ..)); exact ⟨_, (hh.mul ht.next).add hp,fun j n m (hn: j<n) (hm:j < m)=> hP j n m hn hm (t (j+1)) (hr (j+1) n m hn hm)⟩
omit hj hh hy hv
include hk
lemma trust_rate : Income e x E k i (r+2):= by
   obtain ⟨a,b,ha,hb,hA,hB⟩:=e.luminous E k r hk; have he:=sand h hk ht hx hB hb ha hA; have hf:=productive h ht hx hB hb ha he; have hx':Balance.Stable e Nat.le (e.Bx k) (fun j n=> e.dust x E j n i (r+2)):= ⟨he,atypia h hk ht hx hB hb ha hA he hf⟩; refine ⟨?_, hf, oolite h ht hx hB hb ha he hx'.2⟩; exact (hx'.add (e.flare_fluint i (r+2) k)).eq fun j n=> sub_add_cancel _ _
omit h ht hx hk
lemma rentLaw (e:Oasis G)(x:G.ColorIndex)(E:∀ n,RackCore e.a e.M n)(k:ℕ)(hk:3 ≤ k): ∀ i r,e.Income x E k i r:= by
   intro i; induction i using Nat.strongRecOn with| _ i ih=>
   intro r; by_cases he:r≤ i+2; swap; · exact e.nobles x E k r (by omega)
   generalize hy:i+2-r=p; induction p using Nat.strongRecOn generalizing r with| _ p ih' =>
   have hp: Dawn e x E k i r:= by
     intro l v hv; rcases hv with h|⟨h,hr⟩; · exact ih l h v
     subst l; by_cases h:v ≤ i+2; · exact ih' (i+2-v) (by omega) v h rfl
     exact e.nobles x E _ _ (by omega)
   cases r; · exact e.without x E k i
   rename_i r; cases r; · exact e.rankOne x E k i
   rename_i r; have hh:r ≤ i:= (by omega); by_cases hx:i=0; · have hr:r=0:=(by omega); subst r; subst i; exact e.era x E k
   exact trust_rate hp hk hh hx -- args
end Oasis
end Reserve
end
end YM.Contacts.Barrage
