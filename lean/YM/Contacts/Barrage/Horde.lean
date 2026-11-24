import YM.Contacts.Barrage.Flight
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
open Balance Convoy
variable (e:Oasis G) {b:Bed} (x:G.ColorIndex) (E:∀ n,RackCore e.a e.M n) {H:ℕ→ℕ→Prop}{k i n r w:ℕ}{s t:ℝ≥0}{Y Q:TableFee}{F U:bore G}
section common
lemma cradle_minus {α:Type}{F U:House (Node α)} (h:Cradle α F)(hp:Cradle α U): Cradle α (F-U):= by
   refine ⟨⟨?_, fun i j he=> by simp only [Pi.sub_apply,h.thin i j he,hp.thin i j he,sub_zero]⟩, fun i j k x=> congr_arg₂ (·-·) (h.here i j k x) (hp.here i j k x), fun i=>by simp only [Pi.sub_apply,h.scalar i,hp.scalar i,sub_zero]⟩; intro i j; simp_rw [Pi.sub_apply,sub_eq_add_neg]; exact (h.poem _ _).add (hp.poem _ _).minus
lemma minus_hair {α:Type} [Fintype α]{F U:House (Node α)} (h:Cradle α F)(hp:Cradle α U)(hf:Roof s F Y)(hw:Roof t U Q) : hair (F-U) m=hair F m-hair U m:= by
   funext i k; by_cases he:k=0; · subst k; simp only [zero_not_paid F h,zero_not_paid U hp, zero_not_paid (F-U) (cradle_minus h hp),Pi.sub_apply,sub_zero]
   letI:NeZero k:= ⟨he⟩; refine focused (printFeeds (heritage (fun v=> (cradle_minus h hp).here v i k) m)) (lower_onto _) ?_; simp_rw [Pi.sub_apply,sub_eq_add_neg (F i k),sub_eq_add_neg (hair F m i k)]
   let σ:= min s t; have hl (V : House (Node α))(hV:Cradle α V): Shadow (lower m) (V i k) (hair V m i k):= printFeeds (heritage (fun v=> hV.here v i k) _); refine Shadow.add (l:=terrain σ _) (l':=terrain σ _) (hl F h) (show Shadow _ (-(U i k)) (-hair U m i k) from (by simpa only [neg_one_smul] using (hl U hp).scale (-1))) ((hf.shelter ..).weaken (terrain_le (min_le_left ..)) le_rfl) (((hw.shelter ..).weaken (terrain_le (min_le_right ..)) le_rfl).neg)
lemma bright_minus (h:Light F)(hp:Light U)(hf:Roof s F Y)(hw:Roof t U Q) : Light (F-U) := by
   refine ⟨cradle_minus h.my hp.my, fun j m i hi=>?_⟩; rw [minus_hair h.my hp.my hf hw, wind_minus i 0]; exact preservesMinus (h.protects _ _ _ hi) (hp.protects _ _ _ hi)
lemma roof_minus (hf:Roof s F Y)(hw:Roof t U Q): Roof (min s t) (F-U) (Y+Q):= ⟨fun i j=> Rooted.sub ((hf.shelter ..).weaken (terrain_le (min_le_left ..)) le_rfl) ((hw.shelter ..).weaken (terrain_le (min_le_right ..)) le_rfl)⟩
lemma charge_minus {P F:Field (Fin 2) (Node (Dye G))}{b' c:ℝ}(hs:0<s)(he:0<t)(hp:Rooted (terrain s _) P b')(h:Rooted (terrain t _) F c) : salvia G x (P-F)=salvia G x P -salvia G x F:= by
   let y:= min s t; have hu:0<y:= lt_min hs he; have hv:= h.weaken (terrain_le (η:=y) (min_le_right ..)) le_rfl; rw [sub_eq_add_neg P,salvia_sum x (hp.weaken (terrain_le (min_le_left ..)) le_rfl) hv.neg hu,← neg_one_smul ℝ F,salvia_scale x hv hu]; ring
structure Amount (Y:bore G)(f:ℕ→ℝ): Prop where
   pure : Light Y
   price : ∃ s:ℝ≥0, 0<s ∧ ∃ T:TableFee, Roof s Y T
   pinned i : salvia G x (Y i 2)= f i
lemma Amount.minus {f g:ℕ→ℝ}{x:G.ColorIndex}(h:Amount x F f)(hp:Amount x U g): Amount x (F-U) (f-g):= by
   obtain ⟨s,hs,u,hu⟩:= h.price; obtain ⟨t,ht,v,hv⟩:= hp.price; exact ⟨bright_minus h.pure hp.pure hu hv, ⟨min s t, lt_min hs ht,u+v,roof_minus hu hv⟩,fun i=>by simp only [Pi.sub_apply,charge_minus x hs ht (hu.shelter i _) (hv.shelter i _), hp.pinned i,h.pinned i]⟩
def normK (i:ℕ):ℝ:= if i=0 then 1 else 0
lemma Amount.of (i n:ℕ)(h:i ≤ n)(ht:Aegis x F (e.M.H n i)): Amount x F normK:= by
   obtain ⟨s,hs,T,hP⟩:= ht.price; have hp q:=e.lamp.all _ _ h q; exact ⟨should ht.blazing,ht.price,fun i=> by unfold normK; split; subst i; exact stark_cash hs (hp 1).starts ht.blazing hP (released e.lamp h) (fun j=> (hp j).symmetric.1) x; apply ht.honor; omega⟩
theorem Amount.owed (e: Oasis G) (r k:ℕ)(h:Amount x F 0): softRank (frock (r+2)) (dazzle F k (r+2)):= by
   obtain ⟨s,hs,T,hF⟩:= h.price; unfold dazzle; rw [if_pos (by omega)]; by_cases he:r≤2
   · interval_cases r
     · rw [show k+(0+2)-2=k by omega]; exact Lumen.salute e.simple x h.pure hF hs k (h.pinned k)
     · rw [show k+(1+2)-2=k+1 by omega]; exact (soften e.simple x h.pure hF hs k (h.pinned k)).1
     rw [show k+(2+2)-2=k+2 by omega]; exact (soften e.simple x h.pure hF hs k (h.pinned k)).2
   let Z:= F (k+(r+2)-2) (r+2); rw [show frock (r+2)=0 from by unfold frock; omega]; intro v; let V:= mask (G:=G) Z (Prod.snd ∘ v) (Prod.fst ∘ v); change Rays 0 (V ∘ axes); exact rays_zero ( (shadow_face _ _ (hF.shelter _ _) hs (Prod.snd ∘ v) (Prod.fst ∘ v)).analytic_real _)
end common
abbrev incident (i n) := (E n).studio e.Q x i
abbrev entry (i n) := caravan e.Q (e.R i) e.a.clock.kernel (e.incident x E (i+1) n) (e.provisional E i n) (e.M.H n i).metric
abbrev dust (i n) := e.incident x E i n - flare G
lemma wild (i n:ℕ)(h:i≤n): Aegis x (e.incident x E i n) (e.M.H n i):= parliament x e.oga e.lamp (E n) i h
lemma flares (i): e.incident x E i i=flare G:= RackCore.start_n ..
lemma fires (i n:ℕ)(h:i<n): e.entry x E i n=RackCore.panel e.Q (E n) i h (e.incident x E (i+1) n):= by unfold entry; rw [provisional,dif_pos h]; rfl
lemma grub (i n)(h:i<n): e.incident x E i n= let V:=e.entry x E i n; lowerHouse (sink x V) V:= by simp_rw [e.fires x E _ _ h]; exact (E n).palms e.Q x h
structure Forbes (b:Bed)(F:bore G): Prop where
   honest : Blazing F b
   price : ∃ s:ℝ≥0, 0<s ∧ ∃ T: TableFee, Roof s F T
lemma forbes (i n:ℕ)(h:i<n): Forbes (e.M.H n i) (e.entry x E i n):= by
   obtain ⟨ht,-,s,t,c,d,y,hh⟩:= candles x e.oga e.lamp (E n) h (e.wild x E _ _ h); dsimp only at hh; obtain ⟨he,-,-,-,-,-,-,-,-,u,hF,hV⟩:=hh; rw [e.fires x E i n h]; exact ⟨ht,s,he,_,hV⟩
lemma pilaster (i n:ℕ)(h:i≤n): Amount x (e.dust x E i n) 0:= by
   have he:= Amount.of e x i n h (e.wild x E i n h); have hp:= Amount.of e x i i le_rfl (e.wild x E i i le_rfl); rw [e.flares] at hp; simpa only [sub_self] using he.minus hp
lemma pendow (i n m)(hn:i≤n)(hm: i ≤ m): Amount x (e.dust x E i n-e.dust x E i m) 0:= by simpa only [sub_zero] using ((e.pilaster x E _ _ hn).minus (e.pilaster x E _ _ hm))
def Past (i r j v:ℕ):Prop:= j < i ∨(j=i∧r < v)
structure Income (k i r:ℕ):Prop where
   law : Balance.Stable e Nat.le (e.Bx k) (fun v n=> e.incident x E v n i r) -- incl derivative eccentric
   raw : Balance.Stable e Nat.lt (e.Bx k) (fun v n=> e.entry x E v n i r)
lemma nobles (k r:ℕ) (h:i+2 < r) : e.Income x E k i r:= by
   refine ⟨Balance.Stable.cong Balance.Stable.zero (fun v n hv=>?_),Balance.Stable.cong Balance.Stable.zero fun v n hv=>?_ ⟩; exact ((e.wild x E _ _ hv).blazing.frame.thin i r (.inr h)).symm; exact ((e.forbes x E _ _ hv).honest.frame.thin i r (.inr h)).symm
lemma without (k i:ℕ) : e.Income x E k i 0:= ⟨Balance.Stable.costsEmpty,Balance.Stable.costsEmpty⟩
lemma rankOne (k i:ℕ): e.Income x E k i 1:= by
   refine ⟨Balance.Stable.cong Balance.Stable.zero (fun v n h=>?_ ),Balance.Stable.cong Balance.Stable.zero (fun v n h=>?_ )⟩; · obtain ⟨s,-,T,hT⟩:= (e.wild x E v n h).price; exact (rank_one e.simple (should (e.wild x E _ _ h).blazing) hT i).symm
   obtain ⟨s,-,T,hT⟩:= (e.forbes x E _ _ h).price; exact (rank_one e.simple (should (e.forbes x E _ _ h).honest) hT i).symm
-- base K its own chair
lemma kin_diff {F U:Bed}{b:ℝ} (h:(portfolio F.metric U.metric).strip (s:ℝ) b)(ht:0 ≤ b) (he:2*(t:ℝ) ≤ s): Rooted (terrain t _) (kin G F.metric 2-kin G U.metric 2) (‖(2:ℝ)⁻¹‖*((Fintype.card (Breed 1 (Dye G)):ℝ)*b)):= by
    let V:= minusRows (ax G F.metric) (ax G U.metric); have hx: V.strip (s:ℝ) b:= by
       rintro ⟨a,i⟩ ⟨d,j⟩; by_cases he:i=j; · rw [show V (a,i) (d,j)=_ from (show _=portfolio F.metric U.metric a d from funext fun x=> by simp [V,minusRows,portfolio,ax,he])]; apply h
       simp [V,Width,minusRows,ax,he]; exact budget_loosen budget_zero ht
    unfold kin; erw [dif_pos rfl,dif_pos rfl]; dsimp only [takeRank]; rw [←smul_sub,← prints_sub]; exact ((arrive_both hx ht he).even).smul _ -- arg e unused
lemma kin_base (k:ℕ): Balance.Stable e Nat.le (e.Bx k) (fun i n=> kin G (e.M.H n i).metric 2):= by
   let y : ℝ:= (2:ℝ)⁻¹*Fintype.card (Breed 1 (Dye G)); have hy:0≤ y:= by unfold y; positivity
   obtain ⟨p,hp,hP⟩:= e.pension_bill; let t :=e.pier (fun _=> Dye G); let Y i n:= kin G (e.M.H n i).metric 2; have hu i: 2*(e.haloSpan i:ℝ)≤(e.flag i:ℝ):= by have he:= NNReal.coe_le_coe.mpr (e.halos i); unfold haloSpan; push_cast at *; linarith only [he, NNReal.coe_nonneg (e.flag i)]
   apply e.removed (γ:=fun _=> Dye G) (u:=Y) k; refine ⟨⟨_,(e.fair_const _ hy).mul e.fair_z,fun i n h=> ?_⟩,_, (e.fair_const _ hy).mul hp,fun i n m hn hm=>?_⟩
   · convert (kin_desc (G:=G) 1 (e.M.H n i).metric (released e.lamp h) (e.portfolio_n i n h) (e.z_pos i).le (hu i|>.trans (NNReal.coe_le_coe.mpr (e.before i))) 2).ground using 1 <;> first | rfl | (unfold y; ring)
   let Z:=p i*e.η i (min n m); have hh:0≤Z:= mul_nonneg (hp.bank i) ((e.η_pos ..).le); have he:= kin_diff (F:=e.M.H n i) (U:=e.M.H m i) (G:=G) (hP i n m hn hm) hh (hu i); convert he using 1 <;> first| rfl | (unfold y; rw [Real.norm_of_nonneg (by positivity)];ring)
lemma incident_core (n i:ℕ)(h:i≤n): e.incident x E i n 0 2= kin G (e.M.H n i).metric 2:= by obtain ⟨s,-,T,hT⟩:= (e.wild x E i n h).price; exact east ((e.wild x E _ _ h).blazing) (hT.shelter 0 2) (released e.lamp h)
lemma old_enough (n i k:ℕ)(h:i≤n): Rooted (e.Bx k i) (e.incident x E i n 0 2) (share e.T G (e.J i) k):= by rw [incident_core _ _ _ n i h]; exact ((sheet e.T G (e.J i) k).choose_spec.2 _ (e.cash_n i n h)).weaken (fun x=>e.range_shrink i x) le_rfl
lemma era (k:ℕ): e.Income x E k 0 2:= by
   have H:= e.kin_base k; obtain ⟨⟨p,hp,h⟩,q,hq,ht⟩:= H; have he: Balance.Stable e Nat.lt (e.Bx k) (fun i n=> kin G (e.M.H n i).metric 2):= ⟨⟨_,hp,fun i n (h':i<n)=>h i n h'.le⟩,_,hq,fun i n m (hn:i<n) (hm:i < m)=> ht i n m hn.le hm.le⟩
   exact ⟨(e.kin_base k).cong (fun i n h=> e.incident_core x E n i h|>.symm), he.cong (fun i n h=> by simp [entry,caravan,kiss,mintage])⟩
end Oasis
end Reserve
end
end YM.Contacts.Barrage
