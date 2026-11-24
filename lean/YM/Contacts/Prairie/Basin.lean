import YM.Contacts.Prairie.Stubs
import YM.Contacts.Prairie.Lesson
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
variable {S:Boom} {k r d:ℕ}{e}
variable (T:e.License S ζ)(hk:3≤k)(hp:enough (e.floorGoal k d) S)(H:e.Last (S:=S) (ζ:=ζ) k i (r+2))(h:i ≠ 0)(ht:r ≤ i)(hd:r ≤ d)(hs:s∈ S)
include H ht
open Oasis
lemma stamina (t:ℕ)(he:t<r+2): Fleet S (terrain ζ _) (fun p=> dazzle (e.dust p) (i-r) t):= by
    unfold dazzle; split; next hz=> exact Fleet.weaken (Fleet.sub (H (i-r+t-2) t (Or.inl (by omega))).ofPort (flare_q _ _ _ _ _)) bath_terrace
    next he=> exact Fleet.fzero
include T hp hd hk hs h
abbrev A' (e:Parcel G)(k:ℕ):ℝ := 1/4 / e.coin k
omit T hp hd hs hk H ht h in
lemma apostle (e:Parcel G)(k:ℕ):0 ≤ e.A' k:= div_nonneg (by norm_num) (zero_le_one.trans (e.coin_pos ..)) -- omit
local notation "X" => Rooted (bath ζ k (Dye G))
local notation "F" => fun p:Word=> e.dust p i (r+2)
-- beware use parenthes
local notation "Q" => fun p:Word=> e.kickoff p s i (r+2)
lemma base_step : ∃ b≥0,∀ p,OK S p→ ∀ t≥(0:ℝ), X ((F) p) t→ X ((Q) p) (e.A' k*t+b):= by
   obtain ⟨a,ha,hA⟩:= collective (P:=fun t b=> ∀ p,OK S p→ Rooted (terrain ζ _) (dazzle (e.dust p) (i-r) t) b) (Finset.range (r+2)) (fun i _ _ hv h t ht=> (h t ht).weaken (fun _=>le_rfl) hv) (fun t h=> (stamina H ht _ (Finset.mem_range.mp h)).1)
   obtain ⟨b,hb,hB⟩:= floor_cap s T hk hp hs hd; obtain ⟨c,hc,K⟩:= (board_law T hs H).1; refine ⟨b*a+c,add_nonneg (mul_nonneg hb ha) hc,fun p hv t hh h'=>?_⟩; change X (e.kickoff p s i (r+2)) _; rw [kick_formula T hs H hv h]; let Y:=e.dust p; have hh : dazzle Y (i-r) (r+2)=F p:= Oasis.display ht Y; let Z:=stays_nil p T hv; have hu:= (hB p Y (i-r) Z t a ha (by rw [hh]; exact h') (fun j hj=> hA j (mem_range.mpr hj) p hv)); rw [hh] at hu; rw [← add_assoc]; exact hu.add (K p hv)
omit hs
lemma port_will : Will S (bath ζ k _) F := by
   apply bases_run (b:=0) le_rfl (by simp only [dust,origin,sub_self,Pi.zero_apply]; exact Rooted.tranquility _) (fun x _ _ hv hh=> hh.weaken (fun _=>le_rfl) hv)
   intro s hs; obtain ⟨b,hb,B⟩:= base_step s T hk hp H h ht hd hs; obtain ⟨p,hP,P⟩:= (e.strictTick s T hk H hs).1
   let A:= e.coin k; have ht' :0<A:=zero_lt_one.trans_le (e.coin_pos k); refine ⟨A*b+p,add_nonneg (mul_nonneg ht'.le hb) hP,fun i' hi v hv he=>?_⟩; change X (e.dust (s::i') i _) _; rw [show e.dust (s::i') i (r+2)=_ from e.withdrawn i' s h ht]; convert ((e.withdraw_asset i' s T hk (hi.cons hs) (B i' hi v hv he)).sub (P i' hi)) using 1; change _=A*(1/4/A*v+b)+p; field_simp; ring
include hs
lemma U_budget : Will S (bath ζ k _) Q:= by obtain ⟨v,hv,hV⟩:= port_will T hk hp H h ht hd; obtain ⟨b,hb,hB⟩:=base_step s T hk hp H h ht hd hs; exact ⟨_,add_nonneg (mul_nonneg (e.apostle k) hv) hb,fun p hi=> hB p hi _ hv (hV p hi)⟩
lemma base_d : ∃ b≥0,∀ p q u,OK S p→ OK S q→ OK S u → ∀ t≥(0:ℝ), X ((F) (u++p)-(F) (u++q)) t→ X ((Q) (u++p)-(Q) (u++q)) (e.A' k*t+b*mileage u):= by
   obtain ⟨a,ha,hA⟩:= collective (P:=fun t b=> ∀ p q u,OK S p→ OK S q→OK S u→ Rooted (terrain ζ _) (dazzle (e.dust (u++p)) (i-r) t-dazzle (e.dust (u++q)) (i-r) t) (b*mileage u)) (Finset.range (r+2)) (fun i _ _ hv h t p u ht hh he=> (h t p u ht hh he).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right hv (mileage_pos _).le)) (fun t h=> (stamina H ht _ (Finset.mem_range.mp h)).2)
   obtain ⟨b,hb,hB⟩:= floor_cap s T hk hp hs hd; obtain ⟨c,hc,K⟩:= (board_law T hs H).2; let φ:=port_will T hk hp H h ht hd; let Φ:= φ.trade («Q»:=Rooted (terrain ζ (Dye G))) 1 zero_le_one (fun x v he=> he.weaken bath_terrace (by rw [one_mul]))
   let P:= fit_spare (2*ζ) ζ k T.emit_lt; let v := T.round_trips hs; obtain ⟨w,hw,hW⟩:= Threads.rider v (stock_bool _ _ _) (R:=F) Φ -- name
   obtain ⟨_,_,hv⟩:=v.1; obtain ⟨_,_,hφ⟩:=Φ; refine ⟨_, add_nonneg (add_nonneg (mul_nonneg hb ha) (mul_nonneg (zero_le_one.trans P.choose_spec.1) hw)) hc,fun p q u hi hj hu t _ he=>?_⟩
   let n:= u++p; let m:=u++q; let f:=(F); let Y:= e.dust n-e.dust m; let D p:= e.board p s i (r+2); let U p:=e.Lift (r:=r+2) p s; have hh : dazzle Y (i-r) (r+2) = f n-f m:= Oasis.display ht Y; let y:=mileage u; have hN:= hu.append hi; have hM:=hu.append hj; have hZ: Amount e.x Y 0:= by simpa only [sub_zero] using ((stays_nil n T hN).minus (stays_nil m T hM))
   have hl:= hB n Y (i-r) hZ t (a*y) (mul_nonneg ha (mileage_pos u).le) (by rw [hh]; exact he) (fun j h'=> by unfold Y; rw [Oasis.separate]; exact hA j (mem_range.mpr h') _ _ u hi hj hu);
   have hu' : U n (f n - f m)= U n (f n)-U n (f m):= hoist_sub (stock_bool _ _ _) (hv n hN) (hφ n hN) (hφ m hM);
   have hp:=expand_fee (k:=k) T.emit_lt (hW p q u hi hj hu); change X ((Q) n-(Q) m) _; dsimp only; rw [kick_formula T hs H hN h,kick_formula T hs H hM h]; rw [hh,show e.Lift n s (f n-f m)=_ from hu'] at hl; convert ((hl.add hp).add (K p q u hi hj hu)) using 1; swap; · unfold A'; ring
   change U n (f n)+D n-(U m (f m)+D m)=(U n (f n)-U n (f m)+(U n (f m)-U m (f m)))+(D n-D m); abel
omit hs
lemma base_dust : Diff S X F:= by
   apply diff_run (fun x _ _ ht h=>h.weaken (fun _=>le_rfl) ht) (port_will T hk hp H h ht hd) (fun _ _ _ _ ht h=> ht.sub h)
   intro s hs; let R p:= e.kickoff p s i (r+2); let W p:= e.withdraw p s r; let D p:= e.paid p s i r
   have ht':= U_budget s T hk hp H h ht hd hs; obtain ⟨b,hb,hB⟩:= base_d s T hk hp H h ht hd hs; obtain ⟨w,hw,w'⟩:= e.withdraw_d s T hk hs ht'; obtain ⟨c,hc,G⟩:= (e.strictTick s T hk H hs).2; obtain ⟨x,-,hx⟩:=ht'; let a:=e.coin k; have ha:0<a:= zero_lt_one.trans_le (e.coin_pos _); refine ⟨_,add_nonneg (add_nonneg (mul_nonneg ha.le hb) hw) hc,fun p q u hi hj hu v hv hh=>?_⟩; let n:=u++p; let m:=u++q; have hN:=hu.append hi; have hM:=hu.append hj; have he : W n (R n-R m)=W n (R n) - W n (R m):= e.withdraw_sub _ s T (hx _ hN) (hx _ hM); have hg:= (e.withdraw_asset n s T hk (hN.cons hs) (hB p q u hi hj hu v hv hh)); change X (W n (R n-R m)) _ at hg; rw [he] at hg; change X (e.dust (s::n) i _- e.dust (s::m) i _) _; rw [show e.dust (s::n) i (r+2)=_ from e.withdrawn n s h ht,show e.dust (s::m) i (r+2)=_ from e.withdrawn m s h ht]; convert ((hg.add (w' p q u hi hj hu)).sub (G p q u hi hj hu)) using 1; rotate_left; · change v/4+ (a*b+w+c)*_ = a*( (1/4/a)*v+b*mileage u)+w*mileage u+c*mileage u; field_simp; ring
   change W n (R n)-D n-(W m (R m)-D m)= (W n (R n)-W n (R m)+(W n (R m)- W m (R m))) - (D n-D m); abel
include hs
lemma base_U : Diff S X Q := by
   obtain ⟨a,ha,K⟩:= base_dust T hk hp H h ht hd; obtain ⟨c,hc,B⟩:= base_d s T hk hp H h ht hd hs; refine ⟨_,add_nonneg (mul_nonneg (e.apostle k) ha) hc,fun p q u hi hj hk=>?_⟩; convert B p q u hi hj hk _ (mul_nonneg ha (mileage_pos u).le) (K p q u hi hj hk) using 1; ring
omit hs
lemma primes : e.Works (S:=S) (ζ:=ζ) k i (r+2):= by
   let P:= port_will T hk hp H h ht hd; have he: Fleet S _ F:=⟨P,base_dust T hk hp H h ht hd⟩
   exact ⟨Holds.eq (Fleet.add he (flare_q S ζ k i _)) (fun p _=>sub_add_cancel _ _),fun s hs=> ⟨U_budget s T hk hp H h ht hd hs,base_U s T hk hp H h ht hd hs⟩ ⟩
omit H h ht hd
lemma works : ∀ i≤d, ∀ r,e.Works (S:=S) (ζ:=ζ) k i r:= by
   intro i; induction i using Nat.strongRecOn with| _ i ih=>
   intro hg r; by_cases he:r≤ i+2; swap; · exact finished T (by omega)
   generalize hy:i+2-r=t; induction t using Nat.strongRecOn generalizing r with | _ t ih' =>
   by_cases hi:i=0; · subst i; by_cases hh:r=2; subst r; exact roots T k; exact finished T (by omega)
   have hh:Last (S:=S) (ζ:=ζ) e k i r:= by
      intro j v hh; rcases hh with hh|⟨hh,h'⟩; · exact ih j hh (hh.le.trans hg) v
      subst j; by_cases h:v≤ i+2; · exact ih' (i+2-v) (by omega) v h rfl
      exact finished T (by omega)
   by_cases ht:r<2; · exact finished T (by omega)
   match r with | 0 | 1 => omega | r+2 => exact primes T hk hp hh hi (by omega) (by omega)
end Parcel
end
end YM.Contacts.Prairie
