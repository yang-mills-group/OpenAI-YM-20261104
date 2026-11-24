import YM.Contacts.Prairie.Inn
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
open PowerSeries
variable {S:Boom}{r k:ℕ}
variable {F U:Word→ PowerSeries ℝ}
lemma source_m (hp:∀ i<k,Backs S (fun v=> pin (F v) i))(hk:∀ i<k,Backs S (fun v=> pin (U v) i))(j:ℕ)(h:j < k) : Backs S (fun v=> pin (F v * U v) j):= by
   simp_rw [pin, coeff_mul]; exact Backs.sum (antidiagonal j) fun i hi=> (hp i.1 (by have h:= mem_antidiagonal.mp hi; omega)).mul (hk i.2 (by have h:=mem_antidiagonal.mp hi; omega))
lemma source_pow (hp:∀ i<k,Backs S (fun v=> pin (F v) i))(j i:ℕ)(h:i < k) : Backs S (fun v=> pin ((F v)^j) i):= by induction j generalizing i with|zero=>simp_rw [pow_zero]; apply Backs.given|succ j ih=>simp_rw [pow_succ]; exact source_m (fun i hi=>ih i hi) hp _ h
lemma source_gap (hp:∀ i<k,Backs S (fun v=> pin (F v) i))(hk:∀ i<k,Backs S (fun v=> pin (U v) i)) : Backs S (fun v=> Resetter.gap (F v) (U v) k):= by
   unfold Resetter.gap; apply Backs.sum; intro i hi; obtain ⟨hh,hl,ht⟩:=mem_filter.mp hi; have hv:= mem_antidiagonal.mp hh; exact (hp i.1 (by omega)).mul (hk i.2 (by omega))
lemma source_rotate (hp:∀ i<k,Backs S (fun v=> pin (F v) i)) (i:ℕ)(h:i<k) : Backs S (fun v=> pin (Resetter.rotate (F v)) i):= by
   induction i using Nat.strongRecOn with| _ i ih=>
   by_cases he:i=0; · subst i; simp_rw [show ∀ (p:PowerSeries ℝ), pin (Resetter.rotate p) 0=1 from rotate_zero]; apply Backs.given
   let P v:= Resetter.rotate (F v); have hw (t:ℕ)(ht:t < i) : Backs S (fun v=>pin (P v) t):= ih t ht (ht.trans h); let M v:=gap (P v) (P v) i; let X v:= Resetter.gap (F v) (P v * P v) i; let Qq v:= pin (F v) i + (M v+X v); have hh (p:PowerSeries ℝ) : PowerSeries.mk (pin p)=p:= PowerSeries.ext fun j=> (coeff_mk _ _); simp_rw [Resetter.rotate_pin _ i (Nat.pos_of_ne_zero he),Resetter.relative,hh]; change Backs S (fun i=> -(Qq i)/2); rw [show (fun i=> -(Qq i)/2)= (fun i=> Qq i*(-1/2)) from funext fun i=> by ring]; exact Backs.mul (Backs.add (hp i h) ( (source_gap hw hw).add (source_gap (fun j hj=> hp j (hj.trans h)) (source_m hw hw)))) (Backs.given _)
-- proves Funds for arbitrary gauges/regulators with input signatures, pin reexpression
lemma source_pin (hp:∀ i<k,Backs S (fun v=> pin (F v) i)) (i j) (h:j < k): Backs S (fun v=> charge (F v) i j):= source_m hp (source_pow (source_rotate hp) i) j h -- implicit
variable (T:e.License S ζ) (hk:3≤k)
include T hk
lemma snip {b:ℝ}{F:Field (Fin 2) (Node (Dye G))}(h:Rooted (bath ζ k _) F b): ‖salvia G e.x F‖ ≤ b := Lumen.cash_salvia e.x (h.weaken (monoTerrace (by omega) le_rfl) le_rfl) T.light
lemma mintBack (F: Word→Field (Fin 2) (Node (Dye G))) (h: Fleet S (bath ζ k _) F): Backs S (fun p=>salvia G e.x (F p)):= by
   obtain ⟨⟨p,hp,H⟩,q,hq,U⟩:=h; refine ⟨⟨p,hp,fun x hx=> e.snip T hk (H _ hx)⟩,q,hq,fun p q u hi hj he=> ?_⟩; dsimp only; rw [←Oasis.charge_minus e.x T.light T.light ((H _ (he.append hi)).weaken bath_terrace le_rfl) ((H _ (he.append hj)).weaken bath_terrace le_rfl)]; exact e.snip T hk (U p q u hi hj he)
lemma ceiling_pin (hs:s∈S) (h: e.Last (S:=S) (ζ:=ζ) k i (r+2)) : ∀ j < i,Backs S (fun v=> pin (sink e.x (e.kickoff v s)) j):= by
   intro j hj; simp_rw [pin,sink,PowerSeries.coeff_mk]; by_cases h0:j=0; · simp_rw [if_pos h0]; apply Backs.given
   simp_rw [if_neg h0]; exact mintBack _ T hk _ ((h j 2 (Or.inl hj)).ofU s hs)
omit T hk
abbrev loft (i v l:ℕ)(r:ℕ):= ticker (sink e.x (kickoff e p s)) l (i-v) • dazzle (e.port (s::p)) l r -- generic
-- v=r
abbrev Yat (r i:ℕ):= if r=0 then (Finset.range (i-r)).erase 0 else Finset.range (i-r)
def paid (i r:ℕ) := (∑ l∈ Yat r i,loft e p s i r l (r+2))+ flare G i (r+2)
-- Q withdrawal
private def remit (Y:Field (Fin 2) (Node (Dye G))) : (r:ℕ)→Field (Fin (r+2)) (Node (Dye G))→Field (Fin (r+2)) (Node (Dye G))
  | 0=> fun X=> X - salvia G e.x X • Y
  | _+1=> id
def withdraw (r:ℕ):= remit e (e.port (s::p) 0 2) r
lemma loft_scope (he:r ≤ i) : let V:=e.port (s::p); let U:=e.kickoff p s; V i (r+2)= U i (r+2)-∑ l∈Finset.range (i-r), loft e p s i r l (r+2):= by
   intro V U; unfold loft; change _=_-∑ l∈Finset.range (i-r), ticker _ l (i-r) • dazzle V l (r+2); have hh : V=lowerHouse (sink e.x U) U:= e.pore p s; rw [hh]; simpa only [show i+2-(r+2) = i-r from by omega ] using translated (sink e.x U) U (show r+2 ≤ i+2 by omega) (sink_mast _) -- check order
lemma withdrawn  (hp:i≠0) (he:r ≤ i) : let U:=e.kickoff p s; e.dust (s::p) i (r+2)=e.withdraw p s r (U i (r+2))-e.paid p s i r:= by
   intro U; unfold dust; rw [Pi.sub_apply,Pi.sub_apply]; cases r with
   | zero =>
     let V:= e.port (s::p); let l:ℕ→Field (Fin 2) (Node (Dye G)):= fun l=>loft e p s i 0 l 2; have hi:0 ∈Finset.range i:=Finset.mem_range.mpr (Nat.pos_of_ne_zero hp)
     have hv: l 0= salvia G e.x (U i 2) • V 0 2:= by unfold l loft ticker Resetter.charge pin U V; rw [Nat.sub_zero,Nat.sub_zero,pow_zero,mul_one,sink,coeff_mk,if_neg hp]; rfl
     suffices hz: V i 2= U i 2 - (l 0+ (∑ k ∈(Finset.range i|>.erase 0), l k)) by
        rw [hv] at hz; change V i 2 - _= U i 2-salvia G e.x (U i 2) • V 0 2 - ((∑ k∈ (Finset.range i|>.erase 0),l k)+_); rw [hz]; abel
     rw [add_sum_erase (Finset.range i) l hi]; exact e.loft_scope p s he
   | succ r=>
      have hz:= e.loft_scope p s he; change e.port (s::p) i _ - _= e.kickoff p s i _- (_+ flare G i _); rw [show e.port (s::p) i (r+1+2)=_ from hz]; simp only [Yat, Nat.add_eq_zero_iff, one_ne_zero, and_false,↓reduceIte]; abel -- change sees sum
def coin (k:ℕ) := 1+ share e.T G e.J k
lemma coin_pos (k:ℕ):1 ≤ e.coin k := le_add_of_nonneg_right (sharing ..).le
include T hk
lemma strictTick (h: e.Last (S:=S) (ζ:=ζ) k i (r+2)) (hs:s∈S): Fleet S (bath ζ k _) (fun p=> e.paid p s i r) := by
   unfold paid; refine Fleet.add (ι:=Fin (r+2)) ?_ (flare_q ..); apply Fleet.sum; intro l hl; have he : l < i-r ∧ (r=0→l≠0):= by unfold Yat at hl; split at hl; rw [Finset.mem_erase,Finset.mem_range] at hl; exact ⟨hl.2,fun _=> hl.1⟩; rw [Finset.mem_range] at hl; tauto
   have hv : Oasis.Past i (r+2) (l+(r+2)-2) (r+2):= (by unfold Oasis.Past; omega)
   apply Fleet.scale (p:=fun v=> ticker (sink e.x (e.kickoff v s)) l (i-r)) (f:=fun v=> dazzle (e.port (s::v)) l (r+2)); exact source_pin (e.ceiling_pin s T hk hs h) l _ (by omega)
   simp_rw [dazzle,if_pos (show 2≤ l+(r+2) by omega)]; exact Fleet.next (h _ _ hv).ofPort _ hs
lemma withdraw_asset (h:OK S (s::p)){F:Field (Fin (r+2)) (Node (Dye G))}(ht:Rooted (bath ζ k _) F b): Rooted (bath ζ k _) (e.withdraw p s r F) (e.coin k*b):= by
   cases r
   · let H:=e.port (s::p); let t:=share e.T G e.J k; let u:= H 0 2; let v:=salvia G e.x F; refine (ht.sub ((old_fee T k h).smul v)).weaken (fun _=>le_rfl) ?_; have hh: ‖v‖≤b:= e.snip T hk ht; refine (add_le_add_right (mul_le_mul_of_nonneg_right hh (sharing ..).le) b).trans_eq ?_; unfold coin; ring
   exact ht.weaken (fun _=>le_rfl) (le_mul_of_one_le_left ht.cash (e.coin_pos ..))
omit hk in
lemma withdraw_sub {c:ℝ}{F U:Field (Fin (r+2)) (Node (Dye G))}(hf:Rooted (bath ζ k _) F b)(hp:Rooted (bath ζ k _) U c): let t:=e.withdraw p s r; t (F-U)=t F-t U:= by
   cases r; · intro t; unfold t withdraw; rw [remit]; dsimp only; rw [Oasis.charge_minus e.x T.light T.light (hf.weaken bath_terrace le_rfl) (hp.weaken bath_terrace le_rfl),sub_smul]; abel
   intro; rfl
lemma withdraw_d (hs:s∈ S){F:Word→Field (Fin (r+2)) (Node (Dye G))}(h:Will S (bath ζ k _) F): ∃ b≥0,∀ p q u,OK S p→ OK S q → OK S u → Rooted (bath ζ k _) (e.withdraw (u++p) s r (F (u++q))-e.withdraw (u++q) s r (F (u++q))) (b*mileage u):= by
   cases r; swap; · refine ⟨_,le_refl 0,fun p q u hi hj hu=>by simp only [withdraw,remit,id_eq,sub_self,zero_mul]; apply Rooted.tranquility⟩
   obtain ⟨p,hp,hQ⟩:=h; obtain ⟨f,hf,hA⟩:= (Fleet.next (roots T k).ofPort s hs).2; refine ⟨_, mul_nonneg hp hf,fun i j u hi hj hk'=>?_⟩; let v := salvia G e.x (F (u++j)); let z n:=e.port (s::u++n) 0 2; change Rooted _ (F (u++j) - v • z i -(F (u++j)- v • z j)) _; rw [show F (u++j)- _-(F (u++j)- _) = -(v • (z i-z j)) from (by rw [smul_sub]; abel),mul_assoc]; let H:= hA i j u hi hj hk'; exact ((H.smul v).neg).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right (e.snip T hk (hQ _ (hk'.append hj))) H.cash)
end Parcel
end
end YM.Contacts.Prairie
