import YM.Contacts.Barrage.Piscine
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
open Balance PowerSeries
variable {e:Oasis G}{x:G.ColorIndex}{E:∀ n,RackCore e.a e.M n}{i j n r k l v:ℕ}{H:ℕ→ℕ→Prop}
variable {F U:ℕ→ℕ→ PowerSeries ℝ}
lemma source_m (hp:∀ i<k,Funds e H (fun v n=> pin (F v n) i))(hk:∀ i<k,Funds e H (fun v n=> pin (U v n) i))(j:ℕ)(h:j < k) : Funds e H (fun v n=> pin (F v n * U v n) j):= by
   simp_rw [pin, coeff_mul]; exact Funds.sum (antidiagonal j) fun i hi=> (hp i.1 (by have h:= mem_antidiagonal.mp hi; omega)).mul (hk i.2 (by have h:=mem_antidiagonal.mp hi; omega))
lemma source_pow (hp:∀ i<k,Funds e H (fun v n=> pin (F v n) i))(j i:ℕ)(h:i < k) : Funds e H (fun v n=> pin ((F v n)^j) i):= by induction j generalizing i with|zero=>simp_rw [pow_zero]; apply Funds.zero|succ j ih=>simp_rw [pow_succ]; exact source_m (fun i hi=>ih i hi) hp _ h
lemma source_gap (hp:∀ i<k,Funds e H (fun v n=> pin (F v n) i))(hk:∀ i<k,Funds e H (fun v n=> pin (U v n) i)) : Funds e H (fun v n=> Resetter.gap (F v n) (U v n) k):= by
   unfold Resetter.gap; apply Funds.sum; intro i hi; obtain ⟨hh,hl,ht⟩:=mem_filter.mp hi; have hv:= mem_antidiagonal.mp hh; exact (hp i.1 (by omega)).mul (hk i.2 (by omega))
lemma source_rotate (hp:∀ i<k,Funds e H (fun v n=> pin (F v n) i)) (i:ℕ)(h:i<k) : Funds e H (fun v n=> pin (Resetter.rotate (F v n)) i):= by
   induction i using Nat.strongRecOn with| _ i ih=>
   by_cases he:i=0; · subst i; simp_rw [show ∀ (p:PowerSeries ℝ), pin (Resetter.rotate p) 0=1 from rotate_zero]; apply Funds.zero
   let P v n:= Resetter.rotate (F v n); have hw (t:ℕ)(ht:t < i) : Funds e H (fun v n=>pin (P v n) t):= ih t ht (ht.trans h); let M v n:=gap (P v n) (P v n) i; let X v n:= Resetter.gap (F v n) (P v n * P v n) i; let S v n:= pin (F v n) i + (M v n+X v n); have hh (p:PowerSeries ℝ) : PowerSeries.mk (pin p)=p:= PowerSeries.ext fun j=> (coeff_mk _ _); simp_rw [Resetter.rotate_pin _ i (Nat.pos_of_ne_zero he),Resetter.relative,hh]; change Funds e H (fun i n=> -(S i n)/2); rw [show (fun i n=> -(S i n)/2)= (fun i n=> S i n*(-1/2)) from funext fun i=> funext fun n=> by ring]; exact Funds.mul (Funds.add (hp i h) ( (source_gap hw hw).add (source_gap (fun j hj=> hp j (hj.trans h)) (source_m hw hw)))) (Funds.zero _)
-- proves Funds for arbitrary gauges/regulators with input signatures, pin reexpression
lemma source_pin (hp:∀ i<k,Funds e H (fun v n=> pin (F v n) i)) (i j) (h:j < k): Funds e H (fun v n=> charge (F v n) i j):= source_m hp (source_pow (source_rotate hp) i) j h -- implicit
variable (hk:3≤k)
lemma sniff {x:G.ColorIndex} (hk:3≤k) (b:ℝ){F:Field (Fin 2) (Node (Dye G))}(h:Rooted (e.Bx k i) F b): ‖salvia G x F‖≤b:= Lumen.cash_salvia x (h.weaken (monoTerrace (by omega) le_rfl) le_rfl) (e.ξ_pos _)
lemma mintPin (x:G.ColorIndex){F:ℕ→ℕ→Field (Fin 2) (Node (Dye G))}(h:Balance.Base e H (e.Bx k) F)(hk:3≤k): e.Permit (fun i b=> ∀ n,H i n→ ‖salvia G x (F i n)‖ ≤ b):= by obtain ⟨p,hp,h⟩:=h; exact ⟨p,hp,fun i n h' => sniff hk _ (h i n h')⟩
include hk
lemma mintFull (x:G.ColorIndex){F:ℕ→ℕ→Field (Fin 2) (Node (Dye G))}(h:Balance.Stable e H (e.Bx k) F): Funds e H (fun i n=> salvia G x (F i n)):= by
   refine ⟨mintPin x h.1 hk,?_⟩; obtain ⟨⟨p,hp,hp'⟩,v,hv,hh⟩:=h; refine ⟨_,hv,fun i n m hn hm=> ?_⟩; rw [←charge_minus x (e.ξ_pos _) (e.ξ_pos _) ((hp' i n hn).weaken bath_terrace le_rfl) ((hp' i m hm).weaken bath_terrace le_rfl)]; exact sniff hk _ (hh i n m hn hm)
variable (h: e.Dawn x E k i (r+2))
include h
lemma ceiling_pin : ∀ j < i,Funds e Nat.lt (fun v n=> pin (sink x (e.entry x E v n)) j):= by
   intro j hj; simp_rw [pin,sink,PowerSeries.coeff_mk]; by_cases h0:j=0; · simp_rw [if_pos h0]; apply Funds.zero
   simp_rw [if_neg h0]; exact mintFull hk _ (h j 2 (Or.inl hj)).raw
omit h hk
variable (e x E)
-- isolate j=0 in closure for r=2; otherwise all
abbrev loft (j n i v l:ℕ)(r:ℕ):= ticker (sink x (entry e x E j n)) l (i-v) • dazzle (e.incident x E j n) l r -- generic
-- v=r
abbrev Yat (r i:ℕ):= if r=0 then (Finset.range (i-r)).erase 0 else Finset.range (i-r)
def paid (i r j n:ℕ) := (∑ l∈ Yat r i,loft e x E j n i r l (r+2))+ flare G i (r+2)
-- Q withdrawal
private def remit (Y:Field (Fin 2) (Node (Dye G))) : (r:ℕ)→Field (Fin (r+2)) (Node (Dye G))→Field (Fin (r+2)) (Node (Dye G))
  | 0=> fun X=> X - salvia G x X • Y
  | _+1=> id
def withdraw (i n r:ℕ):= remit x (e.incident x E i n 0 2) r
lemma loft_scope (j n:ℕ) (hj:j<n) (he:r ≤ i) : let V:=e.incident x E j n; let U:=e.entry x E j n; V i (r+2)= U i (r+2)-∑ l∈Finset.range (i-r), loft e x E j n i r l (r+2):= by
   intro V U; unfold loft; change _=_-∑ l∈Finset.range (i-r), ticker _ l (i-r) • dazzle V l (r+2); have hh : V=lowerHouse (sink x U) U:= e.grub x E j n hj; rw [hh]; simpa only [show i+2-(r+2) = i-r from by omega ] using translated (sink x U) U (show r+2 ≤ i+2 by omega) (sink_mast _) -- check order
lemma withdrawn (j n:ℕ)(hj:j<n) (hp:i≠0) (he:r ≤ i) : let U:=e.entry x E j n; e.dust x E j n i (r+2)=e.withdraw x E j n r (U i (r+2))-e.paid x E i r j n:= by
   intro U; unfold dust; rw [Pi.sub_apply,Pi.sub_apply]; cases r with
   | zero =>
     let V:= incident e x E j n; let l:ℕ→Field (Fin 2) (Node (Dye G)):= fun l=>loft e x E j n i 0 l 2; have hi:0 ∈Finset.range i:=Finset.mem_range.mpr (Nat.pos_of_ne_zero hp)
     have hv: l 0= salvia G x (U i 2) • V 0 2:= by unfold l loft ticker Resetter.charge pin U V; rw [Nat.sub_zero,Nat.sub_zero,pow_zero,mul_one,sink,coeff_mk,if_neg hp]; rfl
     suffices hz: V i 2= U i 2 - (l 0+ (∑ k ∈(Finset.range i|>.erase 0), l k)) by
        rw [hv] at hz; change V i 2 - _= U i 2-salvia G x (U i 2) • V 0 2 - ((∑ k∈ (Finset.range i|>.erase 0),l k)+_); rw [hz]; abel
     rw [add_sum_erase (Finset.range i) l hi]; exact e.loft_scope x E j n hj he
   | succ r=>
      have hz:= e.loft_scope x E j n hj he; change e.incident x E j n i _ - _= e.entry x E j n i _- (_+ flare G i _); rw [show e.incident x E j n i (r+1+2)=_ from hz]; simp only [Yat, Nat.add_eq_zero_iff, one_ne_zero, and_false,↓reduceIte]; abel -- change sees sum
-- inputs earlier
variable {e x E}
lemma strictTick (hk:3≤k)(h:e.Dawn x E k i (r+2)) (ht:r ≤ i) : Balance.Stable e Nat.lt (e.Bx k) (fun j n=> e.paid x E i r j n):= by
   unfold paid; refine Balance.Stable.add (ι:=Fin (r+2)) ?_ ?_; swap; · exact e.flare_fluint i (r+2) k
   apply Balance.Stable.sum; intro l hl; have he : l < i-r ∧ (r=0→l≠0):= by unfold Yat at hl; split at hl; rw [Finset.mem_erase,Finset.mem_range] at hl; exact ⟨hl.2,fun _=> hl.1⟩; rw [Finset.mem_range] at hl; tauto
   have hv : Past i (r+2) (l+(r+2)-2) (r+2):= (by unfold Past; omega); have hp:= (h _ _ hv).law;
   apply Balance.Stable.scale (F:=fun v n=>ticker (sink x (entry e x E v n)) l (i-r)) (R:=fun j n=>dazzle (e.incident x E j n) l (r+2)); · simp_rw [dazzle, if_pos (show 2≤ l+(r+2) by omega)]; obtain ⟨⟨p,hp,hq⟩,t,ht,hh⟩:=hp; exact ⟨⟨p,hp,fun v n (hn : v < n) => hq v n hn.le⟩,t,ht,fun v n w (hn : v < n) (hw : v < w)=> hh v n w hn.le hw.le⟩
   exact source_pin (ceiling_pin hk h) l _ (by omega)
lemma withdraw_asset (x:G.ColorIndex) {b:ℝ} (hk:3≤k) (h:i≤n){F:Field (Fin (r+2)) (Node (Dye G))}(ht:Rooted (e.Bx k i) F b): Rooted (e.Bx k i) (e.withdraw x E i n r F) (e.fundHat k i*b):= by
   cases r with
   | zero=>
       let H:= e.incident x E i n; let t:=share e.T G (e.J i) k; let u:= H 0 2; let v:= salvia G x F; refine (ht.sub ((e.old_enough x E n i k h).smul v)).weaken (fun _=> le_rfl) ?_; have hh : ‖v‖≤b := sniff hk _ ht; change b+ ‖v‖ * t ≤ _; refine (add_le_add_right (mul_le_mul_of_nonneg_right hh (sharing ..).le) b).trans_eq ?_; unfold fundHat; ring
   | succ => exact ht.weaken (fun _=>le_rfl) (le_mul_of_one_le_left ht.cash (e.fund_pos ..))
lemma withdraw_sub (e:Oasis G)(x:G.ColorIndex)(E:∀ n,RackCore e.a e.M n){b c:ℝ}{F U: Field (Fin (r+2)) (Node (Dye G))}(hf:Rooted (e.Bx k i) F b)(hp: Rooted (e.Bx k i) U c): let t:= e.withdraw x E i n r; t (F-U)= t F-t U:= by
   cases r; · intro t; unfold t withdraw; rw [remit]; dsimp only; rw [charge_minus x (e.ξ_pos i) (e.ξ_pos i) (hf.weaken bath_terrace le_rfl) (hp.weaken bath_terrace le_rfl),sub_smul]; abel
   intro; rfl
-- loads after value
lemma withdraw_drift (x:G.ColorIndex)(E:∀ n,RackCore e.a e.M n){F:ℕ→ℕ→Field (Fin (r+2)) (Node (Dye G))}(h:Balance.Base e Nat.lt (e.Bx k) F)(hk:3≤k): e.Permit (fun i b=>∀ n m,i<n→ i < m→ Rooted (e.Bx k i) (e.withdraw x E i n r (F i m)-e.withdraw x E i m r (F i m)) (b*e.η i (min n m))):= by
   cases r; · obtain ⟨p,hp,hq⟩:= mintPin x h hk; obtain ⟨a,ha,hA⟩:= (e.era x E k).law.2; refine ⟨_, hp.mul ha,fun i n m hn hm=>?_⟩; let x':= salvia G x (F i m); let P n:= e.incident x E i n 0 2; change Rooted _ (F i m - x' • P n - (F i m - x' • P m)) _; rw [show F i m- _-(F i m- _)= -(x' • (P n-P m)) from (by rw [smul_sub]; abel)]; let H:=hA i n m hn.le hm.le; rw [mul_assoc]; exact ((H.smul x').neg).weaken (fun _=>le_rfl) (mul_le_mul_of_nonneg_right (hq i m hm) H.cash)
   refine ⟨_,e.fair_const 0 le_rfl,fun i n m hn hm=>?_⟩; simp only [withdraw,remit, id_eq,sub_self,zero_mul]; apply Rooted.tranquility
end Oasis
end Reserve
end
end YM.Contacts.Barrage
