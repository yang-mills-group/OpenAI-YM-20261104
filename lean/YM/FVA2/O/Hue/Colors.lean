import YM.FVA2.O.Hue.Tax
/-!
# Tax algebra for many orders at once
Q raises effective price grade by one.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad
open scoped Topology ContDiff
variable {E F I:Type} 
variable {G:Gauge}{I' J:Type}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{j n k:ℕ}{t b d:ℤ}{F H:Glade G I}{X Y:T (Glade G I)}{a:I→ℝ}
lemma C_add (h:Certified X M η b)(hp:Certified Y M η b): Certified (X+Y) M η b:= ⟨h.1.add hp.1,by rw [map_add,h.2,hp.2,add_zero]⟩
lemma C_sub (h:Certified X M η b)(hp:Certified Y M η b): Certified (X-Y) M η b:= ⟨h.1.sub hp.1,by rw [map_sub,h.2,hp.2,sub_self]⟩
lemma C_zero : Certified (0:T ( Glade G I )) M η b:=⟨ Response.zero,map_zero _ ⟩
lemma C_ο (s:Finset J){f:J→ T ( Glade G I )}(h:∀ i∈s,Certified (f i) M η b): Certified (∑ i∈s,f i) M η b:= by classical induction s using Finset.induction_on with| empty=> rw [ Finset.sum_empty ]; exact C_zero| insert i s hi ih=>rw [ Finset.sum_insert hi ]; exact C_add (h i (by simp)) (ih fun j hj=>h j (mem_insert_of_mem hj))
-- real coefficient functions
abbrev seat (a:I→ℝ) (X:T ( Glade G I )):= pay (fun i=> (a i:ℂ)) X
lemma C_seat (h:Certified X M η b): Certified (seat a X) M η b:= ⟨ h.1.scale a ,by rw [seat,res_cash,h.2]; funext n i; simp only [ pay,Pi.zero_apply,smul_zero ] ⟩
lemma orientR (a b:I→ℝ): seat (a+b) X=seat a X+seat b X:= by ext; simp only [ Pi.add_apply,seat,pay,Complex.ofReal_add,Pi.smul_apply,add_smul]
lemma distributeR (a:I→ℝ): seat a (X+Y) = seat a X+seat a Y:= by ext; simp only [seat,pay,Pi.add_apply,Pi.smul_apply, smul_add]
@[simp] lemma seat0 (X:T ( Glade G I )): seat (0:I→ℝ) X=0:= by funext n i; change ( (0:ℝ):ℂ) • X n i=0; rw [Complex.ofReal_zero,zero_smul]
lemma Profit.inherits (hp:Profit P.dawn a): Profit P.primary (a ∘ index):= by
    obtain ⟨C,hC,k,h⟩:= hp; refine ⟨C,hC,k,fun i=> (h (index i)).trans ?_⟩; simp only [ Pi.one_apply,mul_one ]; gcongr; · exact (P.dawn.basic_pos _).le;
    have hs:= P.lg (index i); linarith; exact i.ge
lemma tint (S: Scale I){X:I→Law G}{b:I→ℝ}(h:Profit S a)(hv:Latch.Lease false false S X b): Latch.Lease false false S (fun i=> (a i:ℂ) • X i) b:= by
    intro E _ _ w hw hb; obtain hp : Bound S (E:=E) (fun i _=> a i) 1:= Costs.scalar ( paid_at h ( fun i=>zero_le_one ) ); convert Costs.smul hp (hv E w hw hb) using 1 -- Cape/real scalar
    rfl; ext; simp
lemma home_price (hh:P.beg=0)(hp:Reps X d P)(n:ℕ): prime P (X n):= by
    intro E _ _ w hw hc; have hV:Bus P.dawn P.primary P.start:= ⟨ ⟨1,zero_lt_one,1,fun i=>by simp only [ Function.comp_apply,Pi.one_apply,pow_one,mul_one,one_mul]; exact le_rfl⟩,1,zero_lt_one,fun i=>le_of_eq (by rw [one_mul]; rfl ) ⟩; have he:=ticket (p:=1) hV (hp n E w hw hc) ( paidMono ( fun i=> by simp only [ Function.comp_apply, t, start, hh, Pi.zero_apply,exp_zero,one_zpow,mul_one ]; exact le_rfl ) ) (fun _=>zero_le_one); unfold Cape; convert! he using 1; · funext i p; simp only [Chart,sweep,index,start,t, hh,Pi.zero_apply];
    ext i; simp [hh]
lemma RVA (hp: allowance P η)(hx: Response X M η b)(hV:Reps X t P): Reps (nav M η X) (t+1) P := by
    intro i; apply Latch.Lease.sticks ( B_life (P:=P) ( hx.life i|>.cross ) hp ( fun i=> length_p .. ) (hV i) (fun j _=> hV j)); intro i; unfold die; simp only [Pi.mul_apply, neg_add_rev,zpow_add₀ (P.primary.pos i).ne',zpow_neg_one, le_refl ]
lemma Reps_desc (he:Reps X t P)(h:d≤t): Reps X d P:= by
    intro n; refine Latch.Lease.sticks (he n) (fun i=>?_); exact zpow_le_zpow_right₀ ( Real.one_le_exp ( (P.beg_nn _).trans i.ge ) ) ( neg_le_neg h )
lemma Reps_add (h:Reps X t P)(h':Reps Y t P): Reps (X+Y) t P:= fun i=> Latch.Lease.plus (h i) (h' i)
lemma Reps_profit (h:Profit P.dawn a)(hv:Reps X t P): Reps ( seat a X ) t P:= fun i=> tint P.primary h.inherits ( hv i )
lemma Reps_zero : Reps (0:T ( Glade G I )) t P:= fun _=> Latch.Lease.zero fun _=> length_p ..
lemma Reps_sum (s:Finset J){f:J→ T ( Glade G I )}(h:∀ i∈s,Reps (f i) t P): Reps (∑ i∈s,f i) t P:= by classical induction s using Finset.induction_on with| empty=> rw [ Finset.sum_empty ]; exact Reps_zero| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact Reps_add ( h i (by simp)) ( ih fun j hj=> h j (mem_insert_of_mem hj) )
end YM.FVA2.O.Hue
