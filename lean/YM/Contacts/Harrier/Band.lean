import YM.Contacts.Harrier.First
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Prairie
open Cartons Font Pierian Planned.PrimaryIntegral295 Place Carrier MultiNext.SignedSource Pattern Tensor Barrage.Reserve.Oasis Analysis
-- Strict band's masses invariant modulo all lower bands
variable {H K: Field (Fin k) (Node (Dye G))} {x:Dye G}
local notation "I" => Fin k → Node (Dye G)
local notation "F" => (Axis→G.Color)
abbrev book (K: Field (Fin k) (Node (Dye G)))(V:Fin k → plate G)(i:I) := K i * ∏ j:Fin k, sense (G:=G) (V j) (i j)
abbrev fieldSay (K: Field (Fin k) (Node (Dye G)))(V:Fin k → plate G) := tsum (book K V)
variable (hs:0<ζ) (ht:Rest (terrain ζ _) (0,x) H b)
include hs ht
lemma account (V:Fin k→ plate G)(j:ℕ)(hv:∀ i,V i∈ rangeLt F j): Summable (book H V):= by
   obtain ⟨a,ha,H'⟩:= Pierian.toast j V hv; let f:=a*Shuttle.hail (j*k) (ζ:ℝ); have hf:0≤f:= by unfold f Shuttle.hail; positivity
   refine Summable.of_norm ((budget_scale hf ht).2.1.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>?_ )); unfold book; rw [norm_mul]; exact (mul_le_mul_of_nonneg_left (H' ζ x i hs) (norm_nonneg _)).trans_eq (mul_left_comm ..)
variable (hb:∀ j<h,Remains j H)
include hb
lemma placing (P Q:Fin k→ plate G)(n:Fin k→ℕ)(hn: ∑ i,n i=h)(hv:∀ i,1≤ n i)(hm:∀ i,P i ∈ rangeLt F (n i))(hr:∀ i,Q i∈rangeLt F (n i))(he:∀ i, P i-Q i∈ rangeLt F (n i-1)):fieldSay H P=fieldSay H Q := by
   let U(p:Finset (Fin k)) (i:Fin k):= if i∈p then P i else Q i
   have hu (p: Finset (Fin k)) (i:Fin k): U p i∈rangeLt F (n i):= by unfold U; split; exacts [hm i,hr i]
   suffices he : ∀ p:Finset (Fin k),fieldSay H (U p)=fieldSay H Q by exact Eq.trans (congr_arg _ (show P=U univ from funext fun i=>by simp [U])) (he _)
   intro p; induction p using Finset.induction with| empty=>simp only [U,Finset.notMem_empty,↓reduceIte]|insert i p ha ih=>
   let v:=insert i p; let f i:=U v i; let g i:=U p i; have hx:P i-Q i ∈rangeLt F (n i-1):=he i; have hg: g i=Q i:=if_neg ha; have hf:f i=P i:= if_pos (mem_insert_self ..); have hw(k:Fin k)(hk:k ≠ i): f k=g k:= by by_cases hh:k∈p <;> simp [v,U,f,g,hk,hh];
   let V:= update g i (P i-Q i); have hp (p):Summable (book H (U p)):= account hs ht _ h (fun i=> Place.grows F (le_trans (single_le_sum (s:=univ) (f:=n) (fun i _=> Nat.zero_le (n i)) (mem_univ _)) hn.le) (hu p i));
   apply Eq.trans ?_ ih; apply sub_eq_zero.mp; by_cases ht:1 < n i; swap; · change fieldSay H f-fieldSay H g=0; rw [show f = g from funext fun j=>?_]; rw [sub_self]; by_cases he:j=i; subst j; rw [hf,hg]; refine sub_eq_zero.mp (Submodule.mem_bot ℝ|>.1 (?_)); rw [show (⊥: Submodule ℝ (E4→F))=rangeLt F (n i-1) from (by rw [show n i-1=0 from by omega]; rfl)]; exact hx; exact hw _ he
   have hV: fieldSay H V=0:= by
      let l:= update n i (n i-1); refine hb (h-1) (by have hz: n i≤ h:= (single_le_sum (f:=n) (s:=univ) (fun i _=>Nat.zero_le (n i)) (mem_univ _)).trans hn.le; omega) V l (fun j=>?_ ) (fun j=>?_ ) ?_ -- implicit
      · by_cases hj:j=i; subst j; unfold l; rw [update_self]; omega; unfold l; rw [update_of_ne hj]; apply hv
      · by_cases hj:j=i; subst j; simpa only [V,l,update_self] using hx; unfold l V; rw [update_of_ne hj,update_of_ne hj]; apply hu
      rw [←add_sum_erase _ l (mem_univ i),show l i=n i-1 from update_self ..,←hn,← add_sum_erase _ n (mem_univ i),show (∑ j∈univ.erase i,l j)=∑ j∈univ.erase i,n j from sum_congr rfl fun j hj=>update_of_ne (mem_erase.mp hj).1 _ _]; omega
   rw [show fieldSay H (U (insert i p))-fieldSay H (U p)= ∑' v, (book H f v-book H g v) from ((hp v).tsum_sub (hp p)).symm, ← hV]; apply tsum_congr; intro x; unfold book; have hz (t:Fin k→plate G): (∏ j,sense (G:=G) (t j) (x j))= sense (G:=G) (t i) (x i)*(∏ j∈univ.erase i,sense (G:=G) (t j) (x j)):= (mul_prod_erase _ _ (mem_univ i)).symm; rw [hz,hz g,hz V, show V i=P i-Q i from update_self .., show sense (G:=G) (P i-Q i) (x i)=_ from (show _=sense (G:=G) (f i) (x i)-sense (G:=G) (g i) (x i) from (by rw [hf,hg]; rfl))]; let J(t:Fin k→plate G):=∏ j∈univ.erase i,sense (G:=G) (t j) (x j); have hh:J f=J g:= prod_congr rfl fun i hi=> congr_arg (fun x'=> sense (G:=G) x' _) (hw i (mem_erase.mp hi).1); have hn:J V=J g:= prod_congr rfl fun i hi=> congr_arg (fun x'=>sense (G:=G) x' _) (update_of_ne (mem_erase.mp hi).1 _ g); unfold J at hh hn; rw [hh,hn]; ring
omit hb
lemma field_minus (P:Fin k→ plate G)(n:ℕ)(hV:∀ i,P i∈ rangeLt F n)(hK: Rest (terrain ζ _) (0,x) K c): fieldSay (H-K) P=fieldSay H P-fieldSay K P:= by unfold fieldSay; rw [←(account hs ht P n hV).tsum_sub (account hs hK _ _ hV)]; exact tsum_congr fun i=> sub_mul ..
omit ht hs in
lemma field_scale (P:Fin k→ plate G)(b:ℝ): fieldSay (b • H) P=b*fieldSay H P:= by unfold fieldSay; rw [← tsum_mul_left]; exact tsum_congr fun x=> mul_assoc ..
include hb
lemma aspired (P:Parcel G)(p:Parcel.Word)(s:Parcel.Step)(h':Poem H)(hh:h≤P.J)(z:Cover) (V:Fin k→plate G) (n:Fin k→ℕ) (hv:∀ i,1≤ n i)(hb':∀ i,V i∈ rangeLt F (n i))(hq:∑ i,n i ≤ h): let T:=printRun (Trace.wreath z (install (Origin.bleed G (P.gas p s))) H); fieldSay T V=unitStep s.L ^ h * fieldSay H V:= by
    intro R; change say _ (fun i=>sense (G:=G) (V i))= _; have hp (i:Fin k) : n i ≤ h := (single_le_sum (f:=n) (fun i _=>Nat.zero_le _) (Finset.mem_univ i)).trans hq; let f:= P.path p s; let L:= s.L; let u:=unitStep L; choose Y hY T Q using fun i=> Pierian.stepping f P.ready P.K.penalty_pos ((hp i).trans hh) _ (hb' i)
    have hF: Whole (P.gas p s):= ⟨P.reach,_,NNReal.coe_pos.mpr P.reach_pos,stiff P p s⟩; let X(i: Fin k)(x:E4):= Y i (x+Place.seat z); have hx (i: Fin k): X i∈ rangeLt F (n i):= Place.band_shift (hY i) _; have hσ(q:plate G): sense (G:=G) q ∘ backpack z=sense (G:=G) (fun x=> q (x+Place.seat z)):= by funext i; change q (Place.seat (i.1+z)) _ _=q (Place.seat _+Place.seat z) _ _; rw [Place.seat_add]; rfl
    unfold R; rw [Lotus.orchid,Pierian.stride (j:=h) hF hs (staple z ht) (poetic _ h' _) V Y (fun i=> grows F (hp i) (hb' i)) Q,reign]; change say H (fun i=> sense (G:=G) (Y i) ∘ backpack z)=_; simp_rw [hσ]; change fieldSay H X =u^h * _; by_cases hz:∑ i,n i=h; swap; · rw [show fieldSay H V=0 from hb _ (lt_of_le_of_ne hq hz) V n hv hb' (le_refl (∑ i,n i)),show fieldSay H X=0 from hb _ (lt_of_le_of_ne hq hz) X n hv hx (le_refl (∑ i,n i)),mul_zero]
    let M(i:Fin k) := u^n i • V i; have hk: fieldSay H X=fieldSay H M:= placing hs ht hb X M n hz hv hx (fun i=> Submodule.smul_mem _ _ (hb' i)) (fun i=> by let a:=n i; have hX:X i-Y i ∈ rangeLt F (a-1):= Place.band_step (n:=a-1) (by rw [show a-1+1=n i from by have he:=hv i; unfold a; omega]; exact hY i) (Place.seat z); rw [show X i-M i=(X i-Y i)+(Y i - M i) from by abel]; exact Submodule.add_mem _ hX (T i));
    rw [hk]; unfold fieldSay; rw [← tsum_mul_left]; apply tsum_congr; intro i; unfold book; simp_rw [show ∀ j:Fin k,sense (G:=G) (M j) (i j)= u^n j * sense (V j) (i j) from fun j=>rfl,prod_mul_distrib, Finset.prod_pow_eq_pow_sum,hz,mul_left_comm] -- gives ?
variable {e:Parcel G}{p:Parcel.Word}{s:Parcel.Step}
lemma band_same (T:Parcel.License S e ζ)(hh:s∈S) (h':Poem H)(he:h≤e.J)(z:Cover) :
    let Y:=printRun (Trace.wreath z (install (Origin.bleed G (e.gas p s))) H)
    Remains h (Y-unitStep s.L ^ h • H):= by
    intro Y V n hn hv hz; let U:= Origin.bleed G (e.gas p s); have hw: ζ ≤ e.reach:= by apply NNReal.coe_le_coe.mp; have h:=T.warm; push_cast at h; linarith only [h,NNReal.coe_nonneg ζ]
    let G':= Origin.bleed_strip (G:=G) (s:=ζ) (strip_mono (stiff e p s) (NNReal.coe_le_coe.mpr hw) le_rfl) e.tax_pos.le; have hY: Rest (terrain ζ _) (0,x) Y _:= (Lotus.orchid U H z).symm ▸ Hinges.hoist_price x G' e.tax_pos.le (le_trans (div_le_div_of_nonneg_right (a:=(ζ:ℝ)) (NNReal.coe_le_coe.mpr T.down) (side_pos _).le) (Parcel.step_reserved s ζ)) (staple z ht)
    change fieldSay _ V=0; rw [field_minus hs hY V h (fun i=>grows F ((single_le_sum (f:=n) (fun _ _=>Nat.zero_le _) (mem_univ i)).trans hz) (hv i)) (ht.smul _), field_scale, show fieldSay Y V=_ from aspired hs ht hb e p s h' he z V n hn hv hz, sub_self]
end Transfer
end
end YM.Contacts.Harrier
