import YM.FormalBulk08.Hay.Cone

/-! Low-order effective-action reconciliation INCLUDING rollover.
 Does not imply an actual scalar saddle rate. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Hay
open Filter Set Function MeasureTheory Lattice RG Exterior Wilson Precision Tree Work.F05
open Stationary hiding shine Rays
open Reef Series Wick Jets Orb Plait PowerSeries Lava Mesa Broc City Cork Lotus Shore Gorge Laurent Bloch Flat Next.Free Bank Wine
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{K:KernelChoices}{m:ℕ→Side}{p q:Clip}{R U:PathData G}{σ Γ Λ B C γ η E D α:ℝ}{j t r e:ℕ}
lemma cap_alive {T:Pot G}(h:FloatK T)(e):T e 1=0:= by
    refine lost_one (h.civil _ _) (fun s w=> ?_); obtain ⟨s',b,hb,P⟩:= h.fare e 1;
    apply City.coastline s (T e 1) (stone T) e _ (.of_forall fun n=> h.civic n s 0) w; simp_rw [h.flower e 1 0]; exact (Bank.stable hb.le (h.civil _ _) P _).1
lemma ledger {T V:Pot G}(hp:FloatK T)(hx:FloatK V)(h:∀ i,i≤2→ T i (i+2)=V i (i+2))(he:T 2 2=V 2 2): ∀ i:ℕ,i≤2→ T i=V i:= by
    intro i hi; funext j; by_cases hh: j=1
    · rw [hh,cap_alive hp,cap_alive hx]
    by_cases h0:j=i+2
    · rw [h0,h _ hi]
    by_cases hH:i=2 ∧ j=2
    · rw [hH.1,hH.2,he]
    rw [show T i j =0 from ?_, show V i j=0 from ?_]
    swap;· by_contra z;have he:=hp.valence i j z;omega
    by_contra z; have he:= hx.valence i j z;omega
lemma diary {T V:Pot G}{t:ℕ}(h:∀ i≤ t,T i=V i)(n:Side): Through t (stone T n) (stone V n):= by intro i hi; simp_rw [sow_coeff,sow,h i hi]
lemma stamp_shine {V:Pot G}(H U:Pence)(h:Fresh H)(hp:Fresh U)(hv:Vivid V)(e:ℕ): stamp H U V e (e+2)= V e (e+2):= by
    rw [stamp,Finset.sum_eq_single e];
    · rw [bill,tsub_self,show coeff 0 (H^e*U^(e+2))= (1:ℝ) from (Fresh.mul (h.pow e) (hp.pow (e+2))),one_smul]
    · intro i hi hz; have hE: V i (e+2)=0:= by by_contra z; have he:=hv.valence i _ z;rw [Finset.mem_range] at hi;omega
      rw [hE,smul_zero]
    simp
lemma stamp_wire {V:Pot G}(H U:Pence)(h:Fresh H)(hp:Fresh U)(hv: Vivid V):
     stamp H U V 2 2= V 2 2+bill H U 2 0 2 • V 0 2:= by
    let W:=bill H U; unfold stamp
    have he: bill H U 2 2 2=1:= Fresh.mul (h.pow _) (hp.pow _)
    have hz: V 1 2=0:= by by_contra z; have he':=hv.valence 1 2 z;omega
    simp [Finset.sum_range_succ,hz,he,add_comm]
lemma checks_wire (a:hue G){H V:Pot G}(h:FloatK H)(_:FloatK V)(hQ:value a (H 2 2)=0)(hp:value a (V 2 2)=0)(b:ℝ)(he:value a (H 0 2)=1)(ht: V 2 2=H 2 2+ b • H 0 2): H 2 2=V 2 2:= by
   let H₀:= (H 0 2); obtain ⟨η,C,hs,hB⟩:=h.fare 0 2;
   rw [ht,value_add (h.fare 2 2) (show Purse (b • H₀) from ⟨_,_,hs,hB.smul _⟩),hQ,value_coin,he,mul_one,zero_add] at hp; rw [hp,zero_smul,add_zero] at ht; exact ht.symm

lemma edited {T V: Pot G}(a:hue G)(hG:G.Simple){k:ℝ}(v:Train t)(hx:Story T (pink k v))(hk:0<k)(ht:4≤t)(h:Troupe V p R)(H:∀ e:ℕ,e≤2→ T e (e+2)= V e (e+2))(hp:T 2 2= V 2 2+ α • V 0 2) : coeff 2 (scalar a T)= α ∧ ∀ j≤2, (normalized a T) j=V j:= by
    have hb:value a (V 0 2)=1:=by rw [←H 0 (by omega),hx.ink,pink_weigh _ hk ht]
    have ha:value a (V 2 2)=0:= h.seals 2 a 2 le_rfl Nat.zero_lt_two
    let P:= scalar a T; let W:=normalized a T
    have hW: FrameV W (pink k v):= rulecraft_full a T hx hk ht hG
    have ht1(e:ℕ)(he:e≤ 2): W e (e+2)= V e (e+2) := (stamp_shine (bookH P) (bookU P) (book_fresh P) (book_guard P) hx.toVivid e).trans (H e he)
    obtain ⟨s,B,hs,Y⟩:=h.fare 0 2
    refine ⟨?_,ledger (T:=W) { hW with } h.toFloatK ht1 ?_⟩
    · rw [scalar,coeff_mk,hp,value_add (h.fare 2 2) (show Purse (α • V 0 2) from ⟨_,_,hs,Y.smul _⟩),ha,value_coin,hb,zero_add,mul_one]
    symm; refine checks_wire a h.toFloatK {hW with} ha (Sane.frame hW 2 a 2 le_rfl (by omega)) (α + bill (bookH P) (bookU P) 2 0 2) hb ?_
    change stamp (bookH P) (bookU P) _ 2 2=_; rw [stamp_wire _ _ (book_fresh P) (book_guard P) hx.toVivid,hp,H 0 (by omega), add_assoc,add_smul]
section reset
variable (P:Flight j t)(T:Lodge P.patch)(W:Pot G)(ρ:ChartRatio G)(h:P.patch.Branches K G)
variable (F : ∀ i:ℕ, Bid.Dir G (m i) → AxisChart G (Reef.floor K P T (m i)))
variable (hm:Tendsto m atTop atTop)(ht:4≤ t)(hr:LocalRatio ρ)
    (hb: R.Bounds p σ B C)(hU:U.Bounds q η E D)(hy:Story W (pink K.penalty P.wing))(hx:∀ i,Through 2 (stone W (m i*P.patch.L)) (novel p R _))
    (H:∀ i,Critical (S:=primary P.patch K (m i)) (Reef.floor K P T (m i)) p R (F i))(hs:G.Simple)
    (hF:∀ i,ClassicalMatch (S:=primary P.patch K (m i)) (Reef.floor K P T (m i)) p q R U (F i))(hf:∀ i,FiniteBound (S:=primary P.patch K (m i)) (Reef.floor K P T (m i)) R U p q α ρ (F i) Γ γ Λ)(hg:0<γ)
include hm F ht hr hb hU hy hx H hs hF hf hg
lemma reset (a:hue G)(M:Pot G)(hM:Troupe M q U) : coeff 2 (scalar a (waken P T W ρ h)) =α ∧ ∀ i≤2,(Aster.taxi ρ a P T h W) i=M i:= by
   have hC:=creed P T W ρ h hy ht hr
   exact edited a hs P.land hC K.penalty_pos ht hM (fun i he=>equal_spot P T W ρ h F hm ht hr hb hy hx H hs he M hM hF) (flat_fee P T W ρ h F hm ht hr hb hy hx H hs M hM hU hg hf)
end reset
end YM.FormalBulk08.Hay
