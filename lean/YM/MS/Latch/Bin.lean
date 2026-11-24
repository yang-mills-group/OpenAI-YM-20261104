import YM.MS.Latch.Home
/-!
# Change of scale transport for rents
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Latch.Job
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Belt
open scoped Topology ContDiff Interval
variable {I J E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [NormedAddCommGroup F][ NormedSpace ℝ F]{S:Scale I}{Z:Scale J}{P:I→J}{k v:ℕ}{T C:ℝ}{w:J→ℝ}{p:I→ℝ}{f:J→ E→ F}
-- point inequalities with basis-free polynomial exponent.Def tor/cEll.
abbrev paid (S:Scale I) (p q:I→ℝ): Prop:= ∃ C:ℝ,0<C∧ ∃ k:ℕ,∀ i,p i≤ C*S.basic i^k*q i
lemma paidMono {q':I→ℝ}(H:∀ i,p i≤ q' i): paid S p q':= ⟨1,zero_lt_one,0,by simpa using H⟩ -- add implicit
omit [NormedSpace ℝ E] in
lemma paid_at {x:I→ℝ}(h: paid S p x)(ht: nn x) : S.full.Le (fun i (_:E)=>p i) (fun i _=>x i):= by
    obtain ⟨C,hC,k,hK⟩:= h; refine ⟨C,hC,k,fun i p hx=>(hK i).trans ?_⟩; gcongr; · exact ht i;
    · exact ( S.basic_pos i ).le
    exact le_mul_of_one_le_right (S.basic_pos i|>.le) (S.one_le_weight i p)
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma paidStrict {x:I→ℝ}(K:I→Set E)(h:paid S p x): ( S.strict K ).Le (fun i _=>p i) (fun i _=>x i):= by obtain ⟨C,hC,k,hK⟩:=h; exact ⟨_,hC,k,fun i _ _=> hK i⟩
structure Bus (S:Scale I)(Z:Scale J)(P:I→J): Prop where
   guard : paid S (Z.basic∘P) 1
   leg: ∃ C:ℝ, 0<C ∧∀ i, Z.length (P i) ≤ C*S.length i
lemma ticket (h:Bus S Z P)(hx:Bound Z f w)(hv:paid S (w∘P) p)(he:nn p): Bound S ( fun i=> f (P i) ) p:= by
    -- use cancellation constant & cheap. produce linear exponent
    obtain ⟨A,hA,hp⟩:=h.leg; obtain ⟨C,hC,k,hB⟩:= h.guard; obtain ⟨D,hD,v,hV⟩:=hv; refine ⟨fun i=>hx.smooth (P i), fun j=>?_⟩; obtain ⟨T,hT,r,hr⟩:= hx.quoted j; let R:=(1+A)*C; refine ⟨ T*R^r*D*A^j, (by unfold R; positivity), (k+1)*r+v, fun i x _=> (hr ( P i ) x trivial ).trans ?_⟩; change T* _ *(w (P i)* _)≤_; have htT := S.full.cheap_pos (p:=x) (i:=i) trivial; let W:= S.full.cheap i x; have hW : 1≤W:= S.full.one_le i x trivial
    have h0:S.basic i ≤ W:= le_mul_of_one_le_right ( S.basic_pos i|>.le) ( S.one_le_weight i x ); have hr :0<S.basic i:= S.basic_pos i; have hl : Z.weight (P i) x ≤ (1+A)*W:= by
       have hs : Z.weight (P i) x ≤ (1+A)* S.weight i x:= by have he:= mul_le_mul_of_nonneg_right ( hp i ) (norm_nonneg x); unfold Scale.weight; have ht:= zero_le_one.trans ( S.one_le_weight i x ); unfold Scale.weight at ht; nlinarith [S.pos i, norm_nonneg x, S.one_le i]
       apply hs.trans; gcongr; exact le_mul_of_one_le_left (S.weight_pos i x|>.le) (S.one_le i)
    have hu := he i; have ht:= Z.full.cheap_pos (i:=P i) (p:=x) trivial; have hL:= Z.pos ( P i ); have hS:= S.pos i
    have hw : w (P i) ≤ D*W^v*p i := (hV i).trans (by gcongr)
    have hQ:Z.basic (P i)≤ C*W^k:= by
                                          refine le_trans (show Z.basic (P i) ≤ C*S.basic i^k from ?_) ?_; · simpa only [ Function.comp_apply,Pi.one_apply,mul_one] using hB i; -- semicolon
                                          gcongr
    have hZ : Z.full.cheap (P i) x≤ R*W^(k+1):= by
         refine ( mul_le_mul hQ hl ( Z.weight_pos _ _|>.le) (by positivity)).trans_eq ?_; unfold R; ring
    calc
       _ ≤ T*( R*W^(k+1) )^r*( D*W^v*p i* (A*S.length i)^j ):= mul_le_mul (by gcongr ) ( mul_le_mul hw (by gcongr; exact hp i) (pow_nonneg (Z.pos _).le _) (by positivity)) (by have hw : w (P i)≥0:= hx.nonneg (P i) x trivial; positivity) (by unfold R; positivity)
       _ = _ := by rw [pow_add (S.full.cheap i x) ((k+1)*r) v,pow_mul]; unfold W; ring -- gear
-- cheap extraction lemma for Arc.norm when Frame.D wrapper
end YM.MS.Latch.Job
