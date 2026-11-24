import YM.FVA2.O.Fusion.Reads
/-!
# Negative log-scale: work with the weaker `Grant` prices

Still retains momentum derivative estimates. Includes `Thin.left` and `Thin.right`,
showing preservation of the strong (arbitrary-decay) price under taking products
with weaker bounds on the other factor. Useful for working with shifted multipliers.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse
open scoped Topology ContDiff Interval
variable {G:Gauge} {I E W:Type} {B:Deck G}{K:Booked B}{M:MS_Data G K}{q r:ℤ}{S:Scale I}{U V:I→ Law G}{a b:I→ℝ}
abbrev stamp (S:Scale I)(q:ℤ): I→ℝ:= fun i=> S.length i ^ q
lemma posS (i:I) : 0< stamp S q i:= zpow_pos ( S.pos i ) _
def Grant (S:Scale I)(U:I→Law G)(a:I→ℝ): Prop := ∀ (E:Type)[NormedAddCommGroup E][ NormedSpace ℝ E ],∀ w:Wire (BH G) E QP, Costs S.full (Job.single I) (Chart U w) (fun i (_:E)=> Qbud w S a i)
lemma fallen (h:Latch.Lease false false S U a)(hp:∀ i,S.length i≤1): Grant S U a:= by
    intro E _ _ w; obtain he:= h E w (fun i=>Bool.noConfusion i) (fun i=>Bool.noConfusion i); refine ⟨ he.smooth,fun j=> (he.quoted j).right (fun i p hx=>?_ )⟩; rw [Job.cw,one_pow]; exact mul_le_mul_of_nonneg_left (pow_le_one₀ ( S.pos i ).le (hp i)) (he.nonneg i p hx)
lemma recovery (h:∀ q:ℤ, Grant S U ( stamp S q )): Latch.Lease false false S U (stamp S q):= by
    intro E _ _ w _ _; refine ⟨ ( h q E w ).smooth, fun j=> ?_⟩; apply ( h (q+j) E w |>.quoted j ).right; intro i p _; unfold Qbud stamp; simp_rw [zpow_add₀ ( S.pos i ).ne', Job.cw,zpow_natCast,one_pow,mul_one,mul_assoc]; rfl
lemma grant_prime (h: Grant S U a)(hv: Grant S V a): Grant S (U+V) a:= fun E _ _ w=> Costs.add (h E w) (hv E w)
lemma grant_neg (h:Grant S U a): Grant S (-U) a:= fun E _ _ w=> Costs.neg ( h E w )
lemma grant_scale (h:Grant S U a)(c:ℂ) : Grant S (c • U) a:= fun E _ _ w=> Costs.L ( ContinuousLinearMap.mul ℝ ℂ c ) (h E w)
lemma grant_zero (h:Latch.nn a): Grant S (0:I→Law G) a:= fun _ _ _ _=> Costs.zero fun i _ _=> mul_nonneg ( length_p (S:=S) _ i ) (h i)
lemma grant_pull (h:Grant S U a)(ht:∀ i,a i≤b i): Grant S U b:= fun E _ _ w => Costs.raise ( h E w ) (Cost.of_le fun i _ _=> mul_le_mul_of_nonneg_left ( ht i ) (length_p (S:=S) (pitch w) _))
variable [NormedAddCommGroup E][NormedSpace ℝ E]
lemma gather {D:Type}(p:Sector D)(w:Legs D)(f:I→E→Shared D ℂ)(h:∀ l r,Split l r w→ Costs S.full (Job.single I) (fun i x=> f i x l r) (fun i _=>a i)) : Costs S.full (Job.single I) (fun i x=>scatter p w ( f i x )) (fun i _=>a i) := by
    induction w generalizing f with| nil=> exact h _ _ .nil| cons i w ih=> exact ih ( fun u x l r=> f u x ( i::l ) r + Koszul.cross (p i) (degree p l)* f u x l ( i::r ) ) ( fun l r hp=> ( h _ _ hp.left ).add ( Costs.L ( ContinuousLinearMap.mul ℝ ℂ (cross ..)) ( h _ _ hp.right ) ) )
lemma grant_prod (h:Grant S U a)(he:Grant S V b) : Grant S (fun i=>product (field Landau.parity) (U i) (V i)) (a*b) := by
    intro E _ _ w; unfold Chart; simp_rw [scattered,sail_scatter]; apply gather; intro l r hp; convert ( ( h E l ).mul ( he E r )) using 1; rfl; ext i p; unfold Qbud; rw [← w_mass hp,zpow_add₀ ( S.pos i).ne']; dsimp only [Pi.mul_apply]; ring
lemma grant_re (h:∀ i,S.length i≤1)(he:r≤q)(hv:Grant S U (stamp S q)): Grant S U (stamp S r):= grant_pull hv (fun i=> zpow_le_zpow_right_of_le_one₀ ( S.pos i) ( h i ) he)
lemma grant_tilt {p:I→QP}(h:Grant S U a)(hp:paid S (fun i=>‖p i‖) 1): Grant S (fun i=> chair G (p i) (U i)) a:= by
    intro E _ _ w; unfold Chart; simp_rw [seated,sail_net ]; exact pulse_bill ( K:=S.full ) (V:=p) (net w) (h E w) (paid_at hp (fun _ => zero_le_one))
abbrev Royal (S:Scale I)(F:I→ Law G) := ∃ q:ℤ, Grant S F (stamp S q)
lemma Royal.add (H:∀ i,S.length i≤1)(h:Royal S U)(hp:Royal S V): Royal S (U+V):= by obtain ⟨a,h⟩:=h; obtain ⟨b,hb⟩:=hp; exact ⟨min a b,grant_prime (grant_re H (min_le_left ..) h) (grant_re H (min_le_right ..) hb)⟩
lemma r_zero : Royal S (0:I→Law G):= ⟨0, grant_zero fun _=>posS _|>.le⟩
lemma r_smul (h:Royal S U)(x:ℂ): Royal S (x • U):= by obtain ⟨q,h⟩:=h; exact ⟨_, grant_scale h x⟩
lemma stampA : stamp S (q+r)= stamp S q*stamp S r:= funext fun i=> zpow_add₀ (S.pos i|>.ne') q r
lemma Royal.P (h:Royal S U)(he:Royal S V): Royal S (fun i=>product (field Landau.parity) (U i) (V i)):= by obtain ⟨q,h⟩:=h; obtain ⟨r,hp⟩:= he; exact ⟨ q+r,(stampA|>.symm) ▸ grant_prod h hp⟩
def Thin (S:Scale I)(F:I→Law G): Prop:= ∀ q:ℤ,Latch.Lease false false S F (stamp S q)
lemma Thin.zero : Thin S (0:I→Law G) := fun _=> Latch.Lease.zero fun _=>posS _|>.le
lemma Thin.add (h:Thin S U)(he:Thin S V): Thin S (U+V):= fun v=>( h v ).plus (he v)
lemma Thin.sub (h:Thin S U)(he:Thin S V): Thin S (U-V):= fun v=>( h v ).minus (he v)
lemma Thin.scale (h:Thin S U)(c:ℂ): Thin S (c • U):= fun q=> ( h q ).cash c
lemma Thin.left (h:∀ i,S.length i≤1)(hp:Thin S U)(hx:Royal S V): Thin S (fun i=>product (field Landau.parity) (U i) (V i)):= fun _=> recovery fun q=> by obtain ⟨r,hv⟩:= hx; convert ( stampA.symm ▸ grant_prod ( fallen ( hp (q-r) ) h ) hv : Grant S _ ( stamp S (q-r+r))) using 1; rw [sub_add_cancel]
lemma Thin.right (h:∀ i,S.length i≤1)(hp: Thin S V)(hx: Royal S U): Thin S (fun i=>product (field Landau.parity) (U i) (V i)):= fun _=> recovery fun q=> by obtain ⟨r,hv⟩:=hx; convert ( stampA.symm ▸ grant_prod hv ( fallen ( hp (q-r) ) h ) : Grant S _ ( stamp S (r+(q-r)))) using 1; rw [add_sub_cancel]
end YM.FVA2.O.Cool
