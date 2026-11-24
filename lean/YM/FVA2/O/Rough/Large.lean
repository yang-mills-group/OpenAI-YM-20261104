import YM.FVA2.O.Rough.Cobb
/-!
# Rough power-counting for loops (absolute values)

`Well.cycle_q`: from the full `Sheet` estimates on the propagator and the
weaker size-only bounds on a kernel, transfer bounds to the loop terms.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open scoped Topology ContDiff Interval
variable {E I J V:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {f v:I→ QP× E→ ℂ}{S:Scale I}
variable {x a b:I→ℝ}{n m:ℕ}
local notation "R"=> Set.univ (α:=QP)
-- norm version supplies j=0 only, giving full tree estimates but no derivative loss at seam.
def Buzz (S:Scale I)(f:I→ QP× E→ℂ)(p:I→ℝ): Prop:= ∀ j:ℕ, Size ( S.slow (fun _=>R)) f (fun i v=>p i / S.weight i v.1^j)
lemma noisy (h:Rapid S (fun _=>R) f x): Buzz S f x:= fun _=> (h _).norm_cost
omit [NormedSpace ℝ E] in
lemma buzz (hp:Buzz S f x)(he:Size S.full v (fun i _=>b i))(hn:nn b) : Buzz S (fun i x=> f i x*v i x) (x*b):= by
    intro j; obtain ⟨C,hC,k,h⟩:= he; have hV: Size (S.slow (fun _=>R)) v (fun i p=> S.weight i p.1^k*b i):= by
        refine ⟨ C,hC,k,fun i p _=>(h i p trivial).trans ?_⟩; calc
           _ ≤ C*(( S.slow (fun _=>R) ).cheap i p*S.weight i p.1)^k*b i:= by
              gcongr; · exact hn i
              · exact ( S.full.cheap_pos trivial ).le
              exact S.slow_weight _ _ _
           _ = _:= by rw [ mul_pow ]; dsimp only; ring
    refine Size.mon ( Size.fork (hp (j+k)) hV ) ( Cost.of_le fun i p _=>?_ ); apply le_of_eq; simp only [ pow_add, Pi.mul_apply ]; field_simp [ (S.weight_pos i p.1).ne' ]
omit [NormedSpace ℝ E] in
lemma buzz_total (s:Finset V){f: V→ I→ QP × E→ℂ}(h:∀ i∈s,Buzz S ( f i ) a)(he:nn a): Buzz S (fun i p=>∑ j∈s,f j i p) a:= fun _=> Size.tally s (fun j hj=>h j hj _) (fun i _ _=> div_nonneg (he i) (pow_nonneg (S.weight_pos ..|>.le) _))
variable {G:Gauge}{H:I→Law G}{U:I→Edge G}
lemma coast_q (h:FormP S H x true)(hx:nn x)(he:Sheet S a U)(w:Wire (BH G) E QP)(i j:BH G): Buzz S (fun p v=> U p i j v.1 * H p ( (i,v.1)::(j,-v.1)::sail w v.2 ) ) (fun i=> S.length i ^ pitch w * positive S 4 a x i):= by
    let A:= ContinuousLinearMap.fst ℝ QP E; let Q:= ContinuousLinearMap.snd ℝ QP E; let v:Wire (BH G) (QP× E) QP:= (i,A)::(j,-A)::Wire.lift w Q; obtain hp:= h (QP× E) v (fun _=>by simp [v]); convert! buzz ( noisy (Line.rapid ( he i j ) ( F:=E )) ) hp ( λ i=> mul_nonneg ( length_p (S:=S) (pitch v) _ ) ( hx i )) using 1; · funext p v'; simp only [ Chart,sail_cons, lift_sail, v, A, Q, _root_.neg_apply ]; rfl
    funext s; unfold Qbud positive pitch v; simp only [Pi.mul_apply,field_cons, field_lift]; have ht:fieldDim wfield w + (4:ℤ)=(4-wfield i-wfield j)+(wfield i+(wfield j+ fieldDim wfield w)):= by omega
    rw [ show S.length s^4= S.length s^(4:ℤ) from rfl ]; rw [ ← mul_assoc,← zpow_add₀ ( S.pos s ).ne', ht, zpow_add₀ ( S.pos s ).ne' ]; ring
lemma sphere_q (hp:FormP S H x true)(hv:nn x)(ht:Sheet S a U)(ha:nn a)(w:Wire (BH G) E QP): Buzz S (fun i p=> trc (U i) p.1 (H i) (sail w p.2)) ( Qbud w S ( positive S 4 a x )) := by
    simp_rw [at_trc]; refine buzz_total Finset.univ (fun i _=>buzz_total Finset.univ (fun j _=> coast_q hp hv ht w i j) ?_ ) ?_ <;> exact pos_nn ( positive S 4 a x ) ( np S hv ha _ ) S
omit [NormedSpace ℝ E] in
lemma consume_q (he: Buzz S f x)(hv:nn x): Size S.full (fun i p=>∫ q,f i (q,p)∂planeF) (fun i _=>x i*Snap.fee S i):= by
    obtain ⟨C,hC,k,h⟩:= he 5; obtain ⟨T,hT,m,ht⟩:= tom (E:=E) S 5 (by omega); refine ⟨ C*T,by positivity,k+m,fun i p _=>?_⟩; have hs:= S.full.cheap_pos (i:=i) (p:=p) trivial; let V:=C*S.full.cheap i p^k*x i; have hV:0 ≤ V:= by unfold V; have hy:=hv i; positivity
    apply le_trans (norm_integral_le_of_norm_le (( (Tall S 5 (by omega)).integrable i ).const_mul V ) (Eventually.of_forall fun q=>?_)); · rw [ integral_const_mul ]; refine ( mul_le_mul_of_nonneg_left (ht i p trivial) hV )|>.trans_eq ?_; unfold V; rw [pow_add]; ring
    apply le_trans ( h i (q,p) trivial ); unfold V Scale.slow Scale.dust; exact le_of_eq (by dsimp only; ring)
lemma FormP.cycle_q (hp:FormP S H x true)(hx:nn x)(ht:Sheet S a U)(ha:nn a): FormP S (fun i=> cycle (U i) planeF (H i)) (a*x) false:= by
    intro E _ _ w h; obtain hZ:= consume_q (sphere_q hp hx ht ha w) (pos_nn ( positive S 4 a x ) (np S hx ha _) S); refine Size.mon hZ (Cost.of_le fun i p _=> ?_); unfold Qbud positive Snap.fee; simp only [ Pi.mul_apply ]; exact le_of_eq (by field_simp [ (S.pos i).ne' ])
lemma Well.cycle_q (hp:Well S H x (n+2))(hx:nn x)(he:Sheet S a U)(ha:nn a): Well S (fun i=>cycle (U i) planeF (H i)) (a*x) n:= ( Well.cram (( hp.maskW hx ).part.cycle_q hx he ha) (fun i=> Bool.noConfusion i) ).takeM (fun _ _ hi=> cycle_mask _ _ hi)
end YM.FVA2.O.Rough
