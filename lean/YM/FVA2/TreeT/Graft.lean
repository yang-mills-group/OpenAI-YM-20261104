import YM.FVA2.TreeT.Trial
/-!
 # Tree contraction forces: no Tad projections at the highest rank (including resonant grades)

 Momentum: first input of a tree edge always resides on net=0, not necessarily the second on these
 tested kernels. Carry this for reuse on lattice.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.FVA2.TreeT.Graft
open Function Filter Set Finset MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Heat MS.Plane.Flux MS.Landau MS.Arts MS.Arc MS.Plane.Wire MS.Book MS.Book.Convolve
open scoped Topology ContDiff Interval Classical
variable {G:Gauge}{n d r k ℓ m h q:ℕ} {A E I:Type} [NormedAddCommGroup E][NormedSpace ℝ E]
variable {M: A→ℤ}{p:Sector A}{F H:Row A E ℂ}{U:Flux A E ℂ}{x:ℂ}{u v w:ℤ}{b c:Bool}
variable {f g:ℝ→ℂ}
-- `Before` handles all integer weights (some negative) but torch at all derivative orders in the proof.
structure Before (v:ℤ)(f:ℝ→ℂ): Prop where
    smooth : ContDiff ℝ ∞ f
    start (i:ℕ): (i:ℤ)<v→ reading i f=0
namespace Before
lemma zero (v:ℤ): Before v 0:= ⟨contDiff_const,fun _ _=>by simp [reading]⟩
lemma add (hf:Before u f)(hg:Before u g): Before u (f+g):= ⟨ hf.smooth.add hg.smooth,fun i hi=> Eq.trans ( read_add hf.smooth hg.smooth ) (by rw [hf.start i hi,hg.start i hi,add_zero]) ⟩
lemma neg (hf:Before u f): Before u (-f):= ⟨ hf.smooth.neg,fun i hi=> by rw [ show -f= (fun i:ℝ=> ( -1:ℂ ) * f i ) from funext fun t=> ( neg_one_mul _ ).symm, read_const (-1) _, hf.start i hi,mul_zero ] ⟩
lemma scale (hf:Before u f)(c:ℂ): Before u (fun t=> c*f t):= ⟨ contDiff_const.mul hf.smooth,fun i H=> by rw [ read_const, hf.start i H,mul_zero ] ⟩
lemma times (hf:Before u f)(ht:Before v g)(hw:w≤u+v): Before w (fun i=> f i*g i):= by
    refine ⟨hf.smooth.mul ht.smooth,fun i H=>?_⟩; rw [read_mul hf.smooth ht.smooth]; refine Finset.sum_eq_zero (fun j hj=>?_); obtain hL:= Finset.mem_range.mp hj; by_cases hp:(j:ℤ)<u; rw [hf.start j hp,zero_mul]; rw [ht.start _ (by omega),mul_zero]
lemma nothing (hp:ContDiff ℝ ∞ f): Before 0 f:= ⟨hp,fun i hi=>by omega⟩
lemma transit (s:Finset I){f:I→ℝ→ℂ}(H:∀ i∈s, Before u (f i)): Before u (fun t=> ∑ i∈s,f i t):= ⟨ ContDiff.sum (fun i hi=> ( H i hi ).smooth),fun i hi=> by rw [ read_sum ]; exact Finset.sum_eq_zero fun j hj=> (H j hj).start i hi; exact fun j hj=> ( H j hj ).smooth ⟩
lemma menu (t:ℝ→ Shared I ℂ)(w:List I)(p:Sector I)(ht:∀ v l, Split v l w→ Before u (fun i=> t i v l)): Before u (fun x=> scatter p w (t x)):= by
    induction w generalizing t with
    | nil=> exact ht [] [] .nil
    | cons i w ih=>
       apply ih; intro v l hv; exact ( ht _ _ hv.left ).add ((ht _ _ hv.right).scale (cross ( p i ) (degree p v))) -- before addition
end Before

def Above (b:Bool)(M:A→ℤ)(u:ℤ)(n:ℕ)(F:Row A E ℂ): Prop:= ∀ w:Legs (Mode A E), Course b w→ w.length=n→ Before (u-fieldDim M w) (fieldVal F (ray w))
lemma throat (X:Wire A ℝ E): ray (sail X 1)=X:= by
    induction X with| nil=> rfl | cons i X ih=> rcases i with ⟨i,j⟩; change ray ((i,j 1)::sail X 1)=_; change (i,ContinuousLinearMap.toSpanSingleton ℝ _ ) :: ray (sail X 1)=_; rw [ih]; congr! 2; ext; simp
lemma Tilt (H:Above b M u n F)(X:Wire A ℝ E)(hx:Course b X)(hh:X.length=n): Before (u-fieldDim M X) (fieldVal F X):= by
    have he:= H (sail X 1) (sail_course (x:=(1:ℝ)) hx) (by simpa using hh); rwa [sail_dim,throat] at he
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in lemma dim_cost {l k W:Legs (Mode A E)}(h:Split l k W): fieldDim M l+fieldDim M k=fieldDim M W:= split_sum ( M∘ Prod.fst ) h

variable [Fintype A]
local notation "Π" x=> (net (x:Wire A ℝ E))
variable (hf:Above b M u n F)(hg:Above c M v d H)(hx:Reverse U p)(hF: Limit F n)(hH:Limit H d)
-- Restrict shell data to the stipulated weights.
variable (hr:∀ i j,w < M i+M j → U i j=0)(hz:∀ i j,ContDiff ℝ ∞ (U i j))
include hF hH hf hg hr hz
omit [Fintype A] in
lemma joint_slot (x:Wire A ℝ E)(t g:Wire A ℝ E)(hl:x.length+2=n+d)(ho:Course c x)(he:Split t g x)(i j:A): Before (u+v-w-fieldDim M x) (fun a:ℝ=> Heat.radius p U i j F H (sail t a) (sail g a)):= by
    let W:= ( Π t ); let L: Wire A ℝ E:= (i,-W)::t; let Y:Wire A ℝ E:= (j,W)::g; let K(a:ℝ):= (2:ℂ)*cross (p j) (degree (field p) t)* U i j (- W a)
    have h0 : (fun a:ℝ=> Heat.radius p U i j F H (sail t a) (sail g a))=(fun a=> K a *( fieldVal F L a * fieldVal H Y a )):= by funext a; unfold Heat.radius; simp only [sail_degree,sail_net,neg_neg]; unfold fieldVal L Y; rw [sail_cons,sail_cons]; unfold K W; dsimp only; rw [ neg_apply ]; ring
    rw [h0]; obtain hp' := split_length he
    by_cases ht:t.length+1=n; swap
    · rcases lt_or_gt_of_ne ht with ht|ht
      · have ht:fieldVal H Y=0:= funext fun x=> hH _ (by rw [sail_len]; unfold Y; rw [List.length_cons]; omega : (d:ℤ)< (sail Y x).length); rw [ht]; simp only [ Pi.zero_apply, mul_zero ]; exact Before.zero _
      · have ht:fieldVal F L=0:= funext fun x=> hF _ (by rw [sail_len]; unfold L; rw [List.length_cons]; omega : (n:ℤ)< (sail L x).length); rw [ht]; simp only [ Pi.zero_apply,zero_mul,mul_zero ]; exact Before.zero _
    by_cases hu: M i + M j ≤ w; swap; · rw [show K=0 from ?_]; simp only [Pi.zero_apply,zero_mul]; exact Before.zero _; funext x; exact Eq.trans (congr_arg ( ((2:ℂ)*cross (p j) (degree (field p) t)) * · ) ( congr_fun (hr i j (by omega)) ( -( W x ) ) )) ( mul_zero _ )
    obtain hk : Before 0 K:= Before.nothing (contDiff_const.mul ( ( hz i j ).comp W.contDiff.neg )); refine hk.times ( (Tilt hf L ?_ ( List.length_cons.trans ht ) ).times ( Tilt hg Y ?_ ( List.length_cons.trans ( by omega ) )) ( le_refl (u-fieldDim M L+(v-fieldDim M Y))) ) ?_; · exact fun h=> by simp [L,W]
    · exact fun h=> by unfold Y; rw [net_cons,show W+_=net x from split_net he,ho h]
    unfold L Y; simp only [field_cons]; have H:= split_sum (r:= M ∘ Prod.fst ) he; change fieldDim M t + fieldDim M g= fieldDim M x at H; omega
-- Prepare the tree estimate for use even on this auxiliary kernel.
include hx
theorem joint_wire (ht:r+2=n+d): Above c M (u+v-w) r (tree p U F H):= by
    intro x he hr'; let z:= ray x; have hZ:Course c z:= ray_course he; let y:= fieldDim M x
    unfold fieldVal tree; simp_rw [sail_scatter]; apply Before.menu (p:=field p); intro t g hp; simp_rw [Heat.convertR hx]; refine Before.transit _ (fun i hi=>Before.transit _ (fun j hj=>?_)); rw [ ← ray_dim ( m:=M) x ]; exact joint_slot hf hg hF hH hr hz _ _ _ (by rwa [ray_len,hr']) hZ hp i j
end YM.FVA2.TreeT.Graft
