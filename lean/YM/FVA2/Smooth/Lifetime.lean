import YM.MS.Dial.Frame
/-!
# Pay for taking mark derivatives in `Rake` conventions

Multiply by the momentum operator on that mark. These are results about
formal MS primitives, not about derivatives of lattice stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Lifetime
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I E : Type}{G:Gauge}{P: Geo I}{B:Belt I}{b c:Bool}{r n:ℕ}
local notation "H"=> Law G
variable (v:Axis)
def turn (v:Axis) : QP→L[ℝ] ℂ:= (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp (Complex.ofRealCLM.comp (ContinuousLinearMap.proj v))
lemma turn_eq (v:Axis)(p:QP): turn v p= Complex.I*(p v:ℂ):= rfl -- parse I (Type)
def force (v:Axis) (F:Glade G I): Glade G I:= fun i t=> MS.Motif.moment (turn v).toLinearMap.toAddMonoidHom ( F i t )
local notation "τ"=> force v
lemma force_eq (i:I)(t:ℝ)(F:Glade G I)(l:Legs (Lane4 G)): τ F i t l= turn v (net l)*F i t l:= rfl
lemma onlyT {F:Glade G I}(h:collect F): collect (τ F):= by obtain ⟨n,h⟩:=h; refine ⟨n,fun i x y he=>?_⟩; rw [force_eq,h i _ _ he,mul_zero]
lemma budget [NormedAddCommGroup E][NormedSpace ℝ E](S: MS.Scale I)(A:E→L[ℝ] ℂ): Bound S (fun _ (x:E)=>A x) (fun i=>( S.length i )⁻¹) := by
    let C (i:I):=S.length i; have hf:= S.rescaled A.hasTemperateGrowth; have hh(i:I)(x:E): ( C i )⁻¹ • ( A ( C i • x ) )=A x:=by rw [map_smul,inv_smul_smul₀ (S.pos _|>.ne')]
    let T:=fun i (_:E)=> (C i)⁻¹; have hc: Bound S T (fun i=>(C i)⁻¹):= Costs.scalar ( Cost.of_le fun i p h=> ( Real.norm_of_nonneg (inv_nonneg.mpr ( S.pos _|>.le )) ).le ); convert! hc.smul hf using 1; funext i x; exact (hh i x).symm; funext i; exact (mul_one _).symm

-- camp is not literally Here. need analogue. factor into any Lease:
lemma hot_h (S:MS.Scale I){K:I→H}{U:I→ℝ}(h:Lease b c S K U): Lease b c S (fun i=> MS.Motif.moment (turn v).toLinearMap.toAddMonoidHom (K i)) (fun i=> (S.length i)⁻¹*U i):= by
 intro E _ _ w hw he; let C0:=turn v ∘L net w; unfold Cape Plane.Chart; simp_rw [Motif.moon,sail_net]; convert! (budget S C0).mul (h E w hw he) using 1; ext; ring
lemma costs {S:Belt I}{X:S.time→ℝ}{F:Glade G I}(h:Here b c S F X): Here b c S (τ F) (fun i=> ( S.price.length i )⁻¹*X i):= hot_h v S.price h

lemma hot {F:Glade G I}(h:Warm F b): Warm (τ F) b := by
 refine ⟨fun i T he=>?_, fun i w _=>?_⟩
 · convert (hot_h v (single (camp T)) (h.cost i T he)) using 1; rfl; simp [Job.single]; rfl
 unfold force; simp_rw [Motif.moon]; exact continuous_const.mul ( h.walk i w (by assumption) )
lemma stat (F:Glade G I)(K:Planet G I)(i:I)(t:ℝ)(l:Legs (Lane4 G)): τ (sailP (fun _=>planeF) K F) i t l= sailP (fun _=>planeF) K (τ F) i t l:= by
 rw [force_eq]; unfold sailP cycle; rw [← integral_const_mul]; refine integral_congr_ae ( Eventually.of_forall fun x=>?_ ); simp_rw [at_trc, force_eq, net_cons, ← add_assoc (a:=x), add_neg_cancel,zero_add, Finset.mul_sum ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> mul_left_comm ..
-- root-last tree with arbitrary B factor. conservation last leg. valid even off net.
lemma commuteC {p:QP→ℂ} {μ:H}{K: Edge G}{F:H}: tree Landau.parity K F (fun l=>p (net l)* μ l)= fun l=>p (net l)*tree Landau.parity K F μ l:= by
 funext l; unfold tree; let Q:= allocate (field Landau.parity) l ( R:=ℂ ); change Q _= p _ • Q _; rw [← map_smul]; apply scatter_congr; intro i j hi; simp only [ Pi.smul_apply, smul_eq_mul, attaches, neg_neg,net_cons,split_net hi, Finset.mul_sum ]; exact Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> by ring
lemma push (K:Planet G I)(F X:Rake.Site G I)(k:ℕ)(i:I)(t:ℝ)(w:Legs (Lane4 G)): (τ (lonely K F X k)) i t w=lonely K F (fun j=>τ (X j) ) k i t w:= by
 rw [force_eq ]; unfold lonely; simp only [ Finset.sum_apply, Finset.mul_sum ]; apply Finset.sum_congr rfl; intro j hj; exact congr_fun ( commuteC (p:=turn v) ).symm w
lemma venH (K L:Planet G I)(A X:Rake.Site G I)(h: Ven (fun _=>planeF) K L A X): Ven (fun _=>planeF) K L A (fun i=>τ (X i)):= by
    intro i; obtain ⟨hh,hC⟩:= h i; refine ⟨ hot _ hh,?_⟩; intro j w t; convert! (hC j w t).const_mul (turn v (net w)) using 1; simp only [Pi.add_apply,mul_add, ← push, ← stat, force_eq]; -- inspect
lemma step_price {F:Glade G I}(S:Belt I)(r:ℕ)(h: Here false c S F ( rateS S r )): Here false c S (τ F) (rateS S (r+1:ℤ)):= by convert costs v h using 1; ext i; simp only [ rateS, neg_add,zpow_add₀ ( S.price.pos i|>.ne'),zpow_neg,zpow_one]; exact mul_comm ..
lemma marks_h {F:Glade G I}(h: Tip P false false r F): Tip P false false (r+1) (τ F):= by exact ⟨ onlyT _ h.1,hot _ h.2.1,step_price v _ _ h.2.2⟩
end YM.FVA2.Smooth.Lifetime
