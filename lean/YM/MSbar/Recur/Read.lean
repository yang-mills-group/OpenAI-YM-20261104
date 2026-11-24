import YM.MSbar.Recur.Camera
/-! Film lifts of multilinear operations. Transparency at valid fibers. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Play
open Dim Symbol Domain Diagram Scale Scale.Inertia Function Set Filter Category Counter Super Crest Deck
open scoped Classical Topology BigOperators
variable {C:Type}{W:Edition C}{c d e:Bit}{U:Set ℂ}{i k m n:ℕ} {z:ℂ} {F G:Film C}

-- apply unary without delay and with delay
def spin (A:Mono W d e) (F:Film C): Film C:= fun n=> Play.post A (F n)
def delay (A:Mono W d e)(F:Film C): Film C
    | 0=> 0
    | n+1=> Play.post A (F n)
def make (A:Poly W d e c)(F G:Film C): Film C:= fun n=> ∑ i∈Finset.antidiagonal n,twin A (F i.1) (G i.2)
lemma spin_live {A:Mono W d e}: Live W e (spin A F n z):= post_live A
lemma delay_live {A:Mono W d e}: Live W e (delay A F n z):=by cases n; exact Live.zero; exact post_live A
lemma make_live {A:Poly W d e c}: Live W c (make A F G n z):= by rw [make,Finset.sum_apply];exact Live.sum _ fun i _=> twin_live A
lemma shutter_spin (A:Mono W d e): shutter W e (spin A F) z= act (A z) (shutter W d F z):= funext fun n=> post_here
lemma shutter_delay (A:Mono W d e): shutter W e (delay A F) z= sea (A z) (shutter W d F z):= by funext n; cases n; exact nil; exact post_here
lemma shutter_make (A:Poly W d e c) : shutter W c (make A F G) z=knot (A z) (shutter W d F z) (shutter W e G z):= by
   funext v; rw [shutter, make,Finset.sum_apply, sum' (fun i hi=> twin_live A)]; exact Finset.sum_congr rfl fun i _=> twin_here
private lemma intake (h:∀ n, Live W d (F n z))(i n:ℕ): scan i (scope n) F z=(Category.read (fun v=>Scale.slope v z) i n (shutter W d F z)).val:= by
    unfold scan; simp_rw [Category.novel, Submodule.coe_sum,Submodule.coe_smul_of_tower, shutter,plug_eq (h _), Finset.sum_apply]; rfl

variable [Profit U] (hf:Ready U W d m F)(hg: Ready U W e n G)
include hf
lemma Ready.spins {A:Mono W d e} (H: Linear A): Ready U W e m (Play.spin A F):=by
    refine ⟨fun i hi=> by rw [Play.spin,hf.cutoff _ hi,post_0], ?_, ?_⟩
    obtain ⟨k,h⟩:=hf.room; exact ⟨_,fun i=> bound_linear H (h i)⟩
    intro i; refine Price.recognize (bound_linear H (hf.marks i)) ?_; intro z hz; rw [intake (fun n=>spin_live), shutter_spin, Category.read_lm,Play.post, hf.scan_apply hz i, plug_val]
lemma Ready.later {A:Mono W d e}(H: Linear A): Ready U W e (m+1) (delay A F):= by
    refine ⟨fun i hi=> ?_, ?_,?_⟩
    · cases i with | zero=>omega | succ i=> rw [delay, hf.cutoff _ (by omega),post_0]
    · obtain ⟨k,h⟩:=hf.room; exact ⟨k,fun i=> by cases i; exact Price.zero; exact bound_linear H (h _)⟩
    intro i; let q (j:ℕ)(z:ℂ):= (i.choose j:ℂ)*step 1 (i-j) z; let f(j):= times (q j) (Play.post A (scan j (scope m) F))
    have h: Regular U W e (∑ j∈scope i,f j):= Price.sum _ (fun i hi=> Price.unit (bound_linear H (hf.marks i)) ((step_diff 1 _).const_mul _))
    refine Price.recognize h (fun z hz=>?_); rw [intake (fun _=> delay_live),shutter_delay, backwards _ (fun x y=> Scale.slope_add),Finset.sum_apply]; simp only [Submodule.coe_sum,scope]; refine Finset.sum_congr rfl fun j hj=> ?_; simp [f,q,times,Play.post,step, hf.scan_apply hz]
include hg
lemma Ready.bottled {A:Poly W d e c}(H: Polarized A): Ready U W c (m+n) (make A F G):=by
    obtain ⟨B,hB⟩:=hf.room; obtain ⟨D,hD⟩:=hg.room; refine ⟨fun i hi=> Finset.sum_eq_zero fun t h=>?_,⟨B+D,fun i=> Price.sum _ fun x hx=> bound_poly H (hB x.1) (hD x.2)⟩,?_⟩ -- sum_eq_zero inference
    · obtain HH : t.1+t.2=i:=Finset.mem_antidiagonal.mp h; by_cases H:m<t.1; rw [hf.cutoff _ H,twin_zero]; rw [hg.cutoff _ (by omega), twin_nil]
    intro i; let f(j:ℕ):= (i.choose j:ℂ) • twin A (scan j (scope m) F) (scan (i-j) (scope n) G)
    have h: Regular U W c (∑ j∈scope i,f j):= Price.sum _ (fun j hj=> Price.scale (bound_poly H (hf.marks j) (hg.marks _)) _)
    refine Price.recognize h fun z hz=>?_ ; rw [intake (fun n=>make_live),shutter_make, extends_cover _ (fun x y=>Scale.slope_add) (Need hf.cutoff) (Need hg.cutoff),Finset.sum_apply]; simp only [Submodule.coe_sum,scope]; apply Finset.sum_congr rfl; intro j hj; simp [f,twin, hf.scan_apply hz, hg.scan_apply hz]
end YM.MSbar.Play
