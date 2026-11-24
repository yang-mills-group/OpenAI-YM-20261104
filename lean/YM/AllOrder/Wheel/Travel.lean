import YM.AllOrder.Docket.Hail
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Matrix Metric MeasureTheory ProbabilityTheory Finset
open ConnectedActivityE6 Blaze Brush Poll Local Vote Clock
open PositionX.Jet PhysicalNext Repeat Lantern
open Laplace Laplace.SigmaP PertExtension PertExtension.Series Radial Tested
open Plateau Response
open scoped Topology ENNReal BigOperators Classical ContDiff Polynomial
variable {ι:Type*}{V:ι→Type}[∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)][∀ i,FiniteDimensional ℝ (V i)]
variable {T:Clock ι}{p C s ζ b:ι→ℝ}{a c:ℝ}{f g:∀i,V i→ℝ}{x z:∀i,V i}{j l n:ℕ}
local notation "H"=> T.Meter
local notation "Ω"=>0 -- parser
namespace Cover
lemma home (h:Cover T j a p f x)(hc:∀ᶠ i in T.rail,f i=g i): Cover T j a p g x:= fun v he=> ((h v he).and hc).mono fun i hi=> hi.2 ▸ hi.1
lemma paint (h:Cover T j a p f x)(he: ∀ᶠ i in T.rail,p i=C i): Cover T j a C f x:= fun v hv=> ((h v hv).and he).mono fun i hi=> hi.2 ▸ hi.1
lemma caliber (h:Cover T j a p f x)(he:H C c): Cover T j (a+c) p (fun i=> C i • f i) x:= by
 intro e hp; let r:= (e-(a+c))/2; have hr:0<r:=half_pos (sub_pos.mpr hp); filter_upwards [T.positive,h _ (show a<a+r by linarith),he _ (show c<c+r by linarith)] with i hi hI hv; refine ((hI.smul (C i)).climb ?_ le_rfl); apply le_trans (mul_le_mul_of_nonneg_right hv (Real.rpow_nonneg hi.le _)); rw [← Real.rpow_add hi]; rw [show c+r+(a+r)=e by unfold r; ring]
lemma booking {α:Type*}{F:α→ (i:ι) → V i → ℝ} (s:Finset α) (h:∀ i∈s,Cover T j a p (F i) x)(he:∀ᶠ i in T.rail,0≤p i): Cover T j a p (fun i=>(∑ j∈s,F j i)) x:= by
 induction s using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact Cover.fixed (fun _=> (0:ℝ)) he (by simpa only [norm_zero] using Meter.nil T a)
 | insert v s hv ih=> simp only [sum_insert hv]; exact (h _ (mem_insert_self ..)).add (ih fun i hi=> h i (mem_insert_of_mem hi))
lemma prior (h:Cover T j a p f x)(hv:H (fun i=> f i 0) a)(ht:∀ᶠ i in T.rail,0≤p i): Cover T j a p (fun i=> Shellac.off (f i)) x:= h.sub (Cover.fixed (fun i=> f i 0) ht hv.ab)
lemma book_home (F:∀ i, Set (V i))(h:∀ e>a,∀ᶠ i in T.rail,∀ y∈F i,Brush j (T.cost i^e) (p i) (f i) y) : Cover (V:=fun i=> V i.1) (U:=fun _=>ℝ) (T.book F) j a (p∘Sigma.fst) (fun i=> f i.1) (fun i=> i.2.1):= fun v hv=> (T.booked F _).mpr (h v hv)
lemma token (F:∀ i, Set (V i))(h:Cover (V:=fun i=>V i.1) (U:=fun _=>ℝ) (T.book F) j a (p∘Sigma.fst) (fun i=> f i.1) (fun i=> i.2.1)): ∀ e>a,∀ᶠ i in T.rail,∀ y∈F i, Brush j (T.cost i^e) (p i) (f i) y:= fun v hv=> (T.booked F (fun i y=> Brush j (T.cost i^v) (p i) (f i) y)).mp (h v hv)
lemma certainly {f :∀ i, V i→ℝ}{b:ι→ℝ}(h:H b c) (he:∀ᶠ i in T.rail,0<b i ∧ b i≤1) (hp:∀ᶠ i in T.rail, ‖x i‖ ≤ b i)
    (hx:Cover (V:=fun i=>V i.1) (U:=fun _=>ℝ) (T.book (fun i=>closedBall (0:V i) (b i))) j a (fun _=>1) (fun i=>f i.1) (fun i=> i.2.1))(hn:n<j): Cover T j (a+c*(n+1:ℕ)) (fun i=>(b i)⁻¹) (fun i=> f i - Work.G05.blockTaylor n (f i)) x:= by
    intro e hv; obtain ⟨w,hw,hb⟩:=exists_between hv; let s:=w-c*(n+1:ℕ); have hS:a<s:=(by unfold s; linarith); filter_upwards [T.positive,token (j:=j) (p:=fun _=>1) (fun i=>closedBall (0:V i) (b i)) hx s hS, (Clock.Meter.pale T s|>.mul (h.pow (n+1))) e (by unfold s; linarith), he,hp] with i hi hx hI he hp
    exact (Local.Taylor.forecast he.1 he.2 hn (fun z hz=>(hx z (mem_closedBall_zero_iff.mpr hz))) hp|>.climb ((le_abs_self _).trans hI) le_rfl)
end Cover
local notation "S"=> Shellac.off
def forming {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] (c:Word ℝ) (u:Book E)(n:ℕ): E→ℝ:=∑ i∈ range (n+1), c i • u (n-i)
variable {i:ι}
lemma delay_right {f:Book (V i)}{n:ℕ}{t:ℝ}{c:Word ℝ} : delay (forming c f) n t= ∑ j∈ range (n+1), (t^j*c j) • (delay f (n-j) t):= by
 induction n with
 | zero=> simp [delay,forming]
 | succ n ih=>
    let N:= n+1; let g:=(forming c f); let k i j:=(t^i*c i) • delay f j t; let dp(r:ℕ):=(c r) • f (n+1-r); let u:=k (n+1); have hz: delay g N t= delay g n t + t^N • (∑ i∈ range (N+1),dp i):= by unfold delay; rw [Finset.sum_range_succ]; rfl
    let F(i:ℕ):=t^N • dp i; rw [hz, Finset.smul_sum, sum_range_succ, ih]; -- edit rewrite ordering
    have hp (i:ℕ)(hi:i∈range (n+1)): k i (n-i)+F i= k i (n+1-i):= by
       have he:=mem_range.mp hi; unfold k; rw [show n+1-i=(n-i)+1 by omega]; conv_rhs=> unfold delay; rw [Finset.sum_range_succ]
       rw [smul_add]; apply congr_arg; unfold F dp; rw [smul_smul,smul_smul, show n+1-i=n-i+1 by omega, show t^N*c i=(t^i*c i)*t^(n-i+1) from ?_] -- handle conv scope
       rw [mul_right_comm,← pow_add,show i+(n-i+1)=N by unfold N; omega]
    -- structure sums edit via congr
    conv_rhs=>rw [sum_range_succ];
    rw [←add_assoc,←sum_add_distrib, show ∑ i∈range (n+1),(k i (n-i)+F i)=∑ i∈range (n+1),k i (n+1-i) from sum_congr rfl hp]; apply congr_arg; unfold dp N; rw [tsub_self,smul_smul]; simp [delay]
end YM.AllOrder.Catch
