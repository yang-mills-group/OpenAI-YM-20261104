import YM.Qlocal.Moonset.Hark
/-!
Real stencil comparison for the reporting/evolution coupling change, *not* assuming the
calendar matches the change exactly. Fees on the discrepancy, for all group fields on the same
masks, with actual rank scale. On fixed common short hull.
No smallness hypotheses other than symbolic licensing, and inequalities on support and threshold
exponents that will be acquired by schedule.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Moonset
open Function Filter Wilson Lattice RG Gauge Push.AbsoluteSums Finset Marker
open AllOrder AllOrder.Floe AllOrder.Floe.Pace
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern Quipu.Eluder
open scoped Topology BigOperators Classical ContDiff
variable {V:Type} [Fintype V][DecidableEq V] {R:Marker.Census V} {G:Gauge}
variable {g:V→ℕ}{p N i k L:ℕ}(Y : Stanza R G g p)
variable {t a C L₀ : ℝ}
open Dialect
variable (s:Senses R) {n: Side} (o:V → Site n) (Z : ℕ → Prop) (N:ℕ)
set_option quotPrecheck false
local notation "C'" => Lagger.dues g s.val
local notation "T" => Stanza.son Y N
local notation "K" => p+C'+1
local notation "S★" => o (Sonnet.root s)
local notation "Λ" => Stack.selector (T)
local notation "Ψ" => art Y s o
variable (P:BudgetPoint)(δ : ℝ)
local notation "Ω" => Tale.court P.B (o (Sonnet.root s))
local notation "t★" => P.threshold
variable {w : ℕ} (hb:w ≤ P.B)
variable (q : Coin) (q₀ : q 0=0) (r:ℕ)(hr:p ≤ r)
variable (h : ℝ) (hh:0<h) (z : ℝ) (hz:0<z) (hp:(Stanza.son Y N).Allows a C)(ha:0<a)
local notation "YW"=> toParent q Y
local notation "YD"=> toChild q Y
local notation "Φ"=>Moonset.forward q
-- for all computations at exact positive β fine/coarse
/-- Coefficient of `(e,k)` of the re-setting discrepancy. `h` and `z` are respectively TRUE g
of finer and coarser mesh. `q` is the formal series of renormalization constants with `Wheel.wag`
convention. No exponent lost by the re-expression itself. -/
noncomputable def gap (p e k:ℕ)(h z:ℝ)(q:Coin) := worth z e k -∑ i∈Finset.Icc e p, worth h i k * Moonset.forward q e k (i-e)
-- exact formula for wake, arbitrary momentum board & t from reader history
noncomputable def record (o: V→Site n) (Z : ℕ→Prop)(N :ℕ) (h : ℝ) := Tale.wake s (Stanza.son Y N) (Stack.selector _ Z) o h
noncomputable def immediate (o: V→Site n) (w : ℕ)(N : ℕ) (h : ℝ) : Config G n→ℝ:= record Y s o (fun i=> i ≤ w) N h
local notation "U"=> record Y s o Z N
local notation "U0"=> record Y s
local notation "Ud"=> record (toChild q Y) s o Z N
variable (x:Config G n)
include hp ha hh hz
lemma authentic : record Y s o Z N z x-record (toChild q Y) s o Z N h x=∑ e∈range (p+1),∑ k∈range (p+C'+1), gap p e k h z q * draw Y s e k Z o N x:= by
  let g e k:= draw Y s e k Z o N x; let W i e k:= worth h i k * Moonset.forward q e k (i-e) * g e k
  let a := range (p+1); let b:= range K
  have hB(i:ℕ)(hi:i ≤ p)(k:ℕ) : worth h i k* (draw (toChild q Y) s i k Z o N x)=∑ e∈a,if e ≤ i then W i e k else 0 := by
    unfold toChild; rw [retention Y s (Φ) o Z x N i k hi hp ha,mul_sum, ← Finset.sum_filter,show a.filter (fun e=> e ≤ i)=range (i+1) from (by ext; unfold a; simp only [mem_filter,mem_range]; omega)]; exact Finset.sum_congr rfl fun j _=> (mul_assoc ..).symm
  have hi e: (∑ i∈a,∑ k∈b,if e ≤ i then W i e k else 0)=∑ k∈b,∑ i∈Icc e p, W i e k:=by
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun k _=>?_ ; rw [← Finset.sum_filter,show a.filter (fun i=>e ≤ i)=Icc e p from (by ext; unfold a; simp only [mem_filter,mem_range,Finset.mem_Icc]; omega)]
  have he : Ud h x=∑ e∈range (p+1),∑ k∈range K,∑ i∈Finset.Icc e p,W i e k:= by
    unfold record; rw [price_recovered _ _ _ _ _ _ _ hh]; apply Eq.trans (b:=∑ i∈a,∑ e∈a,∑ k∈b,if e ≤ i then W i e k else 0); · refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Finset.sum_comm (s:=a) (t:=b)]; exact Finset.sum_congr rfl fun k hk=>hB i (Nat.le_of_lt_succ (mem_range.mp hi)) k
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun e _=> hi e
  rw [he]; unfold record; rw [price_recovered _ _ _ _ _ _ _ hz,← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl fun e he=>?_ ; rw [← Finset.sum_sub_distrib]; refine Finset.sum_congr rfl (fun k hk=>?_); unfold gap W; rw [sub_mul,← Finset.sum_mul]
include q₀ in
lemma placement : (record (toParent q Y) s o Z N z) - (record Y s o Z N h) = ∑ e∈range (p+1),∑ k∈range (p+C'+1), gap p e k h z q • draw (toParent q Y) s e k Z o N := by
 let y:=toParent q Y; let B:=∑ v:Senses R,Lagger.dues g v.val
 have H:= retain_price Y (raise q) B C (fun i=> Finset.single_le_sum (f:=fun v:Senses R=> Lagger.dues g v.val) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i)) hp
 funext x
 have he : record Y s o Z N h x= record (toChild q (toParent q Y)) s o Z N h x:= by
   unfold record; simp_rw [price_recovered _ _ _ _ _ x _ hh]; refine Finset.sum_congr rfl fun j hj=> Finset.sum_congr rfl fun i hi=>?_ ; rw [recovers Y s o Z x N q q₀ j i (Nat.le_of_lt_succ (mem_range.mp hj)) hp ha]
 simp only [Finset.sum_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,he]
 exact authentic y s o Z N q h hh z hz H ha x

-- quote in the PayR norm retaining `P.supportExponent` or a larger specified δ
variable {b d e: ℝ} (hd: δ/P.B ≤ d) (hδ:0 ≤ δ) (hv:0 ≤ d) (h0: (Stanza.son Y N).Allows (d+a) C)
local notation "f"=> draw Y s
-- common padded roster costs. no rank≤e+dues needed
noncomputable def tax {G:Gauge}(P:BudgetPoint)(δ a:ℝ)(N k:ℕ) (C:ℝ) : ℝ:= P.threshold^k * Vase.humid G P.power P.order k N P.B 1 δ a * C
local notation "E"=> Real.exp (-(δ*coverNumber P.B Ω))
local notation "T!"=> tax (G:=G) P δ a N
local notation "Z'"=> (fun i:ℕ=> i ≤ w)
omit hp hh hz
include hb hd hδ hv h0
lemma chosen (i k:ℕ) : PayR P (Tale.court P.B (o (Sonnet.root s))) (tax (G:=G) P δ a N k C * Real.exp (-(δ*coverNumber P.B Ω))) (draw Y s i k (fun i=>i ≤ w) o N):= by
 let A:= book Y s i k; let o' := o (Sonnet.root s); let Z j:= Stack.history Z' A j∧ Bay.Hears (A j).stage o; have he:= padded_pay Y C h0 s i k
 have hg: Album.Health A (d+a+(0:ℝ)) C:=by rw [add_zero]; exact he
 let l : Lattice.Order:= Equiv.refl _
 have hq(j:ℕ)(h:Z j): Vase.Carrier l (A j) o' 1 P.B P.B Ω:= Vase.verge l (A j) o' ((show (A j).momentum ≤ w from h.1).trans hb)
 have ht:= Album.chilly l A o' P Z hg hd hδ hq le_rfl 0 (fun i hi=> Nat.zero_le _) N ha
 simp only [zero_mul,add_zero] at ht
 obtain ⟨hh,hx⟩:=Album.money l A o' P Z hq ht hg (by linarith only [hv,ha]); exact ⟨budget_nonneg ht,hh,hx⟩
-- sum cost over complete supported terms forecast only so far.
def rent_gap {G:Gauge}(P:BudgetPoint) (p N l:ℕ) (h z C δ a:ℝ)(q:Coin) := ∑ e∈ range (p+1),∑ k∈range (p+l+1),|gap p e k h z q| * tax (G:=G) P δ a N k C
local notation "E!"=> rent_gap (G:=G) P
omit hb hd hδ hv h0 ha in
lemma toll_positive {P:BudgetPoint}(δ:ℝ){d a:ℝ}(i k:ℕ)(hd:0 ≤ d)(ha:0<a): 0 ≤ tax (G:=G) P δ a i k d:= mul_nonneg (mul_nonneg (pow_nonneg P.threshold_pos.le _) (Vase.humid_nn _ _ _ _ _ _ _ _ ha)) hd
include q₀ hh hz
-- difference in **regular log** model representation, with the REAL full-purpose derivative data
lemma responsible (L:ℕ)(hw:∀ s:Senses R,Lagger.dues g s.val ≤ L) : PayR P (Tale.court P.B (o (Sonnet.root s)))
  (rent_gap (G:=G) P p N L h z (price_ops (raise q) p (p+L) C) δ a q *Real.exp (-(δ*coverNumber P.B Ω))) (immediate (toParent q Y) s o w N z-immediate Y s o w N h):= by
  let B:=price_ops (raise q) p (p+L) C; let y:=toParent q Y; have hP:= retain_price Y (raise q) L C hw h0; -- h0 at d+a
  let F i k:= gap p i k h z q
  let k' x:= tax (G:=G) P δ a N x B
  unfold immediate; rw [placement Y s o Z' N q q₀ h hh z hz h0 (by linarith)]; let M i k:= |F i k| * (k' k*E)
  have he(i k:ℕ): PayR P Ω (M i k) (F i k • draw y s i k Z' o N):= (chosen y s o N P δ hb ha hd hδ hv hP i k).z_m _
  have hx := PayR.sum (p:=P) (H:=Ω) (range (p+1)) (fun i => ∑ k∈range (p+C'+1), F i k • draw y s i k Z' o N) (fun i=> ∑ k∈range (p+C'+1),M i k) (fun i hi=> PayR.sum (range (p+C'+1)) _ _ (fun j hj=> he i j)); apply hx.enlarge; unfold rent_gap; simp_rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _=>?_ ; apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg («f»:=M i) (Finset.range_mono (show p+C'+1 ≤ p+L+1 from ?h)) (fun j hj hk=>(he i j).safe)) (le_of_eq ?he); case h=> have :=hw s; omega
  case he => exact Finset.sum_congr rfl fun j _=> (mul_assoc ..).symm
end YM.Qlocal.Moonset
