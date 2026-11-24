import YM.QuadraticLocal.Neighborhood.Door
import YM.QuadraticLocal.Deletion.Crop
import YM.QuadraticLocal.Startup.Arbor
/-!
## Back and forth to the manuscript root norms

The full l1 Hit ledger is a working *per-site* budget. Root-norm inputs
instead only pay per-MARK of any specified labels, summing over their other
incidences. For Factored Θ (actual polynomial), convert along the point
`BudgetPoint` metric (no change to the representation masks). We'll spend
 +2 reserve in exponent for E (including reanchoring to all supported sites,
 on native root kernel derivative norm) and +1 for K (including all nonempty
 mark-set/forced partners). The caller then has the canonical test ledger on
 both coordinates and ANY radii. Avoid paying local amplitude for unmarked
 real K: this port buys it from true-vacuum `Rent` separately before combining.
 These receipts extend the `FullBudget` operator only in economy protocol:
 tests in full Wallet at realmark costs BEFORE sums over all labels. Geometry
 carried with every mode.Stencil.Call`. Not changing polynomial coefficients.
 Erasure and mergers demanding support reserve must invoke on that same meter.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Neighborhood
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local Extra.Multi
open Throng
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {T J : Type*} {w : V → ℝ} {a α β γ k b r t :ℝ} {B : ℕ}
variable {P : ℕ→ ForcedAddress G n} {F : Code G n} {S:Set V}
variable (hw: ∀ i,0<w i)
variable (L:Lamps T J G p o R)
variable (H: QuadraticLocal.Hard T p P F o R)
variable [Fintype V] {μ : ℕ}
local notation "tW"=> Poly.toll w

namespace Aperture
structure RootsE (w: V→ℝ) (a e :ℝ) :Prop where
   account : ∃ f:J→ℝ, (∀ i,0≤f i) ∧ (∀ i v,v∈(L.mode i).val → ∀ t:T,Mix.grain p (L.ground i) (L.nominal t i) (o v) (f i)) ∧
     Extra.Multi.Rooted (fun i=>(L.mode i).val) L.ground p.B a (fun i=> Poly.toll w (L.mode i)*f i) e

def muQ (p:BudgetPoint) (μ:ℕ) := ((μ:ℝ)*siteFactor p.B)
def muE (p:BudgetPoint) (μ:ℕ) := (scarf p*(↑(p.order.factorial):ℝ)) * muQ p μ
variable (hp:Extra.Multi.Occupancy o μ)
include hw
lemma RootsE.output (h:L.Paid w p.B a b) : RootsE L w a (3*b):=by
   obtain ⟨f,hf,hG,h⟩:=h.budget; refine ⟨fun i=>3*f i,fun i=> mul_nonneg (by norm_num) (hf i),fun i v hv t=>outBound (o v) _ (hG i t (o v) (L.roots _ _ hv)),fun i=> budget_mono (budget_scale (show (0:ℝ)≤3 by norm_num) (h (o i))) (fun j=> ?_) (fun j=>?_)⟩
   · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Poly.worth hw _).le (mul_nonneg (by norm_num) (hf _))); exact le_rfl
   split; next hV=> rw [if_pos ( show _∈ L.ground j from L.roots _ i hV )]; dsimp; apply le_of_eq; ring
   next=> exact mul_nonneg (by norm_num) ((h (o i)).1 j)
include hp
lemma RootsE.meter (hh:RootsE L w (a+2) b)(hb:0≤b): L.Paid w p.B a (muE p μ*b):=by
   obtain ⟨f,hf,hC,hF⟩:= hh.account; let g0:=scarf p*(↑(p.order.factorial):ℝ); let g i:= Real.exp (coverNumber p.B (L.ground i))*(g0*f i); have he:0≤ g0:= mul_nonneg (scarf_pos p).le ( Nat.cast_nonneg _ )
   have hh i: (L.mode i).val.Nonempty:= Finset.nonempty_iff_ne_empty.mpr (fun h=> L.live i (Subtype.ext h)); have h1 i:0≤g i:= mul_nonneg ( Real.exp_pos _ ).le (mul_nonneg he (hf i)); let c i:= Poly.toll w (L.mode i)*f i; have hc i:0≤c i:= mul_nonneg (Poly.worth hw _).le (hf i)
   let E:=Extra.Multi.root_hit (mode:=fun i=>(L.mode i).val) (a:=a+1) hp hc hb (fun i _=>by obtain ⟨v,h⟩:=hh i; exact ⟨v,h,L.roots _ _ h⟩) (show Rooted _ _ p.B ((a+1)+1) c b from ?_)
   swap; · rw [add_assoc]; norm_num; exact hF
   refine ⟨g,h1,fun i t u hx=> ?_, fun i=> ?_ ⟩
   · obtain ⟨v,h⟩:=hh i; rw [show g i= _ from (by unfold g g0; ring : g i=(scarf p*Real.exp (coverNumber p.B (L.ground i)))*(p.order.factorial*f i) ) ]; exact cost (o v) u (L.ground i) (L.roots _ _ h) hx (inBound (o v) _ (hC i v h t))
   let hQ:= budget_scale he (E i); unfold muE; rw [mul_assoc]; refine budget_mono hQ (fun j=>?_) (fun j=>?_)
   · split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (h1 j)) (Real.exp_pos _).le; exact le_rfl
   dsimp only [Lamps.ground]; split; next=> dsimp only [c,g,Lamps.ground]; rw [add_mul,one_mul,Real.exp_add]; exact le_of_eq (by ring)
   next=>rw [mul_zero]
-- K.Target transducer. Use polynomial majorants on ONLY the weighted nonquiet words, at each force address.S.Persistent. Retains FUZZ stencils. Inputs such d incorporate budgets before relation. Need not assume any zero convention on d—we set the terms without eligible footprint to zero at reporting.
omit hp
local notation "ρ"=> GridRenewal.Rain.fresh
local notation "J!"=> ℕ× R.Mode

structure RootsK (w:V→ℝ) (a b:ℝ): Prop where
    cash : ∃ d:ℕ→Poly R,(∀ i t U s,s ≠ R.quiet→ ‖(H.hard t i U).part s‖≤ ‖(d i).part s‖)∧
       Rooted (fun j : ℕ×R.Mode=>j.2.val) (fun j=> (P j.1).support) p.B a (fun j:ℕ×R.Mode=> Poly.toll w j.2 * ‖(GridRenewal.Rain.fresh (d j.1)).part j.2‖) b
local notation "Φ"=> Poly.price w
-- prune only output **majorants**. 
private def plot (H: QuadraticLocal.Hard T p P F o R)(f:ℕ→Poly R) (r:ℕ→ℝ) (i:ℕ) := Poly.inject fun s=> if s=R.quiet then (r i:ℂ) else if Trigger.Origins (o:=o) ((P i).support) s.val then (↑(‖(f i).part s‖):ℂ) else 0
omit hw in
private lemma plot_part {r:ℕ→ℝ} (f:ℕ→Poly R) i s: (plot H f r i).part s= if s=R.quiet then (↑(r i):ℂ) else if Trigger.Origins (o:=o) ((P i).support) s.val then (↑(‖(f i).part s‖):ℂ) else 0:=rfl
omit hw in
private lemma plot_bound {f:ℕ→Poly R}{r:ℕ→ℝ} (hr:∀ i U, ‖F i U‖≤ r i)
    (h:∀ i t U s,s≠R.quiet → ‖(H.hard t i U).part s‖ ≤ ‖(f i).part s‖) : ∀ i t U,Width.Covered (H.hard t i U) (plot H f r i) := by
    intro i t U s; by_cases hx:s=R.quiet
    · subst s; rw [H.quiet]; have he:= hr i U; change ‖((F i U:ℝ):ℂ)‖ ≤ _ ∧ _ ; unfold plot Poly.part Poly.inject; simp only [Complex.norm_real,if_true]; exact ⟨he,rfl⟩
    by_cases he: Trigger.Origins (o:=o) (P i).support s.val
    · rw [show (plot H f r i).part s=(↑(‖(f i).part s‖):ℂ) from (by rw [plot_part,if_neg hx,if_pos he])]; exact ⟨h i t U s hx,rfl⟩
    rw [show (plot H f r i).part s=0 from (by rw [plot_part,if_neg hx,if_neg he]),not_ne_iff.mp (show ¬ (H.hard t i U).part s≠0 from (fun hx=> he (H.locality t i|>.carry U s hx)))]; simp
omit hw in
private lemma center {f:ℕ→Poly R}{a':ℕ→ℝ} (i:ℕ) : (plot H f a' i).part R.quiet=(a' i:ℂ):=by rw [plot_part,if_pos rfl]
local notation "dC"=> Throng.Hard.active w
private lemma spars (f:ℕ→Poly R)(a':ℕ→ℝ){i:J!} (he: 0< Poly.toll w i.2 * ‖( GridRenewal.Rain.fresh (plot H f a' i.1)).part i.2‖ ) : (i.2).val.Nonempty ∧ Trigger.Origins (o:=o) (P i.1).support i.2.val:= by
     rw [Hard.hotPart] at he; split at he; swap
     next h=>
       refine ⟨Finset.nonempty_iff_ne_empty.mpr (fun ht=> h (Subtype.ext ht)),?_⟩; contrapose! he; rw [show (plot H f a' i.1).part i.2=0 from (by rw [plot_part,if_neg h,if_neg he]),norm_zero,mul_zero]
     next=> simp at he
private lemma prune (f:ℕ→Poly R)(a':ℕ→ℝ)(i:ℕ) (s:R.Mode): ‖( GridRenewal.Rain.fresh (plot H f a' i)).part s‖ ≤ ‖( GridRenewal.Rain.fresh (f i)).part s‖:= by
      rw [Hard.hotPart,Hard.hotPart]; split; exact le_rfl; next h=> rw [plot_part,if_neg h]; split; simp; rw [norm_zero]; apply norm_nonneg
local notation "Root"=> Extra.Multi.Rooted
private lemma rooted_foot {a':ℕ→ℝ}{f:ℕ→Poly R} (h:Hit (fun i=>(P i).support) p.B (fun i=>dC (f i)) a b): Rooted (fun j : ℕ×R.Mode=>j.2.val) (fun j=> (P j.1).support) p.B a (fun j:ℕ×R.Mode=> Poly.toll w j.2 * ‖(ρ (plot H f a' j.1)).part j.2‖) b:=by
   let g j := Hard.active w (plot H f a' j); have hz(s:V): Hit (fun j:J!=> (P j.1).support) p.B (fun j:J!=> Poly.toll w j.2 * ‖(ρ (plot H f a' j.1)).part j.2‖) a b := RemainderComparison.CoefficientPrices.tallyI («p»:=p) _ _ h (fun (j:ℕ) (s:R.Mode)=>Poly.toll w s * ‖( ρ (plot H f a' j)).part s‖) (fun i j=>mul_nonneg (Poly.worth hw _).le (norm_nonneg _)) (fun i=>Finset.sum_le_sum fun j _=> mul_le_mul_of_nonneg_left (prune hw H _ _ i j) (Poly.worth hw _).le)
   intro s; refine budget_mono (hz s (o s)) (fun i=>?_) (fun i=>?_)
   · split; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Poly.worth hw _).le (norm_nonneg _)); exact le_rfl
   split; next hp=>
      dsimp only [] at *; let p0:= Poly.toll w i.2 * ‖(ρ (plot H f a' i.1)).part i.2‖; rcases eq_or_lt_of_le (mul_nonneg (Poly.worth hw _).le (norm_nonneg _):0 ≤ p0) with hn|hn
      · simp_rw [←hn,mul_zero,zero_mul,ite_self]; exact le_rfl
      rw [if_pos ((spars hw H f a' hn).2 _ hp),mul_comm];
   next=> exact (hz s (o s)|>.1 _)
lemma RootsK.output (hx: Throng.Hard.Pair H w p.B a b r): RootsK H w a r:=by
   obtain ⟨f,hf,hX,h⟩:=hx.cashout; let g:=plot H f (fun i=>(f i|>.part R.quiet).re); have hr (i)(t:T)(U): ‖F i U‖≤ ((f i|>.part R.quiet).re):= by
       let y:= hf i (t:T) U R.quiet; rw [H.quiet,Complex.norm_real] at y; exact y.1
   refine ⟨g,fun i t U s hp=>?_,rooted_foot hw H h⟩
   by_cases hv: (H.hard t i U).part s≠0
   · unfold g; rw [show (plot H f (fun i=>(f i|>.part R.quiet).re) i|>.part s)=(↑(‖(f i).part s‖):ℂ) from (by rw [plot_part,if_neg hp, if_pos (show Trigger.Origins (o:=o) (P i).support s.val from H.locality t i|>.carry _ _ hv)]),Complex.norm_real,Real.norm_of_nonneg (norm_nonneg _)]; exact (hf i t U s).1.trans_eq ((hf i t U).norm s|>.symm)
   rw [not_ne_iff.mp hv,norm_zero]; exact norm_nonneg _
include hp
set_option linter.unusedSectionVars false
lemma RootsK.assemble (hk:RootsK H w (a+1) b)(hb:0≤b)(hf: QuadraticLocal.Hard.Rent P F p a k): Throng.Hard.Pair H w p.B a (k + muQ p μ*b) (muQ p μ*b):=by
    obtain ⟨r,hr,hU,hK⟩:= hf.earns; obtain ⟨d,hD,hB⟩:= hk.cash; let f:= plot H d r
    let q :ℕ×R.Mode→ℝ:=fun j=> Poly.toll w j.2 * ‖(GridRenewal.Rain.fresh (f j.1)).part j.2‖; have hs i:0≤q i:= mul_nonneg (Poly.worth hw _).le (norm_nonneg _)
    have hg : Hit (fun i:ℕ×R.Mode=> (P i.1).support) p.B q a (muQ p μ*b):= Extra.Multi.root_hit (mode:=fun i=>i.2.val) hp hs hb (fun i he=> by obtain ⟨⟨v,hv⟩,hz⟩:= spars hw H d r he; exact ⟨v,hv,hz _ hv⟩) (Rooted.mono hB hs (fun i=>mul_le_mul_of_nonneg_left (prune hw H d r i.1 i.2) (Poly.worth hw _).le) le_rfl le_rfl)
    -- regroup exactly by address, no site-dependent choice. cf CoefficientPrices.
    have ht: Hit (fun i=>(P i).support) p.B (fun i => dC (f i)) a (muQ p μ*b):=by
       intro x; let φ : ℕ×R.Mode→ℝ:= fun i=> if x∈(P i.1).support then q i* Real.exp (a*coverNumber p.B (P i.1).support) else 0; have hv:SumBudget φ _:= hg x; let g i:= ∑' s:R.Mode, φ (i,s); have hh: _=SumBudget g (muQ p μ*b):= (by apply Eq.symm; apply congr_arg (SumBudget · _); funext i; unfold g; rw [tsum_fintype]; by_cases H:x∈(P i).support; simp only [φ,H,if_true,← sum_mul]; swap; simp [φ,H]; rfl : (SumBudget (fun i:ℕ=> if x∈(P i).support then Hard.active w (f i)*Real.exp (a*coverNumber p.B (P i).support) else 0) (muQ p μ*b))= _ )
       rw [hh]; exact ⟨fun i=>tsum_nonneg fun j=>hv.1 _, hv.2.1.prod,hv.2.1.tsum_prod.symm.trans_le hv.2.2⟩
    refine ⟨f,plot_bound H hU hD,fun x=>?_,ht⟩
    apply budget_mono (budget_plus ( hK x ) (ht x)) (fun i=>?_) (fun i=>?_)
    · split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
    dsimp only; rw [Throng.Hard.wholly]; split; next=> rw [show (f i|>.part R.quiet)=(r i:ℂ) from center H i,Complex.norm_real,Real.norm_of_nonneg (hr i), add_mul]
    next=> rw [add_zero]
end Aperture
end YM.QuadraticLocal.Neighborhood
