import YM.QuadraticLocal.Shelter.Corner
import YM.QuadraticLocal.Canopy
/-!
## Curtain closings. Construct the ShiftRows at common mark halo and pay

One mark edit per engaged group/polymode; evaluated exactly at ALL fields, not just in
any chart. Need BOTH the paid raw and formal positions independently. Note that mark
pressure wiggled again (`κ⁻¹`) only for the shifts. There's at least one mark in their mode,
so divide the price by κ. Can then buy the room in the ACTUAL second merger (done once
w input budget with that smaller w). Doesn't shift Residual budgets themselves into the
 flag side; retains terms/bounds and their old discrepancy factor. Model marker footprints
and stencil locations are retained in each edit by source geometry assumed along both Calls
 mode. Usage proof on germe's Shelf, separate. Only bind to Actual Travel.success_shrink etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Shelter
open Function Filter Finset Lattice Wilson RG Ac Marker Push Push.Local Push.Corrected Push.AbsoluteSums MeasureTheory
open Animals Next.Foundations Extra.Trajectories
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side}{V T ι μ ξ C : Type}[DecidableEq V]{o:V→Site n}{R:Census V}{P:BudgetPoint} {B H:ℕ}
variable {L:Lamps T ι G P o R}{L':Lamps T μ G P o R} {L₀:Lamps T ξ G P o R} (w:V→ℝ)(hw:∀ i,0<w i)
variable {D:Terrain C R}
variable {a b b₁ b₂ r t τ ε δ:ℝ} {α β γ:C→Type} [∀ i, Fintype (α i)] [∀ i, Fintype (β i)] [∀ i, Fintype (γ i)]
namespace Deck
variable (d:Deck L D H α) (d': Deck L' D H β) (d₀: Deck L₀ D H γ) (i:C)(x:T) (U:Config G n)
open Canopy
variable (hO : ∀ (i:C)(t:T) (U:Config G n), Healthy P.threshold (D.barrier o H i) U→ d.white i t U=d'.white i t U+d₀.white i t U)
include hO in
def soap : ShiftRows T C G P o R where
    place i:=⟨D.barrier o H i, D.center o i,(neighbors_mem ..).2 (by simp)⟩
    soap t i:=fun U=> Poly.send (D.mode i) (d.round i t U-d'.round i t U-d₀.round i t U)
    cost t i:=by
       have he (F Z:Config G n→Poly R)(h:Width.LocalCharge P o (D.barrier o H i) F)(q:Width.LocalCharge P o (D.barrier o H i) Z) : Width.LocalCharge P o (D.barrier o H i) (fun U=> F U-Z U):= by
          refine ⟨fun _ _=> congr_arg₂ _ (h.gauge ..) (q.gauge ..), h.borel.sub q.borel, fun _ _ hv hs=> congr_arg₂ _ (h.reads _ _ hv hs) (q.reads _ _ hv hs), fun U j hu v hv=>?_⟩
          by_cases hp:(F U).part j=0; swap; · exact h.carry _ _ hp _ hv
          exact q.carry _ _ (fun h=> hu (by rw [part_sub,hp,h]; abel)) _ hv
       have hp (x y:ℂ) : Poly.send (D.mode i) (x-y)=Poly.send (D.mode i) x-Poly.send (D.mode i) y:= by ext v; rw [part_sub]; simp only [Poly.part_send]; split_ifs <;> ring -- syntax?
       simp_rw [hp]; exact he _ _ (he _ _ (d.gatheredSym i t) (d'.gatheredSym i t)) (d₀.gatheredSym i t)
    clean t i U h hx:=by apply h; rw [d.shown i t U hx,d'.shown i t U hx,d₀.shown i t U hx,hO i t U hx]; ring_nf; simp
    skip t i U:= by rw [Poly.part_send,if_neg (D.live i|>.symm)]
    single t i U:= Classical.byContradiction fun hv=> disjoint_left.mp ((merges_of_tagged_mul hv).choose_spec.1) (D.at_anchor i) (D.at_anchor i)

local notation "V₀"=> soap d d' d₀ hO
variable (ht:0≤t)(ha:0≤a)(hτ:∀ i,(Lattice.coverNumber B (D.barrier o H i):ℝ)≤τ)
variable (h:L.Paid w B t b) (h':L'.Paid w B t b₁) (h₀:L₀.Paid w B t b₂)
include hw h h' h₀ ht
local notation "χ"=> crewCost H a τ
-- exact full masks
lemma order : L.log x U=L'.log x U+L₀.log x U+(soap d d' d₀ hO).log x U:=by
    let F (H j:ℂ) (i:C):Poly R:= Poly.send (D.mode i) (H-j)
    have he (i:C)(a b:ℂ): Poly.send (D.mode i) (a-b)=Poly.send (D.mode i) a-Poly.send (D.mode i) b:=by ext; simp only [part_sub,Poly.part_send];split_ifs <;> ring
    have hp : HasSum (fun i=> (V₀).soap x i U) (L.log x U-L'.log x U-L₀.log x U):=by simp_rw [soap,he]; apply ((d.receipt x U (h.sums ht hw ..)).sub (d'.receipt x U (h'.sums ht hw ..))).sub (d₀.receipt x U (h₀.sums ht hw ..))
    rw [ShiftRows.log,hp.tsum_eq]; abel
variable (k:ℝ)(hk:1≤k)
omit hw h h' h₀ ht
open Marker.Poly (toll)
local notation "w₀" => fun i=>w i/k
include hw ha h h' h₀ ht hτ hk
lemma paying : (soap d d' d₀ hO).Budget (fun i=>w i/k) B a (k⁻¹*(Deck.crewCost H a τ*(b+b₁+b₂))):=by
    obtain ⟨f,hf,hF,hH⟩:= h.budget; obtain ⟨g,hg,hG,hH'⟩:= h'.budget; obtain ⟨v,hv,hV,hR⟩:=h₀.budget
    let x (i:C):= d.amount i f+d'.amount i g+d₀.amount i v; have hx i:0≤x i:= add_nonneg (add_nonneg (d.bien i f hf) (d'.bien i g hg)) (d₀.bien i v hv)
    let y i:=Poly.send (D.mode i) ((x i:ℝ):ℂ); have hp:0<k:= lt_of_lt_of_le zero_lt_one hk; have hm(i:C):toll w₀ (D.mode i)≤ k⁻¹*toll w (D.mode i):=by
       rw [mul_comm]; unfold toll; rw [prod_div_distrib, Finset.prod_const]; rw [←div_eq_mul_inv]; gcongr; · exact Finset.prod_nonneg fun v _=>(hw v).le
       nth_rw 1 [show k=k^1 from (pow_one k).symm]; exact pow_le_pow_right₀ hk (Finset.card_pos.mpr ⟨D.anchor i,D.at_anchor i⟩) -- auto solve
    refine ⟨y,(fun i x' U=>?_), fun u=>?_⟩
    · intro j; change ‖(Poly.send _ _).part _‖ ≤ _ ∧ _
      dsimp only [y]; simp only [Poly.part_send]; split_ifs; swap; · simp
      exact ⟨le_trans (norm_sub_le ..) (add_le_add ((norm_sub_le ..).trans (add_le_add (d.ticket _ _ _ f (fun i t=>hF _ t _ (L.address i).anchor)) (d'.ticket i _ _ g (fun i t=>hG i t _ (L'.address i).anchor)))) (d₀.ticket i _ _ v (fun i t=>hV i t _ (L₀.address i).anchor))),rfl⟩
    have he (i:C): Poly.price w₀ (y i) ≤ k⁻¹*(toll w (D.mode i) * x i):=by
       unfold y; rw [Poly.solo]
       rw [Complex.norm_real, Real.norm_of_nonneg (hx i),← mul_assoc]
       exact mul_le_mul_of_nonneg_right (hm _) (hx _)
    rw [mul_add, mul_add χ]; refine budget_mono (budget_scale (inv_nonneg.mpr hp.le) (budget_plus (budget_plus (d.wages w hw f hf hH ht ha hτ u) (d'.wages w hw g hg hH' ht ha hτ u)) (d₀.wages w hw v hv hR ht ha hτ u))) (fun i=>by split; exact mul_nonneg (Poly.nonnegative (fun i=>(div_pos (hw i) hp)) _) (Real.exp_pos _).le; rfl) (fun i=>?_)
    -- simp unfolds
    dsimp only [Deck.soap]; split
    next=>
       apply le_trans (mul_le_mul_of_nonneg_right (he i) (Real.exp_pos _).le); unfold x; ring_nf
       exact le_rfl
    next=>simp only [add_zero,mul_zero,le_refl]
end Deck
end YM.QuadraticLocal.Shelter
