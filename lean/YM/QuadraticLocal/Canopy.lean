import YM.QuadraticLocal.Arches
/-!
## Plant additional mark-bearing exact mask changes on the final reclosure

After the first merger, the second (`finish`) will use a Drawer, with infinite alphabets,
retaining earlier flags and tests *inside* its payloads. We can inject all new `h_Z`
occurrences into the same merger, rather than trying to buy a third merger after no support
reserve then! This stays test-uniform on all χ within the paid radii; countable atom labels
and Markers share the larger Receipt. Use again also on extensions requiring the connected log
factorization with changed H by a sum of square-zero shifts on actual bad domains.

Exact K `Hard` full polynomial after this merger, with same address table as `finish` at the end
of the actual numerical step. No leaking normalization. `light_shade` requires the supplier's
explicit log equality: measured at all fields t,U; we don't forget log changes and estimate
only the product-integrated prices. The unwritten mask ledger for Kernel readability/address
`Reads` in T is supplied independently (field regular derivatives here not required on K).

There is no loss of price in this operation under the **strengthened** plus-one hit premises
and existence of numerical budgets. In particular, if disks shrink temporarily, Ray receipts
including K incoming across this step must be supplied at those disk sizes. Their proportional
restoration isn't inferred here. Store support/payload Shape at actual U also through the drawer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Canopy
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Payments GridRenewal.Rain
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {n : Side} {p : BudgetPoint}
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι T : Type*} {w : V → ℝ} {a x α β c δ γ κ k m b W D : ℝ} {B : ℕ}
-- Numerics independent of `p`.
lemma hedge {B:ℕ} {y:ℝ} (h:Rates B a b c k)(he:0≤x)(hx:x≤b)(hh:0≤y)(hy:y≤c)(ht:a≤D): Rates B D x y k:=by
    have hl : inflation x y k ≤ inflation b c k:=add_le_add (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left hy zero_le_two)
    exact ⟨h.heading,he,hh,hy.trans h.soft_limit,(mul_le_mul_of_nonneg_left hl (by positivity)).trans h.capital, ((mul_le_mul_of_nonneg_left (sub_le_sub_right (Real.exp_monotone hl) _) (Real.exp_pos _).le).trans h.returns).trans ht⟩

structure ShiftRows (T:Type*) (ι:Type*) (G:Gauge) (p:BudgetPoint)(o:V→Site n)(R:Census V) where
  place : ι→ Zone n
  soap : T → ι→ Config G n→Poly R
  cost t i : Width.LocalCharge p o (place i).val (soap t i)
  clean t i U : soap t i U≠0→ ¬Healthy p.threshold (place i).val U
  skip t i U : (soap t i U).part R.quiet = 0
  single t i U : soap t i U * soap t i U = 0
-- Could use general exp of nonquiet mask pieces, pay its `-1` Hit with common weights;
-- use single here as abbreviation to also recover the Taylor log additivity directly.
variable (M:ShiftRows T ι G p o R)
namespace ShiftRows
structure Budget (w:V→ℝ)(B:ℕ)(a s:ℝ): Prop where
  earned : ∃ f:ι→Poly R,(∀ i t U,Width.Covered (M.soap t i U) (f i)) ∧
    Hit (fun i=>(M.place i).val) B (fun i=> Poly.price w (f i)) a s

def log (t:T)(U:Config G n) := ∑' i,M.soap t i U
omit [Fintype V] in
lemma earnings (h:M.Budget w B a b)(hw:∀ i,0<w i)(ha:0≤a)(t:T)(U:Config G n): Summable (fun i=>M.soap t i U):=by
    obtain ⟨f,hf,hH⟩:=h.earned
    exact (Poly.budgeted hw (Letters.Frame.from_hit B a b _ (fun i=>(M.place i).prop) (fun i=> Poly.nonnegative hw (f i)) ha hH).2.1 (fun i=>(hf i t U).reprice _ hw)).1

open Rack
variable [Countable ι]
def packPost : ι↪ℕ := Embedding.trans (show ι ↪ Zone n ×ℕ from ⟨fun i=>(M.place i,Extra.Trajectories.pin i), fun _ _ h=> Extra.Trajectories.pin_injective (congr_arg Prod.snd h)⟩) (spare (softKeys n))
omit [Fintype V] in
lemma packSite (i:ι): (drawer G n).softer (M.packPost i)=(M.place i).val:= by
    unfold packPost; rw [Embedding.trans_apply]; unfold drawer; simp only; rw [recorded ..]; rfl
variable {X:Pipes G n}{d:Tap G n}
local notation "X'"=> drawer G n
set_option quotPrecheck false
local notation "d'"=> widen X d
local notation "ek"=> preserves X d p
local notation "Φ"=> M.packPost
def placed (t:T) : ℕ→ Config G n→Poly R:= stuff Φ (M.soap t)
variable (h:Hard.Soft X d p)
include h
lemma softWide : Hard.Soft X' d' p:=by
    let P:= X'; let d1:=d'; let e:=upS X; have he i j (hh:i=e j):d1.logarithm i=d.logarithm j ∧ P.softer i=X.softer j:= hh.symm ▸ And.intro (stuffed ..) (soft_up X j)
    have h0 (i:ℕ) : GaugeInvariant (d1.logarithm i)∧ UsesFinal p.threshold (P.softer i) (d1.logarithm i) ∧ Measurable (d1.logarithm i) ∧ (∀ U:Config G n, d1.logarithm i U≠0→ ¬Healthy p.threshold (P.softer i) U):=by
        by_cases hh:i∈ Set.range e
        · obtain ⟨j,rfl⟩:=hh; rw [(he _ _ rfl).1,(he _ _ rfl).2]; exact ⟨h.gauge _,h.uses _,h.meas _,h.flagged _⟩
        rw [show d1.logarithm i=0 from blank _ _ hh]; exact ⟨fun _ _=>rfl,fun _ _ _ _=>rfl,measurable_const,fun _ hh=>(hh rfl).elim⟩
    exact ⟨fun i=>(h0 i).1,fun i=>(h0 i).2.1,fun i=>(h0 i).2.2.1, fun i=>(h0 i).2.2.2⟩
-- transport K to drawer before its merger. Right placements mark-only.
variable (L:Hard T p X.kernel d.forced o R)
local notation "L0"=> (Hard.readdress (A:=X.pours d) L ek)
local notation "s'"=> softWide h
local notation "St"=> (L0).stock s'
omit [Fintype V] in
private lemma legal (i:ℕ)(t:T): Width.LocalCharge p o ((X').softer i) ((St t).slipVal i+M.placed t i)∧ (∀ U, ((St t).slipVal i U+M.placed t i U)≠0→¬Healthy p.threshold ((X').softer i) U):=by
    by_cases hx:i∈ Set.range Φ
    swap
    · rw [show M.placed t i=0 from blank _ _ hx]; simp only [add_zero,Pi.zero_apply]; exact ⟨(St t).slipLocal i,(St t).flagged i⟩
    obtain ⟨i,rfl⟩:=hx; rw [show M.placed t (Φ i)=M.soap t i from stuffed .., M.packSite]
    have h0:(St t).slipVal (Φ i)=0:= by
      funext y; have hh: (d').logarithm (Φ i)=0:= blank _ _ (distinct (softKeys n) _ _ _); change Poly.send _ (↑(Real.exp _-1):ℂ)=(0:Poly R); rw [hh]; simp
    rw [h0,zero_add]; exact ⟨M.cost t i,by simp only [Pi.zero_apply,zero_add]; exact M.clean t i⟩

def stock (t:T): (layout X').Stock p R o:=
    { St t with slipVal i:= (St t).slipVal i+M.placed t i
                slipLocal i:=(M.legal h L i t).1 -- order?
                flagged i:=(M.legal h L i t).2 }
omit [Fintype V] in
lemma quietWide (t:T) : WithQuiet (stock M h L t) d':=by
    let A' := Hard.stockQuiet (L0) (h:=s') t
    refine ⟨A'.hard, fun i U=>?_⟩
    suffices he : (M.placed t i U).part R.quiet=0 by
       change _+(M.placed t i U).part R.quiet=_; rw [he,add_zero]; exact A'.soft i U
    by_cases hx:i∈ Set.range Φ
    · obtain ⟨i,rfl⟩:= hx; unfold placed; rw [stuffed]; exact M.skip ..
    unfold placed; rw [blank _ _ hx]; rfl

def poster : Hard T p (addr (folio G n) p) (solid (folio G n) p d') o R where
  hard t := marked (folio G n) (stock M h L t)
  locality t := markedLocal (folio G n) (stock M h L t)
  charged t := markedEligible (folio G n) (stock M h L t)
  quiet t := WithQuiet.marked (folio G n) (M.quietWide h L t)
local notation "L*"=> M.poster h L

variable (hw:∀ i,0<w i)(ha:0≤a)(hb:Hard.SoftPrice X d p.B (a+1) b)(hh:L.Paid w p.B (a+1) m)(ht:M.Budget w p.B (a+1) δ) (hk: Rates p.B W m (b+δ) k)
omit h [Fintype V] in
private lemma wide_paid (B:ℕ)(hb:Hard.SoftPrice X d B a b): Hard.SoftPrice X' d' B a b:=by
   obtain ⟨f,hf,h,hH⟩:= hb.funds
   refine ⟨stuff (upS X) f, Rack.positive _ _ hf,?_,fun x=>transfer_budget (upS X) ?_ ?_ (hH x)⟩
   · intro i U; by_cases he:i∈ Set.range (upS X)
     · obtain ⟨j,rfl⟩:=he; rw [show (d').logarithm (upS X j)=d.logarithm j from stuffed ..,stuffed]; exact h _ _
     rw [show (d').logarithm i=0 from blank _ _ he, blank _ _ he]; simp
   · simp only [stuffed,soft_up,implies_true]
   intro j hj; simp only [blank _ _ hj,zero_mul,ite_self]
include hw ha hb hh ht hk
omit h hw ha hb hh ht hk [Fintype V] in
lemma prices {G : Gauge} {n : Side} {p : BudgetPoint} {V : Type}
    [Fintype V] [DecidableEq V] {R : Census V} {o : V → Site n}
    {ι T : Type*} {w : V → ℝ} {a δ k m b W : ℝ}
    (M : ShiftRows T ι G p o R) [Countable ι]
    {X : Pipes G n} {d : Tap G n} (h : Hard.Soft X d p)
    (L : Hard T p X.kernel d.forced o R) (hw : ∀ i, 0 < w i)
    (ha : 0 ≤ a) (hb : Hard.SoftPrice X d p.B (a + 1) b)
    (hh : L.Paid w p.B (a + 1) m) (ht : M.Budget w p.B (a + 1) δ)
    (hk : Rates p.B W m (b + δ) k) :
    ∃ f: Ovens.Label→ Poly R,(∀ i U t, Width.Covered ((stock M h L t).ink i U) (f i))∧
      Hit (drawer G n).patch p.B (fun i=> Sum.elim (fun _=>Real.exp k) (fun _=>1) i* Poly.price w (f i)) (a+1) (inflation m (b+δ) k):=by
    obtain ⟨f,hf,hG⟩:= (Hard.readdressPrice (A:=X.pours d) L (preserves X d p) hh).wages
    obtain ⟨g,hg,hη⟩:= ht.earned; have he₁ :0≤δ:= budget_nonneg (hη 0)
    have he₂:0≤b := by obtain ⟨f,-,-,hF⟩:=hb.funds; exact budget_nonneg (hF 0)
    obtain ⟨f',hf',hF⟩:= Hard.combinePays ((Hard.readdress (A:=X.pours d) L (preserves X d p))) (softWide h) hw ha (fun t i=>hf i t) hG (wide_paid _ hb) (hedge hk hk.hard le_rfl he₂ (le_add_of_nonneg_right he₁) le_rfl);
    let v:Ovens.Label→Poly R:= Sum.elim (fun _=>0) (stuff (M.packPost) g)
    refine ⟨f'+v,?_,?_⟩
    · rintro (i|i) U t
      · simp only [Pi.add_apply,v,Sum.elim_inl,add_zero]; exact hf' (.inl i) t U
      have h (g z f f':Poly R)(hp:Width.Covered g f)(hv:Width.Covered z f'): Width.Covered (g+z) (f+f'):=by
          intro i; rw [Poly.part_plus,Poly.part_plus, Complex.add_re, Complex.add_im]; have ht' := hp i; have hh := hv i; exact ⟨(norm_add_le ..).trans (add_le_add ht'.1 hh.1),by rw [ht'.2,hh.2,add_zero]⟩
      refine h _ (M.placed t i U) _ (stuff (M.packPost) g i) (hf' (Sum.inr i) t U) ?_
      by_cases he: i∈ Set.range (M.packPost)
      · obtain ⟨i,rfl⟩:= he; unfold placed; rw [stuffed,stuffed]; exact hg _ t U
      unfold placed; rw [blank _ _ he,blank _ _ he]; intro i; simp
    · have hn (i: Ovens.Label) : (0:ℝ) ≤ Sum.elim (fun _=>Real.exp k) (fun _=>1) i := by cases i; exact (Real.exp_pos _).le; exact zero_le_one
      intro x; let X₁ : Ovens.Label→ ℝ:=fun i=> if x∈ ((drawer G n)).patch i then (Sum.elim (fun _=>Real.exp k) (fun _=>1) i * Poly.price w (v i)) * Real.exp ((a+1)*coverNumber p.B (((drawer G n)).patch i)) else 0
      have hQ : SumBudget X₁ δ:= by
         let e:ι↪ Ovens.Label:= ((M.packPost)).trans (show ℕ↪ℕ⊕ℕ from ⟨Sum.inr,Sum.inr_injective⟩)
         refine transfer_budget e ?_ (fun i he=>?_) (hη x)
         · intro i; unfold X₁; change (if x∈((drawer G n)).softer ((M.packPost) i) then (1* Poly.price w (stuff _ g ((M.packPost) i)))*Real.exp ((a+1)* _) else 0)=_ ; rw [stuffed,M.packSite,one_mul,show ((drawer G n)).patch (e i)=_ from M.packSite i]
         rcases i with i|i
         · unfold X₁ v; simp
         unfold X₁ v; rw [Sum.elim_inr,Sum.elim_inr, blank (M.packPost) g (fun hx=> he (by obtain ⟨i,rfl⟩:=hx; exact ⟨i,rfl⟩)),Poly.zero_price]; simp
      refine budget_loosen (budget_mono (budget_plus (hF x) hQ) ?_ fun i=>?_) (show inflation m b k+ δ≤ inflation m (b+δ) k from by unfold inflation; linarith)
      · intro i; split; exact mul_nonneg (mul_nonneg (hn _) (Poly.nonnegative hw _)) (Real.exp_nonneg _); exact le_rfl
      unfold X₁; split
      next=>rw [← add_mul,← mul_add]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Poly.addition hw ..) (hn i)) (Real.exp_nonneg _)
      next=>rw [add_zero]
lemma budgets : (L*).Paid w p.B a W:=by
    obtain ⟨f,hf,hH⟩:= M.prices h L hw ha hb hh ht hk; let v:=(inflation m (b+δ) k); let χ := Real.exp k; let he:= merger (d:=d') (f:=f) (χ:=χ) (γ:=v) (folio G n) (stock M h L) (M.quietWide h L) hw ha (Real.one_le_exp hk.heading) (add_nonneg (mul_nonneg (Real.exp_nonneg _) hk.hard) (mul_nonneg zero_le_two hk.soft)) hf hH hk.capital
    refine ⟨wallet (folio G n) f,fun i t U=> (he.2.1 i t|>.2 U).2.1, fun x=> budget_loosen (he.1 x) (?_ : (Real.exp v-1)/χ ≤ W)⟩;
    refine (le_of_eq (?_ : (Real.exp v-1)/χ= Bid.quote k v)).trans hk.returns; rw [div_eq_inv_mul,Bid.quote,Real.exp_neg]
-- full transported log; `K` bought on stated **unnormalized** prices
omit hh hk in
private lemma fern (t:T) (U:Config G n) : ∏' i,(1+(stock M h L t).slipVal i U) =
        cyclone ((bead R (↑(∑' j,(d').logarithm j U):ℂ)+ M.log t U)):=by
    let ℓ (j:ℕ):=(d').logarithm j U; let v' j := M.placed t j U; let g (j:ℕ):= bead R (ℓ j:ℂ)
    have hℓ: Summable ℓ := ((wide_paid _ hb).cost (add_nonneg ha zero_le_one)).summable U
    have hG: HasSum g (bead R (↑(∑' j,ℓ j):ℂ)):= HasSum.map hℓ.hasSum ((bead R).comp Complex.ofRealHom) ((GridRenewal.Rain.lit R).comp Complex.continuous_ofReal)
    have hV: HasSum v' (M.log t U):= (Φ).injective.hasSum_iff (fun i hi=> by unfold v' placed; rw [blank _ _ hi]; rfl)|>.1 ((M.earnings ht hw (add_nonneg ha zero_le_one) ..).hasSum.congr_fun (fun i=> by unfold v' placed; simp only [Function.comp_apply,stuffed]))
    have he i: 1+(stock M h L t).slipVal i U= cyclone (g i+v' i):= by
       by_cases hh:i∈ Set.range Φ
       · obtain ⟨i,rfl⟩:=hh; rw [show g (Φ i)=0 from (?_),zero_add,RemainderComparison.Flues.evaporate (?_ : v' (Φ i)*v' (Φ i)=0)]
         · change 1+(Poly.send _ (↑(Real.exp _-1):ℂ)+v' (Φ i))= _; rw [show (d').logarithm (Φ i)=0 from blank _ _ (distinct (softKeys n) _ _ _)]; simp
         · unfold v' placed; rw [stuffed]; exact M.single ..
         unfold g ℓ; rw [show (d').logarithm (Φ i)=0 from blank _ _ (distinct (softKeys n) _ _ _)]; simp
       have hzchar: v' i=0:=by unfold v' placed; rw [blank _ _ hh]; rfl
       change 1+(bead R (↑(Real.exp (ℓ i)-1):ℂ)+ v' i)= _; rw [hzchar,add_zero,add_zero]; unfold g; rw [GridRenewal.Rain.clear,← Complex.ofReal_exp, Complex.ofReal_sub, map_sub]; simp
    suffices ht: HasProd (fun i=> cyclone (g i+v' i)) (cyclone (bead R (↑(∑' j,ℓ j):ℂ) + M.log t U)) by rw [funext he]; exact ht.tprod_eq
    apply (show Tendsto (fun s:Finset ℕ=> cyclone (∑ i∈s,(g i+v' i))) atTop _ from GridRenewal.Rain.breath.continuousAt.tendsto.comp (hG.add hV)).congr
    intro i; exact GridRenewal.Rain.roaring ..

lemma posterSum (t:T)(U:Config G n) : HasSum (packet (fused (folio G n) p d') p ((L*).hard t) U)
    ((Real.exp (∑' j,(d').logarithm j U):ℂ) • ((∑' i,packet (X.pours d) p (L.hard t) U i)* cyclone (M.log t U))) := by
    obtain ⟨f,hf,hH⟩:= M.prices h L hw ha hb hh ht hk
    have he:= Attached.total d' (folio G n) (stock M h L t) hw (add_nonneg ha zero_le_one) (Real.one_le_exp hk.heading) hH (fun i U=>hf i U t) U
    have hV : (∑' i,packet ((X').pours d') p ((stock M h L t).hardVal) U i)=∑' i,packet (X.pours d) p (L.hard t) U i := (Hard.readdressGas (A:=X.pours d) L ek t U (Hard.packet_summing (X:=X.pours d) L hh (add_nonneg ha zero_le_one) hw ..).hasSum).tsum_eq
    rw [fern M h L hw ha hb ht t U,hV,GridRenewal.Rain.plus,GridRenewal.Rain.clear,← Complex.ofReal_exp,mul_left_comm,GridRenewal.Rain.bead,Poly.product_bead] at he; exact he.2.2

-- compare the SAME F. No derivatives behind moved flags needed.
lemma light_shade (F log log':T→ Config G n→ Poly R)(hz:ReadZone T p (X.pours d) L F log)
     (he: ∀ t U, log t U=log' t U+M.log t U)
     (ho:∀ t U,(log' t U).part R.quiet=0): ReadZone T p (fused (folio G n) p d') (L*) F log':=by
   intro t U
   obtain ⟨hx,v,hF⟩:= hz t U; have hb:= M.posterSum h L hw ha hb hh ht hk t U; let r:ℂ:=↑(Real.exp (∑' i,(d').logarithm i U)); let y:= (∑' i,packet (X.pours d) p (L.hard t) U i); refine ⟨hb.summable,v/r,?_⟩
   have hR : r ≠ 0:= Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _); have hQ(t:T)(U): (M.log t U).part R.quiet=0:=by unfold ShiftRows.log; rw [Poly.share (M.earnings ht hw (add_nonneg ha zero_le_one) t U)]; simp_rw [M.skip]; exact tsum_zero -- notation shadow
   rw [hF,hb.tsum_eq, mul_smul_comm, smul_smul]; change _= ((v/r)*r) • _; rw [div_mul_cancel₀ _ hR]; congr 1; rw [he, ← GridRenewal.Rain.passes _ (by simp only [Poly.part_plus,ho,hQ,zero_add]), ← GridRenewal.Rain.passes _ (ho ..), GridRenewal.Rain.plus]; ring
end ShiftRows
end YM.QuadraticLocal.Canopy
