import YM.QuadraticLocal.Fusion
import YM.Progress.DIRECTED_RECIPE.Tender
import YM.RG3.Held.Lives

/-!
# qlocal — marked forced tables after the vacuum mergers

The unmarked comparison path has two forced-fusion steps with countably many slip addresses
and a final (fixed, but choice-dependent) dilation to make room for new marks. Quantitative
transport of the **whole** forced array (on that path, retaining the small factor), not a claim
about moving the step to a differently-priced vacuum (e.g. with `v` or kinetic held at a
perturbatively predicted value rather than extracted).

`Hard` is an array behind `LocalComparison.FullBudget`'s forced entries. Each entry includes the
vacuum; prices are coefficient majorants, chosen before the (unit) tests. Padded layouts and
stronger address regions can use their own witnesses later; here `o` asserts *at least* those
origins remain present. Countable `Tap.logarithm` and actual mask at the step (no derivatives
for the flagged hard component).
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type*} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι μ T : Type*} {w : V → ℝ} {a α β δ γ κ k m b W D : ℝ} {B : ℕ}
variable {P : ℕ→ ForcedAddress G n} {F : Code G n}

structure Hard (T : Type*) (p : BudgetPoint) (P : ℕ→ ForcedAddress G n) (F : Code G n)
    (o : V → Site n) (R : Census V) where
  hard : T → ℕ → Config G n → Poly R
  locality t i : Width.LocalCharge p o (P i).support (hard t i)
  charged t i U : hard t i U≠0 → (P i).eligible p.threshold U
  quiet t i U : (hard t i U).part R.quiet= (F i U:ℂ)
namespace Hard
variable (H : Hard T p P F o R)
structure Paid (w : V→ℝ) (B : ℕ) (a m : ℝ) : Prop where
  wages : ∃ f:ℕ→Poly R,(∀ i t U, Width.Covered (H.hard t i U) (f i)) ∧
    Hit (fun i=>(P i).support) B (fun i => Poly.price w (f i)) a m
private lemma covered_zero : Width.Covered (0:Poly R) 0:=fun j=>by simp
private lemma local_zero (i:Support n)(p:BudgetPoint)(o:V→Site n) : Width.LocalCharge p o i (0:Config G n→Poly R):=by
  refine ⟨fun _ _=>rfl,measurable_const,fun _ _ _ _ =>rfl,?_⟩; exact fun U q h=> (h rfl).elim

def pullback (f : μ → T) : Hard μ p P F o R := ⟨H.hard ∘ f,fun _ => H.locality _,fun _ => H.charged _,fun _ => H.quiet _⟩

lemma mono (h:H.Paid w B a m) (h' : m≤b):H.Paid w B a b:=by obtain ⟨f,h,hF⟩:=h.wages; exact ⟨f,h,fun i=>budget_loosen (hF i) h'⟩

def truncate (H' : BudgetPoint) (ht:H'.threshold=p.threshold): Hard T H' P F o R:=
  ⟨H.hard,fun t i=> { H.locality t i with reads:= ht.symm ▸ (H.locality t i).reads }, fun t i=> ht.symm ▸ H.charged t i, H.quiet⟩

def stockAux (X:Pipes G n) (F:Code G n) (K:ℕ → Config G n → Poly R) (h:∀ i, Width.LocalCharge p o (X.softer i) (K i))
    (ht:∀ i U,K i U≠0 → ¬Healthy p.threshold (X.softer i) U) (H: Hard T p X.kernel F o R) (t:T) : (layout X).Stock p R o :=
  ⟨H.hard t, K, H.locality t, H.charged t, h, ht⟩
-- same marked array through actual unmarked slips
variable (H : Hard T p X.kernel d.forced o R) (e : ℕ ≃ X.Pellet)

/-- Can use in intermediate reclosure irrespective of affine-nulling. -/
structure Soft (X : Pipes G n) (d : Tap G n) (p : BudgetPoint) : Prop where
  gauge j : GaugeInvariant (d.logarithm j)
  uses j : UsesFinal p.threshold (X.softer j) (d.logarithm j)
  meas j : Measurable (d.logarithm j)
  flagged j U : d.logarithm j U≠0 → ¬Healthy p.threshold (X.softer j) U
structure SoftPrice (X : Pipes G n) (d : Tap G n) (B : ℕ) (a b : ℝ) : Prop where
  funds : ∃ f:ℕ→ℝ,(∀ i, 0≤ f i) ∧ (∀ i U, ‖d.logarithm i U‖ ≤ f i) ∧ Hit X.softer B f a b
namespace SoftPrice
lemma cost {X : Pipes G n} {d : Tap G n} {B : ℕ} {a b : ℝ} (hS : SoftPrice X d B a b) (ha : 0 ≤ a) : Dominated d.logarithm := by
  obtain ⟨f,h,hU,hF⟩:= hS.funds; exact ⟨f,(Letters.Frame.from_hit _ _ _ f X.sites h ha hF).2.1,hU⟩
end SoftPrice

variable (h : Soft X d p)
private def scalarRow (c:ℝ) : Poly R := Poly.send R.quiet c
private lemma at_quiet (c : ℝ) : (scalarRow (R:=R) c).part R.quiet=c := by simp [scalarRow]
private def reachesScalar (j:ℕ)(U:Config G n) : Poly R := scalarRow (reach d (.inr j) U)
include h
private lemma movement (i) : Width.LocalCharge p o (X.softer i) (reachesScalar (R:=R) (d:=d) i):=by
  change Width.LocalCharge p o _ (fun U=> Poly.send R.quiet ((Real.exp (d.logarithm i U)-1:ℝ):ℂ))
  refine ⟨fun t U=>by rw [h.gauge i t U],(Overlay.Bands.sends _).measurable.comp ?_,fun U Z hx hp=> ?_, fun U a hx=> ?_⟩
  · exact Complex.continuous_ofReal.measurable.comp ((Real.measurable_exp.comp (h.meas _)).sub measurable_const)
  · rw [h.uses _ _ _ hx hp]
  intro j ht
  by_cases he : a=R.quiet; subst a; exact (Finset.notMem_empty _ ht).elim
  exfalso; apply hx; rw [Poly.part_send, if_neg he]

private lemma movement_flag i U : reachesScalar (R:=R) (d:=d) i U≠0 → ¬Healthy p.threshold (X.softer i) U := by
  contrapose!
  intro hu; obtain hz:= mt (h.flagged i U) (not_not_intro hu); rw [not_ne_iff] at hz
  simp [reachesScalar,reach,hz,scalarRow]

def stock (t:T) := stockAux X d.forced _ (movement h) (movement_flag h) H t
lemma stockQuiet (t:T) : WithQuiet (H.stock h t) d :=
  ⟨H.quiet t,fun _ _=> at_quiet _⟩

def transport : Hard T p (addr e p) (solid e p d) o R where
  hard t := marked e (H.stock h t)
  locality t := markedLocal e (H.stock h t)
  charged t := markedEligible e (H.stock h t)
  quiet t := WithQuiet.marked e (H.stockQuiet h t)

@[simp] lemma transport_hard (t i U) : (H.transport e h).hard t i U= marked e (H.stock h t) i U:= rfl
-- expose pump Hit at those construction's Rates. 
lemma combinePays {f : ℕ→Poly R} (_hw : ∀ i,0<w i) (ha : 0 ≤ a) (hF : ∀ t i U, Width.Covered (H.hard t i U) (f i))
    (hxF: Hit (fun i => (X.kernel i).support) p.B (fun i => Poly.price w (f i)) (a+1) m)
    (hS: SoftPrice X d p.B (a+1) k) (ht: Payments.Rates p.B W m k κ):
    ∃ g:Ovens.Label→Poly R,(∀ i t U,Width.Covered ((H.stock h t).ink i U) (g i)) ∧
      Hit X.patch p.B (fun i=> Sum.elim (fun _=>Real.exp κ) (fun _=>1) i * Poly.price w (g i)) (a+1) (Payments.inflation m k κ):=by
  obtain ⟨q,hq,hU,hK⟩ := hS.funds
  refine ⟨Sum.elim f (fun i=>scalarRow (2*q i)),?_,?_⟩
  · rintro (i|i) t U
    · exact hF t i U
    change Width.Covered (scalarRow (R:=R) (Real.exp (d.logarithm i U)-1)) _
    have hn : q i≤k:=by
      obtain ⟨x,hx⟩:= X.sites i; have hY:=Samples.one_le_quote (hK x) i; rw [if_pos hx] at hY; exact (le_mul_of_one_le_right (hq _) (Real.one_le_exp (mul_nonneg (by linarith) (by positivity)))).trans hY
    have hΔ := (Real.abs_exp_sub_one_le ((show |d.logarithm i U| ≤ q i from hU i U).trans (hn.trans ht.soft_limit))).trans (mul_le_mul_of_nonneg_left (hU i U) zero_le_two)
    intro v; by_cases hv:v=R.quiet; subst v; · simp only [Sum.elim_inr,at_quiet,Complex.ofReal_re,Complex.ofReal_im,Complex.norm_real]; exact ⟨hΔ,trivial⟩
    simp [Sum.elim_inr,scalarRow,hv]
  · have ht(X:ℕ→Support n)(f:ℕ→ℝ)(v b:ℝ)(hv:0≤v)(h:Hit X p.B f (a+1) b): Hit X p.B (fun i=> v*f i) (a+1) (v*b):=by
      intro x; convert budget_scale hv (h x) using 1; funext i; by_cases he:x∈X i <;> simp [he,mul_assoc]
    let f' := Sum.elim (fun i => Real.exp κ * Poly.price w (f i)) (fun i => 2*q i)
    have heq : (fun i : Ovens.Label=> Sum.elim (fun _ => Real.exp κ) (fun _ => (1:ℝ)) i * Poly.price w (Sum.elim f (fun i=>scalarRow (2*q i)) i)) = f':= by
      funext i; cases i
      · rfl
      rename_i i; simp only [f', Sum.elim_inr, one_mul, scalarRow, Poly.solo, Poly.quiet_toll, Complex.norm_real,Real.norm_of_nonneg (mul_nonneg zero_le_two (hq i))]
    rw [heq]; intro x
    let Z (i : Ovens.Label):= if x∈ X.patch i then f' i* Real.exp ((a+1)*coverNumber p.B (X.patch i)) else 0
    have h₁:SumBudget (Z ∘ Sum.inl) (Real.exp κ*m):= ht _ _ _ _ (Real.exp_nonneg _) hxF x
    have h₂:SumBudget (Z ∘ Sum.inr) (2*k):= ht _ _ _ _ zero_le_two hK x
    have htZ : HasSum Z _:= HasSum.sum h₁.2.1.hasSum h₂.2.1.hasSum
    refine ⟨?_,htZ.summable,(htZ.tsum_eq).trans_le (add_le_add h₁.2.2 h₂.2.2)⟩
    intro i; cases i
    · exact h₁.1 _
    exact h₂.1 _

lemma paid (hw : ∀ i,0 < w i) (ha : 0 ≤ a)
    (hF : H.Paid w p.B (a+1) m) (hS: SoftPrice X d p.B (a+1) k)
    (ht: Payments.Rates p.B W m k κ) : (H.transport e h).Paid w p.B a W := by
  obtain ⟨f,hf,hZ⟩:= hF.wages
  obtain ⟨f,hx,hY⟩:=H.combinePays h hw ha (fun i j=>hf j i) hZ hS ht
  have hQP := merger e (H.stock h) (H.stockQuiet h) hw ha (Real.one_le_exp ht.heading)
    (show 0 ≤ Payments.inflation m k κ from add_nonneg (mul_nonneg (Real.exp_pos _).le ht.hard) (mul_nonneg zero_le_two ht.soft)) (fun i U t=>hx i t U) hY ht.capital
  refine ⟨wallet e f,fun i t U=> (hQP.2.1 i t|>.2 U).2.1, fun i=> budget_loosen (hQP.1 i) (?_ : _ ≤ W)⟩
  apply le_trans (le_of_eq ?_) ht.returns
  rw [div_eq_inv_mul, Bid.quote,Real.exp_neg]

private lemma expLog (hS: SoftPrice X d B a b) (ha:0≤a) (t:T) (U) :
    ∏' j, (1+(H.stock h t).slipVal j U) = scalarRow (R:=R) (Real.exp (∑' j, d.logarithm j U)) := by
  let f i := d.logarithm i U
  have he:HasProd (fun i=> Real.exp (f i)) (Real.exp (∑' i,f i)):= by
    have hf: Tendsto (fun s:Finset ℕ => ∏ i∈s, Real.exp (f i)) atTop (𝓝 (Real.exp (∑' i,f i))):=by
      simp_rw [← Real.exp_sum]; exact Real.continuous_exp.continuousAt.tendsto.comp (((hS.cost ha).summable U).hasSum)
    exact hf
  let P : ℝ →+* Poly R := (Poly.bead R).comp Complex.ofRealHom
  have hp:Continuous P:= (Overlay.Bands.sends R.quiet).comp Complex.continuous_ofReal
  refine (?_ : HasProd (fun j=>1+(H.stock h t).slipVal j U) _).tprod_eq
  apply HasProd.congr_fun (he.map P hp); intro j
  change 1+P (Real.exp (f j)-1)=P _
  rw [map_sub,map_one]; ring


lemma carries (hw : ∀ i,0 < w i) (ha : 0 ≤ a)
    (hF : H.Paid w p.B (a+1) m) (hS: SoftPrice X d p.B (a+1) k) (ht: Payments.Rates p.B W m k κ) (t:T) (U : Config G n) :
    Summable (packet (X.pours d) p (H.hard t) U) ∧
    HasSum (packet (fused e p d) p ((H.transport e h).hard t) U)
      ((Real.exp (∑' i,d.logarithm i U):ℂ) • (∑' b, packet (X.pours d) p (H.hard t) U b)) := by
  obtain ⟨f,hf,hZ⟩:=hF.wages
  obtain ⟨f,hx,hY⟩:=H.combinePays h hw ha (fun i j=>hf j i) hZ hS ht
  obtain ⟨hI,hG,hQ⟩ := Attached.total d e (H.stock h t) hw (add_nonneg ha zero_le_one) (Real.one_le_exp ht.heading) hY (fun i U=>hx i t U) U
  rw [expLog H h hS (by linarith),mul_comm] at hQ
  rw [← Poly.product_bead]; exact ⟨hI,hQ⟩
omit h

-- readdress to `finish`, old predicate still effective on values (`stuffed`), no mismatch.
section Shift
variable {A B0 : Activities G n} (Z:Hard T p A.forced A.K o R)
variable {f g:ℕ ↪ ℕ}

def readdress (hP:Readdress p f g A B0) : Hard T p B0.forced B0.K o R where
  hard i := stuff g (Z.hard i)
  locality t i := by
    by_cases hi:i∈ Set.range g
    · obtain ⟨i,rfl⟩:= hi; rw [stuffed,hP.sup]; exact Z.locality _ _
    rw [blank _ _ hi]; exact local_zero ..
  charged t i U := by
    by_cases hi:i∈ Set.range g
    · obtain ⟨i,rfl⟩:= hi; rw [stuffed]; exact fun h=> hP.admits i U (Z.charged _ _ _ h)
    rw [blank _ _ hi]; simp
  quiet t i U:=by
    by_cases hi:i∈ Set.range g
    · obtain ⟨i,rfl⟩:= hi; rw [stuffed,hP.kernels]; exact Z.quiet _ _ _
    rw [blank _ _ hi,hP.restK i hi]; simp

variable (hP:Readdress p f g A B0)
lemma readdressPrice (hB:Z.Paid w B a m) : (Z.readdress hP).Paid w B a m:=by
  obtain ⟨f,hf,h⟩:=hB.wages; refine ⟨stuff g f,?_,fun i=>?_⟩
  · intro i t U; unfold readdress; dsimp only; by_cases hi:i∈Set.range g
    · obtain ⟨i,rfl⟩:= hi; rw [stuffed,stuffed]; exact hf _ _ _
    rw [blank _ f hi,blank _ _ hi]; exact covered_zero
  refine transfer_budget g ?_ ?_ (h i)
  · simp only [stuffed,hP.sup,implies_true]
  intro j hj; simp [blank g f hj]
lemma readdressGas (t:T) (U : Config G n) {v : Poly R}
    (h: HasSum (packet A p (Z.hard t) U) v):
    HasSum (packet B0 p ((Z.readdress hP).hard t) U) v:=by
  let F:=packet B0 p ((Z.readdress hP).hard t) U
  let heq : (F ∘ Finset.map g)= _ := funext fun i=> (show F (i.map g)=packet A p (Z.hard t) U i from (by unfold F packet; rw [hP.covers]; split; simp only [readdress, prod_map,stuffed]; rfl))
  rw [← heq] at h; change HasSum F _; refine Function.Injective.hasSum_iff (Finset.map_injective _) (fun i hi=> ?_)|>.1 h
  obtain ⟨j,hj,h'⟩:= finsets_off g i hi; unfold F packet; split; exact prod_eq_zero hj ((show _=0 from congrFun (blank g (Z.hard t) h') U) : stuff g (Z.hard t) j U=0); rfl

lemma changeThresholdPrice (p' : BudgetPoint) (ht:p'.threshold=p.threshold) (hB:Z.Paid w B a m) : (Hard.truncate Z p' ht).Paid w B a m:= ⟨hB.wages⟩
end Shift

open RG3.Held
-- preserves multilinearity on unrestricted tests, if supplied. Independent of Paid.Num.
variable {Y : V → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
variable (Z : Hard (∀ i,Y i) p X.kernel d.forced o R)
lemma transportPublished (hs : ∀ i U, Published (K:=ℂ) Y (fun t=>Z.hard t i U))
    (h : Soft X d p) (i : ℕ) (U) : Published (K:=ℂ) Y (fun t=>(Z.transport e h).hard t i U) := by
  simp_rw [transport_hard, Attached.marked_eq]
  split
  · apply Published.prod; intro i _; cases i
    · exact hs _ _
    next i _ => exact Published.const (scalarRow (R:=R) (reach d (.inr i) U)) (fun j hj=> (Poly.part_send ..).trans (if_neg hj))
  exact Published.zero
end Hard
end YM.QuadraticLocal
