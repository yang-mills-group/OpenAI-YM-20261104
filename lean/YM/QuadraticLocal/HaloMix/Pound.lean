import YM.QuadraticLocal.Kiosk
import YM.QuadraticLocal.SameSlot
/-!
# Coefficientwise budget of mark part, for ANY arities

For proportional estimate of the marked part of K despite it carrying the same
unmarked/vacuum word. Define `boom ε` which multiplies ONLY the price in every
nonempty set of markers by ε≥1; keeps the actual unmarked entry. This is NOT
substitution in the array! Do not use it to evaluate. It lets us use the same
strong pre-merger rates on the exact full polynomial in any many-source tests,
then conclude linear smallness of each parcel that has one or more markers in it,
relative to its input rooted budget. This isn't yet enough to track *all powers*
of old errors under linear multi-source transport.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Throng
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι μ T : Type*} {w : V → ℝ} {a α β δ γ κ k m b W D : ℝ} {B : ℕ}
variable {P : ℕ→ ForcedAddress G n} {F : Code G n}
def weight (z:ℝ) (i : R.Mode) : ℝ:= if i=R.quiet then 1 else z
def boom (z:ℝ) : Poly R→L[ℂ] Poly R where
     toFun x:= Poly.inject fun i=> ((weight z i:ℝ):ℂ)*x.part i
     map_add' x y:=by ext1 i; change _ * (x.part i+y.part i)= _*x.part i+_*y.part i; apply mul_add
     map_smul' c x:=by ext1 i; change _*(c*x.part i)=c*(_*x.part i); ring
     cont:= by -- finite Π
       apply continuous_pi; intro i; exact (Poly.part_cont _).const_mul _
local notation "η'" i:max=> weight α i
@[simp] lemma paid (x:Poly R)(z:ℝ)(i:R.Mode) : ((boom z) x).part i=((weight z i:ℝ):ℂ)*x.part i:= rfl
@[simp] lemma silent (x:Poly R)(z:ℝ): (boom z x).part R.quiet=x.part R.quiet:=by simp [paid,weight]
@[simp] lemma scalar (a:ℂ): boom α (Poly.send R.quiet a)=Poly.send R.quiet a:=by
 ext1 i; by_cases h:i=R.quiet
 · subst i; apply silent
 simp only  [paid,Poly.part_send,if_neg h,mul_zero]
@[simp] lemma identity(z:ℝ):boom z (1:Poly R)=1:=by change boom z (Poly.send R.quiet 1)= _; rw [scalar]; rfl
variable (hp:1≤ α)
include hp
lemma mass (i:R.Mode):1 ≤ weight α i:= by unfold weight; split; exact le_rfl; exact hp
lemma thin (i j s:R.Mode)(hs:Poly.merges i j s): weight α s ≤ weight α i *weight α j:= by
  by_cases h:i=R.quiet
  · subst i; have he:= Poly.vacuum _ _|>.1 hs; subst s; simp [weight]
  by_cases he:j=R.quiet
  · subst j; have hv:= (Poly.vacuum _ _).mp ((Poly.wind _ _ _).mp hs); subst s; simp [weight]
  by_cases hv:s=R.quiet
  · subst s; exact False.elim (h ((Poly.merge_vac i j).mp hs).1)
  unfold weight; simp only [h,he,hv,↓reduceIte]; exact le_mul_of_one_le_left (zero_le_one.trans hp) hp
lemma middle {x y:Poly R} (h:Width.Covered (boom α x) y) : Width.Covered x y:= by
     intro i; refine ⟨ le_trans ?_ (h i).1,(h i).2⟩; rw [paid,norm_mul, Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (mass hp _))]; exact le_mul_of_one_le_left (norm_nonneg _) (mass hp i)
lemma multiply {x y s t: Poly R}(hx:Width.Covered (boom α x) s)(hy:Width.Covered (boom α y) t): Width.Covered (boom α (x*y)) (s*t):= by
  intro i; refine ⟨?_,(Width.Covered.multiply hx hy i).2⟩; rw [paid]; simp only [Poly.part_mul,mul_sum,Complex.re_sum]; apply (norm_sum_le ..).trans; refine sum_le_sum fun k _=>?_ ; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_
  by_cases hh: Poly.merges k j i
  swap; · simp only [hh,↓reduceIte,mul_zero,norm_zero,Complex.zero_re]; rfl
  simp only [if_pos hh,norm_mul,Complex.norm_real, Real.norm_of_nonneg (zero_le_one.trans (mass hp i)), Complex.mul_re,(hx _).2,(hy _).2,zero_mul,sub_zero]; let h':= (hx k).1; let h'':=(hy j).1; rw [paid,norm_mul,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (mass hp _))] at h' h''; apply le_trans (mul_le_mul_of_nonneg_right (thin hp _ _ _ hh) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  rw [mul_mul_mul_comm]; exact mul_le_mul h' h'' (mul_nonneg (zero_le_one.trans (mass hp _)) (norm_nonneg _)) ((norm_nonneg _).trans (hx k).1)
lemma full {Z:Type*}{x y:Z→ Poly R} (t:Finset Z)(hx:∀ i∈t,Width.Covered (boom α (x i)) (y i)): Width.Covered (boom α (∏ i∈t,x i)) (∏ i∈t,y i):=by
  induction t using Finset.induction with
  | empty => simp only [prod_empty,identity]; intro i; simp only [Poly.one_part]; split <;> simp
  | insert i t hi ih => rw [prod_insert hi,prod_insert hi]; exact multiply hp (hx i (mem_insert_self _ _)) (ih fun i hi=> hx i (mem_insert_of_mem hi))
lemma forceMerge (S : (layout X).Stock p R o) (e:ℕ≃ X.Pellet) (U':Config G n)(f:Ovens.Label→ Poly R) (hF : ∀ i, Width.Covered (boom α (S.ink i U')) (f i)) (i:ℕ) : Width.Covered (boom α (marked e S i U')) (wallet e f i):= by
    let v:= full hp (x:=fun j=> S.ink j U') (e i).val (fun i _=>hF i); rw [marked_eq]; split; exact v; rw [(boom α).map_zero]; exact v.zero
namespace Hard
-- Only *for budgets*. Re-express independently.The support, vacuum & Θ stay.
def metal (H:QuadraticLocal.Hard T p P F o R)(z:ℝ) : QuadraticLocal.Hard T p P F o R where
   hard t i:= boom z ∘ H.hard t i
   locality t i:= by
     let h:= H.locality t i; refine ⟨fun a U=> congr_arg (boom z) (h.gauge a U), (boom z).continuous.measurable.comp h.borel,fun U V hx ht=> congr_arg (boom z) (h.reads U V hx ht), fun U j hj W hw=> h.carry U j ?_ W hw⟩
     intro he; apply hj; rw [Function.comp_apply, paid, he,mul_zero]
   charged t i U he:= H.charged t i U (fun hx => he (by rw [Function.comp_apply, hx]; exact (boom z).map_zero))
   quiet t i U:= (silent (H.hard t i U) z).trans (H.quiet t i U)
lemma metallic (H:QuadraticLocal.Hard T p P F o R)(h:(metal H α).Paid w B a b): H.Paid w B a b:= by
    obtain ⟨f,hf,h⟩:=h.wages; exact ⟨f,fun i t U'=> middle hp (x:=H.hard t i U') (hf i t U'),h⟩
lemma transported (H : QuadraticLocal.Hard T p X.kernel d.forced o R)(e:ℕ≃ X.Pellet)(h: QuadraticLocal.Hard.Soft X d p)(hF:(metal H α).Paid w p.B (a+1) m)
    (hK: QuadraticLocal.Hard.SoftPrice X d p.B (a+1) k)(ht:Payments.Rates p.B W m k κ)(hw:∀ i,0<w i)(ha:0≤a): (metal (H.transport e h) α).Paid w p.B a W:= by
    obtain ⟨f,hf,hH⟩:= hF.wages; let L:= metal H α; obtain ⟨g,hg,hG⟩:= QuadraticLocal.Hard.combinePays L h hw ha (fun t i U=> hf i t U) hH hK ht
    let A:= Payments.inflation m k κ; let χ:=Real.exp κ; have he:= Attached.payment e (p:=p) hw ha (Real.one_le_exp ht.heading) (show 0≤ A from add_nonneg (mul_nonneg (Real.exp_pos _).le ht.hard) (mul_nonneg zero_le_two ht.soft)) hG ht.capital; refine ⟨wallet e g,fun i t U'=>forceMerge hp (H.stock h t) e U' g ?_ i,fun i=> budget_loosen (he i) (?_: (Real.exp A-1)/χ≤ W)⟩
    · intro j; rcases j with j|j; exact hg (Sum.inl j) t U'; rw [show (H.stock h t).ink (.inr j) U'= Poly.send R.quiet (↑(Ovens.Pipes.reach d (Sum.inr j) U'):ℂ) from rfl, scalar]; exact hg (Sum.inr j) t U'
    apply le_trans (le_of_eq ?_) ht.returns; rw [div_eq_inv_mul,Bid.quote,Real.exp_neg]
lemma through {U W: Activities G n}{a':ℝ}(D:Kiosk.First p U W m a' a)
    (hw:∀ i,0<w i)(ha:0≤a)(H:QuadraticLocal.Hard T p U.forced U.K o R)(hx:(metal H α).Paid w p.B (a+1) m): (metal (Kiosk.First.led H D) α).Paid w p.B a a':= by
    let L:= Kiosk.shape D.oldP D.oldV H; have h:(metal L α).Paid w p.B (a+1) m:= by let v:= Kiosk.turned D.oldP D.oldV (metal H α) hx; exact v; -- [Fintype V] needed?
    let v:= transported hp L D.roll D.softens h D.softPaid D.funds hw ha; let f':=(Kiosk.turned D.projection.symm D.keeps.symm _ v); exact f'
-- void shift transport below for many mask continuations (induced shifts implemented later)
end Hard
end YM.QuadraticLocal.Throng

namespace YM.QuadraticLocal.Throng
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Payments Rack
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {ι μ T : Type*} {w : V → ℝ} {a α β δ γ κ k m b W D r : ℝ} {B : ℕ}
namespace Hard
variable (L':QuadraticLocal.Hard T p X.kernel d.forced o R) (h:QuadraticLocal.Hard.Soft X d p)
variable [Fintype V] [Countable ι](Z: Canopy.ShiftRows T ι G p o R)
-- currently used case: homogeneous shifts with all marked orders, not assuming radius power by arity.
def shift (α:ℝ) : Canopy.ShiftRows T ι G p o R where
   place:=Z.place
   soap t i U':= (α:ℂ) • Z.soap t i U'
   cost t i:= by
      let h:= Z.cost t i; refine ⟨fun g U'=> congr_arg _ (h.gauge g U'),Measurable.const_smul h.borel (α:ℂ),fun U' V hx ht=>congr_arg _ (h.reads U' V hx ht),fun U' j hj W hw=> h.carry U' j ?_ W hw⟩
      intro he; apply hj; rw [Poly.part_smul,he,mul_zero]
   clean t i U' hj:= Z.clean t i U' (fun he=>hj (by rw [he,smul_zero]))
   single t i U':= by rw [smul_mul_assoc, mul_smul_comm, Z.single,smul_zero,smul_zero]
   skip t i U':= by rw [Poly.part_smul,Z.skip,mul_zero]
set_option quotPrecheck false
local notation "S'"=> shift Z α
local notation "Φ"=> Z.packPost
local notation "X'"=> drawer G n
local notation "d'"=> widen X d
local notation "T'"=> Canopy.ShiftRows.stock Z h L'
local notation "L₁"=> QuadraticLocal.Hard.readdress (A:=X.pours d) L' (preserves X d p)
local notation "L★"=> QuadraticLocal.Hard.readdress (A:=X.pours d) (metal L' α) (preserves X d p)
local notation "Std"=> QuadraticLocal.Hard.stock L₁ (Canopy.ShiftRows.softWide h)
local notation "M++"=> metal L' α
local notation "St'"=> Canopy.ShiftRows.stock S' h M++
omit [Fintype V] in
lemma metal_packs (t:T) (U':Config G n) (i:ℕ): (S').placed t i U'= boom α (Z.placed t i U') := by
   by_cases hi:i∈ Set.range Φ
   · obtain ⟨i,rfl⟩:=hi
     change stuff (Z.packPost) ((S').soap t) (Φ i) U'= _; rw [Canopy.ShiftRows.placed, stuffed Φ,stuffed Φ]; unfold shift; dsimp only; ext1 j; rw [Poly.part_smul,paid]; unfold weight; split; next hv=>
       subst j; rw [Z.skip,mul_zero,mul_zero]
     next=> rfl
   unfold Canopy.ShiftRows.placed; rw [show (S').packPost=Z.packPost from rfl,blank (Z.packPost) _ hi,blank (Z.packPost) _ hi]; exact (boom α).map_zero.symm
lemma metalized (t:T)(U':Config G n)(i:Ovens.Label): (St' t).ink i U'= boom α ((T' t).ink i U') :=by
   cases i with
   | inl i =>
       let A := upK X; change (L★).hard t i U'=boom α ((L₁).hard t i U'); by_cases h:i∈ Set.range A
       · obtain ⟨i,rfl⟩:=h; unfold QuadraticLocal.Hard.readdress; dsimp only; rw [stuffed A, stuffed A]; rfl
       unfold QuadraticLocal.Hard.readdress; dsimp only; rw [blank A _ h,blank A _ h]; exact (boom α).map_zero.symm
   | inr i=>
       change (Std t).slipVal i U'+(S').placed t i U'= boom α ((Std t).slipVal i U'+Z.placed t i U'); rw [(boom α).map_add, show boom α ((Std t).slipVal i U') = _ from (scalar (α:=α) (R:=R) (↑(Real.exp ((d').logarithm i U')-1):ℂ)),metal_packs]; rfl
lemma sheltered (hp:1≤α) (hV:(metal L' α).Paid w p.B (a+1) m) (hx:QuadraticLocal.Hard.SoftPrice X d p.B (a+1) k)
     (hZ : (shift Z α).Budget w p.B (a+1) r) (hq:Rates p.B W m (k+r) κ)(hw:∀ i,0<w i)(ha:0≤a): (metal (Z.poster h L') α).Paid w p.B a W:=by
    obtain ⟨f,hF,hG⟩:= (shift Z α).prices h (metal L' α) hw ha hx hV hZ hq
    let χ:=Real.exp κ; let A:= inflation m (k+r) κ;
    let he:= Attached.payment (p:=p) (folio G n) hw ha (Real.one_le_exp hq.heading) (show 0≤ A from add_nonneg (mul_nonneg (Real.exp_pos _).le hq.hard) (mul_nonneg zero_le_two hq.soft)) hG hq.capital; refine ⟨_,fun i t U'=> forceMerge hp (T' t) (folio G n) U' f (fun j=> by rw [← metalized]; exact hF j U' t) i,fun i=> budget_loosen (he i) (?_: (Real.exp A-1)/χ≤ W)⟩
    apply le_trans (le_of_eq ?_) hq.returns; rw [div_eq_inv_mul,Bid.quote,Real.exp_neg]
lemma president {U' W': Activities G n}{a':ℝ}(D:Kiosk.Second p U' W' m a' a r)
    (hw:∀ i,0<w i)(ha:0≤a)(hp:1≤α)(H:QuadraticLocal.Hard T p U'.forced U'.K o R)(hx:(metal H α).Paid w p.B (a+1) m) (hZ : (shift Z α).Budget w p.B (a+1) r): (metal (Kiosk.Second.canopy H Z D) α).Paid w p.B a a':= by
    let L:= Kiosk.shape D.oldP D.oldV H; have h:(metal L α).Paid w p.B (a+1) m:= by let v:= Kiosk.turned D.oldP D.oldV (metal H α) hx; exact v
    let v:= sheltered L D.softens Z hp h D.softPaid hZ D.funds hw ha; let f':=(Kiosk.turned D.projection.symm D.keeps.symm _ v); exact f'
end Hard
end YM.QuadraticLocal.Throng
