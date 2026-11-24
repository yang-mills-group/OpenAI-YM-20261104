import YM.QuadraticLocal.Germ.Scribe
import YM.QuadraticLocal.HaloMix.Yield
/-!
# Compatible mark deletion at the supported stencils, incl. merged force

Erase by zeroing the variables not in the retained list. Keep full
 dimensional census for the retained-marker requests. This includes preimage
 aggregation remaining untouched; exact on unnormalized densities (and pass
 & log) and basis orders. *Also* works on the already combined Roll
 and Calendar epochs. Not claiming independent runs of the ORIGINAL compiler
 on a deleted dictionary will give exactly these representatives. Choose the
 representation first and implement requests at the retained list on THIS one.
 A theorem matching skills/local precision under deletion is still separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Deletion
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 RG3.Ink Ovens Ovens.Pipes Progress.DirectedRecipe Fusion Attached Push.Local
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} {X : Pipes G n} {d : Tap G n} {p : BudgetPoint}
variable {V : Type} [DecidableEq V] {R : Census V} {o : V → Site n}
variable {T J : Type*} {w : V → ℝ} {a α β γ k b r :ℝ} {B : ℕ}
variable {P : ℕ→ ForcedAddress G n} {F : Code G n} {S:Set V}
variable (R) (S) in
noncomputable def crop : Poly R→L[ℂ] Poly R:= ModeWeight.turn R (fun i => if i∈S then 1 else 0)
-- permit/list budget explicitly, regardless of any kernel-based absorption after projection
-- note: ∀ s in R.terms finite by Census. Don't request selection adaptively with t.We.Shape.
def preserve (s:Finset V)(S:Set V): Prop:= ∀ i∈s,i∈S
variable (S)
set_option quotPrecheck false
local notation "Ζ"=> crop R S
@[simp] lemma watching (x:Poly R) (i:R.Mode): ( Ζ x ).part i = if preserve i.val S then x.part i else 0:=by
   unfold crop; rw [ModeWeight.scale]; split; next h=> rw [prod_eq_one (fun i hi=> if_pos (h i hi)),one_mul]
   next h=> unfold preserve at h; push Not at h; obtain ⟨j,hj,hh⟩:=h; rw [prod_eq_zero hj (if_neg hh),zero_mul]
@[simp] lemma quiet (x:Poly R): (Ζ x).part R.quiet=x.part R.quiet:= (watching S x _).trans (if_pos (show preserve _ _ from by simp [preserve,Census.quiet]))
lemma zeroMode (x:Poly R)(i:R.Mode) : (crop R ∅ x).part i= if i=R.quiet then x.part i else 0:=by
     rw [watching]; split; next h=> rw [if_pos (Subtype.ext (show i.val=∅ from Finset.eq_empty_iff_forall_notMem.mpr fun x hh=> Set.notMem_empty _ (h _ hh)))]
     next h=> rw [if_neg (fun ht=> h (by rw [ht]; intro i hp; exfalso; exact notMem_empty _ hp))]
-- Mode-space budget on any radius.
open Throng
variable (hw:∀ i,0<w i)
lemma cover (x y:Poly R)(h:Width.Covered x y): Width.Covered (Ζ x) (Ζ y):=by
     intro i; rw [watching,watching]; split; exact h i; simp
include hw
lemma paid (x:Poly R): Poly.price w (Ζ x)≤Poly.price w x:=by
     unfold Poly.price; refine sum_le_sum fun j _=>?_ ; apply mul_le_mul_of_nonneg_left _ (Poly.worth hw _).le; rw [watching]; split; exact le_rfl; rw [norm_zero]; exact norm_nonneg _
lemma paidK (x:Poly R): Throng.Hard.active w (Ζ x) ≤Throng.Hard.active w x:= by
     unfold Throng.Hard.active; rw [show GridRenewal.Rain.fresh (Ζ x)= Ζ (GridRenewal.Rain.fresh x) from ?_]; exact paid S hw _
     ext1 i; rw [Hard.hotPart,watching,watching,Hard.hotPart]; split_ifs <;> rfl
omit hw
lemma forever (m:R.Mode)(z:ℂ): Ζ (Poly.send m z)= Poly.send m (if preserve m.val S then z else 0):= by
     ext1 i; rw [watching]; by_cases h:i=m; · subst i; simp
     simp [h]
-- quiet part valid despite exports to View.T: projection is inert on `F` at ALL fields
variable (L:Lamps T J G p o R)
def sink : Lamps T J G p o R:={L with
    nominal t i:= if preserve (L.mode i).val S then L.nominal t i else fun _=> 0
    legal t i:= by split; exact L.legal ..; exact regular_const _
    pure t i U he:= by split; exact L.pure t i U he; rfl }
local notation "U!"=> sink S L
lemma light (i:J)(t:T)(U:Config G n): (U!).light t i U= if preserve (L.mode i).val S then L.light t i U else 0:=by
     unfold Lamps.light; change (if L.clear i then _ else masked p.threshold (L.ground i) _ U)=_; split
     · by_cases h: preserve (L.mode i).val S
       · unfold sink; simp only [if_pos h]
       unfold sink; simp only [if_neg h]
     next _ =>
        simp only [sink]; split; exact rfl; next _ =>
     
           by_cases h': Healthy p.threshold (L.ground i) U; rw [masked_eq _ _ _ _ h']; rw [masked_ne _ _ _ _ h'] -- inspect
-- retains exact dimensions and every address incl. dark (value outside mask now also dark on a deleted slot)
lemma frame (i:J)(t:T)(U:Config G n): (U!).frame i t U= Ζ (L.frame i t U):=by
     unfold Lamps.frame; rw [forever S (L.mode i),light]; rfl
lemma owed (h:L.Paid w B a b): (U!).Paid w B a b:=by
     obtain ⟨f,hp,hf,hV⟩:= h.budget; refine ⟨f,hp,?_,hV⟩; intro i t y hy; unfold sink; dsimp only; split; exact hf i t y hy; exact bound_weaken (bound_const _) ((norm_zero (E:=ℂ)).trans_le (hp i)) -- E:=?
variable (H: QuadraticLocal.Hard T p P F o R)
def cork : QuadraticLocal.Hard T p P F o R where
   hard t i := fun x=> Ζ (H.hard t i x)
   locality t i := by
      let h:= H.locality t i; refine ⟨fun a U=>congr_arg (Ζ) (h.gauge a U),(Ζ).continuous.measurable.comp h.borel,fun U' V' hT hk=>congr_arg (Ζ) (h.reads U' V' hT hk), fun U' j hj ν hv=> h.carry U' j ?_ _ hv⟩
      intro he; apply hj; rw [watching, he, ite_self]
   charged t i U he:= H.charged t i U (fun h=>he (by rw [h]; exact (Ζ).map_zero))
   quiet t i U:= (Deletion.quiet S _).trans (H.quiet t i U)
local notation "Υ"=> cork S H
include hw
lemma cork_paid (h: H.Paid w B a b): Υ |>.Paid w B a b:=by
     obtain ⟨f,hf,hG⟩:= h.wages; let g i:= Ζ (f i); refine ⟨g,fun i t U=>Deletion.cover S _ _ (hf i t U),fun i=>budget_mono (hG i) (fun j=>by split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>by split; exact mul_le_mul_of_nonneg_right (paid S hw _) (Real.exp_pos _).le; exact le_rfl)⟩
lemma pair_paid (h:Throng.Hard.Pair H w B a b r): Throng.Hard.Pair Υ w B a b r:= by
    obtain ⟨f,hf,hG,hP⟩:= h.cashout; let g i:= Ζ (f i); refine ⟨g,fun i t U=>Deletion.cover S _ _ (hf i t U),fun i=>budget_mono (hG i) (fun j=>by split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>by split; exact mul_le_mul_of_nonneg_right (paid S hw _) (Real.exp_pos _).le; exact le_rfl),fun i=>budget_mono (hP i) (fun j=>by split; exact mul_nonneg (Hard.active_nonneg hw _) (Real.exp_pos _).le; exact le_rfl) (fun j=>by split; exact mul_le_mul_of_nonneg_right (paidK S hw _) (Real.exp_pos _).le; exact le_rfl)⟩
omit hw
variable {X0:Rep G n} (M:Gallery T J o X0 R)
def offer : Gallery T J o X0 R:= ⟨sink S M.E,cork S M.K⟩
open Affinity
variable {E:V→Type*}[∀ i,AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
lemma retention (t:∀ i,Set (E i))(K :∀ i,Submodule ℝ (E i)) (M: Gallery (Wallet t) J o X0 R)(X:V→Support n)(h:Collared X t K X0 M): Collared X t K X0 (offer S M):=by
    refine ⟨⟨h.lamps.house, fun i U=>?_⟩,⟨fun i U=>⟨fun j=>?_⟩⟩⟩
    · by_cases hV:preserve (M.E.mode i).val S
      · unfold offer sink; simp only [hV,↓reduceIte]; exact h.lamps.adv i U
      unfold offer sink; simp only [if_neg hV]; exact Attn.silent
    unfold offer cork; simp_rw [watching]; split; exact (h.hard.lesson i U).each j; exact Addressable.gone
variable (h:M.Pays w a b r) (ha:0≤a)
local notation "T!"=> offer S M
include h hw
lemma prices : (T!).Pays w a b r:=⟨owed S _ h.budget,cork_paid S hw _ h.wages⟩
variable [Fintype V]
include ha
lemma read (t:T)(U:Config G n): (T!).density t U= Ζ (M.density t U):= by
    have hE: (sink S M.E).log t U= Ζ (M.E.log t U):= by unfold Lamps.log; rw [(Ζ).map_tsum (h.budget.sums ha hw t U)]; exact tsum_congr fun i=> Deletion.frame S M.E i t U
    let f:=packet X0.activities X0.p (M.K.hard t) U
    have hF: (T!).gas t U= Ζ (M.gas t U):=by
       unfold Gallery.gas; rw [(Ζ).map_tsum (Hard.packet_summing M.K h.wages ha hw _ _)]; refine tsum_congr fun i=>?_ ; unfold packet; split; exact (ModeWeight.mult R _ i (fun i=> M.K.hard t i U)).symm; rw [(Ζ).map_zero]
    unfold Gallery.density; rw [(Ζ).map_smul,show Ζ (Poly.pass (M.E.log t U)*M.gas t U)= _ from ModeWeight.rum R _ _ _,hF,ModeWeight.pass,show (T!).E.log t U= Ζ _ from hE]; rfl
    -- show remaining equality
end YM.QuadraticLocal.Deletion
