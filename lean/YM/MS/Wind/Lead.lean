import YM.MS.Wind.Portfolio
/-!
# Order-by-order preserving initial triangularity

Dimension/arity calibration. Degree at top from `BIndex` picks a single basis element.
 At this grade actual monomial content could mix all metric contractions; don't
 assume color-irreducible. Movement even on $∆$ high mark context.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Wind.Leading
open Function Filter Set Finset Plane Koszul Flux MeasureTheory Real
open Landau Native Lattice Tone Momentum Heat Frame Wire Color Detect Native.Wilsonian Paint
open Book Convolve City Logarithm Program Signal High Menus Lifting Knobs Local.Physical
open Complex (I)
open scoped Topology ContDiff
variable {G:Gauge}{p:Team}{B:Deck G}{d:ℕ}(V: LitBook B)(j:Glyph B d){F:Tact B d}{P: Acts B d}{n r:ℕ}{u:ℤ}

-- reserve one label at order0
structure FitOrder (j:Glyph B d)(F:Tact B d): Prop where
   Low (x:ℝ): Limit (F.proof.input x).val (j.grade-1)
   Single (i:Glyph B d): j.grade ≤ i.grade→ F.register i= if i=j then 1 else 0
abbrev Tactic0 (j: Glyph B d)(i:ℕ):= {F:Tact B d // i=0→ FitOrder j F}
def script (j: Glyph B d) (i:ℕ): Tactic0 j i:= ⟨ { register:= fun i=> if i=j then 1 else 0, proof:=0 }, fun _=> ⟨fun _ _ _=>rfl, fun _ _=>rfl⟩ ⟩
def clockM (j:Glyph B d)(A: Code (Tactic0 j)): Acts B d:= fun i=> (A i).val

def trio (p:Team) : Knobs (Tactic0 j) G where
    wake P:= (Seek V p d).wake (clockM j P)
    stay _ _ _ h:=(Seek V p d).stay _ _ _ (fun i hi=>congr_arg Subtype.val (h i hi))
lemma fix_order {j:Glyph B d}{u:ℤ}(h:FitOrder j (P 0)){X: Price B d}{Y: Power G}(hx:Glyph.Homes X u r)(hy:Y.allowance≤r)(hv:r<j.grade ∨ 0<n): FitOrder j (Menus.patch P X Y n 0):= by
   unfold Menus.patch; split; swap; exact h
   next ht=>
      have hu:r< j.grade:=by omega
      refine ⟨fun x=> Limit.sub (h.Low x) (Limit.up (Y.ranks x) (by omega)),fun i hi=>?_⟩; change (P 0).register i - X i= _; have hg : X i=0:= Classical.byContradiction (fun H=> Nat.not_lt_of_ge hi (hx.grade i H|>.symm ▸ hu)); rw [h.Single i hi,hg,sub_zero]

section fits
variable (p) {j}
lemma cap0 (h: FitOrder j (P 0))(x:ℝ) : Limit (score V p P x 0).val j.grade ∧ Fits (score V p P x 0) j.read j.grade j.size false:= by
   let A0:=score V p P x 0; let f (c:Glyph B d):= oil P c 0 x • Glyph.preamble V p c x 0; let Y:Finset (Glyph B d):=Finset.univ.erase j; let Z:=Glyph.preamble V p j x 0; let T:= motto p P x 0; let U:= T + ∑ i∈Y,f i; have he : A0= Z+U:= by
       unfold A0 score U T; rw [Pi.add_apply, add_left_comm,add_comm]; congr 1; unfold Menus.rent; simp_rw [Finset.Nat.antidiagonal_zero,Finset.sum_singleton]; change ∑ c,f c=Z+∑ c∈Y,f c;
       rw [← Finset.add_sum_erase _ f (Finset.mem_univ j)]; unfold f oil; rw [h.Single j (le_refl _), if_pos rfl,Polynomial.eval_one,Complex.ofReal_one]; rw [one_smul]
   have hr : Limit T.val ((j.grade:ℤ)-1):= by
       have hl := h.Low x; let Q :=(P 0).proof; have hh:T= Menus.advance (Q.input x):= by simp only [T,sky,Finset.Nat.antidiagonal_zero,Finset.sum_singleton, style,whoZero]; rfl
       rw [hh]; exact Limit.add (Limit.up (lapLimit hl) (by omega)) (Limit.up (rootLimit (participates G 0) hl) (by omega)) -- root found Lifting
   have hi i (hi:i∈Y): Limit (f i).val ((j.grade:ℤ)-1):= by
       rcases lt_or_ge i.grade j.grade with hI|hI; · exact Limit.up (Limit.smul _ (Glyph.pre_cost V p i x 0)) (by omega)
       unfold f oil; rw [h.Single i hI,if_neg (Finset.mem_erase.mp hi).1,Polynomial.eval_zero,Complex.ofReal_zero,zero_smul]; exact fun _ _=>rfl
   have hL : Limit U.val ((j.grade:ℤ)-1):= by refine Limit.add hr ?_; rw [Cylinder.sum_stack]; exact Limit.sum _ hi
   rw [show score V p P x 0=_ from he]; refine ⟨Limit.add (by convert Glyph.pre_cost V p j x 0 using 1; simp) (Limit.up hL (by omega)),?_⟩; suffices ht : Fits U 0 j.grade j.size false from by rw [← add_zero j.read]; exact (Glyph.pre_floor V p j x).add ht
   unfold Fits; rw [maskOff (by omega) (Tone.oneRank hL)]; exact face_zero _
lemma zerosOrder (h:FitOrder j (P 0))(x:ℝ) : let U:= horizon V p P 0 x; Rank U j.grade ∧ ∀ t,Lifting.Face wfield (Book.mask j.grade (U t)) j.read j.size false:= by
   intro U; let M:= (aqua V p P); obtain hz:= M.recu 0 x; obtain hx := cap0 p V h x; change U 0 = _ ∧ _ at hz;
   have hv: Wind.Near false U:= by obtain ⟨r,hr⟩:= (M.owes 0).pay; refine ⟨((M.owes 0).stay x).joint,⟨r,hr x⟩,fun t w _=>?_⟩; have hl:=hz.2 t w; simpa only [Pi.add_apply, Wind.path,Domain.paths,Finset.Ico_self,Finset.sum_empty,smul_zero,Pi.zero_apply,add_zero] using hl
   obtain ⟨h0,hg⟩:= Dprecise hv (r:=j.grade) (hz.1 ▸ oneRank hx.1); refine ⟨h0,fun t=>?_⟩; rw [show Book.mask _ (U t)=Book.mask _ (U 0) from ?_,hz.1]; exact hx.2; funext w; by_cases he:(w.length:ℤ)=j.grade; simp only [enough _ he,hg w he]; simp only [strange _ he]
end fits
structure PhysicalHF (j:Glyph B d)(F:Recount G): Prop where
   owns : j.size=d
   too (x: Clock ℝ): Limit (F 0 x) j.grade
   top (x: Clock ℝ): Book.mask j.grade (F 0 x)= j.read
end YM.MS.Wind.Leading
