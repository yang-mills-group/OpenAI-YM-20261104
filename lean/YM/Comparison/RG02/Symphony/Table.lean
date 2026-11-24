import YM.Comparison.RG02.Symphony.Clarity
import YM.Push.LOOP_COEFFICIENT.Coefficient
/-!
# Kinetic witness at the *output period-limit* (pre-regulator removal)

 The canonical local Caliber is taken using cover-wave symbols, not guessing from finite fits.
 Quantized on **all** grids with their actual period paths. Positions lifted reconstruction by
 Sky & eventual Fk authorization separately; only rank-two here. Offer.Mirrors does NOT assert
 that cofinal inputs exist. Comes from the prescription and primitive limits and comparison, not
 declaring it to identify two different regulator schemes. Body derives Ward conclusions over
 any such Offers. They supply real sign/metric orientation incl per-site volume convention. Use
 these or adapt via explicit equality of germ. Signs: Offer means symbol of negative ground
 (action kernel before coupling reexpression). Uses a transverse probe on the Hessian
 of that action (all loop terms included). Rescale normalizes to +1 on kinetic normalized curvature; prove its entire
 momentum order <=3 vanishes on the REAL-oriented branch symbols for all e>=1 with compatible
 Offers (norm prices separately). No claims on e+1 budgets. Covers optional compatible
 source polynomials too (need scalar branch for rank-one & two and parity separately; export
 fee test presently vacuum). Low Plan is enough to construct at that order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Symphony
open Function Filter Finset MeasureTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Laplace Symmetry Symmetry.Orbit
open Moving Moving.Path Moving.Shift Valence Adjacent Assembly LocalScript
open Matrix Push.Loops Laurent Bloch YM.Work.F05
open YM.AnalyticNext.QuarticMatch.Joint (shifts)
open scoped Topology BigOperators Classical ContDiff -- *not* default Matrix Norm Frobenius
open scoped Matrix.Norms.L2Operator
variable {G:Gauge} {n:ℕ→Side} {i:ℕ} {M:ℕ→ℤ} {r k:ℕ}
abbrev FamilyCoeff (G:Gauge)(s:ℕ→Side):= ∀ i, fieldDir G (s i) 1→ℂ
abbrev Columns (G:Gauge)(s:ℕ→Side):= ℕ→ FamilyCoeff G s
abbrev SpecK (G:Gauge):= Momentum → Matrix (Axes G) (Axes G) ℂ

variable {U:FamilyCoeff G n}{p:SpecK G} (a:G.ColorIndex)
structure Offer (p:SpecK G)(U:FamilyCoeff G n) : Prop where
    smooth : ContDiffAt ℂ ω p 0
    referral : LinkMirror (fun i=> Clarity.value (U i)) p
lemma zero_probe : probe₂ (0:SpecK G) a=0 := by simp [probe₂,mark,lineD]
namespace Offer
variable (h:Offer p U)
include h
section
variable (he:Expands n)
include he
lemma uniqueS {q:SpecK G} (H:Offer q U)(x:Momentum)(hz:star x=x): p x=q x:= Mirrors.unique h.referral H.referral he hz
lemma unique_price {q:SpecK G} (H:Offer q U): probe₂ p a=probe₂ q a := probe_congr a h.smooth H.smooth (fun p hp=> h.uniqueS he H p hp)
lemma unique_tap {V:FamilyCoeff G n}{s:SpecK G} (H: Offer s V)(hz:∀i, Clarity.value (U i)=Clarity.value (V i)): probe₂ p a=probe₂ s a := h.unique_price a he (Offer.mk H.smooth (by simp_rw [hz]; exact H.referral))
variable (hp:∀i, Clarity.Body (U i))
include hp
lemma signature: Signature G true p := Clarity.accepted he hp h.referral
lemma kinetic : Signature.Short p 2:= (h.signature he hp).short_two h.smooth
lemma paid : ((probe₂ p a).re:ℂ)=probe₂ p a:= (h.signature he hp).probe_real h.smooth a
lemma color_one (b:G.ColorIndex)(hG:G.Simple) : probe₂ p b= probe₂ p a:= by
   unfold probe₂; rw [(h.signature he hp).mark_color h.smooth hG a]; simp
lemma textile (hG:G.Simple) {V:FamilyCoeff G n}{s:SpecK G}(H:Offer s V)(ht:∀i,Clarity.Body (V i))(hW:probe₂ s a=1): Signature.Short (fun u=>p u-(probe₂ p a) • s u) 4 := (h.signature he hp).relative_four h.smooth hG (H.signature he ht) H.smooth hW -- zero momentum after subtract
end

omit h
lemma none {U:FamilyCoeff G n} (hg: ∀ i, Clarity.value (U i)=0) : Offer (0:SpecK G) U := by refine ⟨contDiffAt_const,?_⟩; intro x f k hx hf hh; simp_rw [hg,map_zero,Push.Loops.sample,Matrix.mul_zero,Matrix.zero_mul,smul_zero]; exact tendsto_const_nhds
private lemma pool_mirror {A B : ∀ i,Matrix (BondKey G (n i)) (BondKey G (n i)) ℝ}{V W : SpecK G} (hA:LinkMirror A V)(hB:LinkMirror B W): LinkMirror (fun i=>A i+B i) (V+W) := by
   intro x f k hx hf h; simp_rw [map_add,sample_add]; exact (hA x f k hx hf h).add (hB x f k hx hf h)
private lemma weigh_mirror {A: ∀ i,Matrix (BondKey G (n i)) (BondKey G (n i)) ℝ}{p:SpecK G}(h:LinkMirror A p)(x:ℝ): LinkMirror (fun i=>x • A i) ((x:ℂ) • p) := by
    intro v f k hx hf H
    simp_rw [show ∀ i,cmat (x • A i)= (x:ℂ) • cmat (A i) from fun i=>by rw [map_smul]; ext j l; exact Complex.real_smul ..]
    simp_rw [sample_smul]; exact tendsto_const_nhds.smul (h v f k hx hf H)
private lemma combination {S:Type*} (f : Finset S){p:S→SpecK G} {A:S→ ∀ i,Matrix (BondKey G (n i)) (BondKey G (n i)) ℝ}(h:∀s∈f,LinkMirror (A s) (p s)) (x:S→ℝ) : LinkMirror (fun i=>∑ s∈f, x s • A s i) (∑ s∈f,(x s:ℂ) • p s) := by
    induction f using Finset.induction with
    | empty=> simp only [sum_empty]; intro i g k hp hf hh; simp_rw [map_zero, Push.Loops.sample,Matrix.mul_zero,Matrix.zero_mul,smul_zero]; exact tendsto_const_nhds
    | insert z V hz ih=> simp_rw [sum_insert hz]; exact pool_mirror (weigh_mirror (h z (mem_insert_self ..)) _) (ih fun i hi=>h i (mem_insert_of_mem hi))

lemma alongS {S:Type*}(L:Finset S)(x:S→ℝ) {H:S→SpecK G} {p:S→FamilyCoeff G n} {V:FamilyCoeff G n} (he:∀i∈L,Offer (H i) (p i))(hp:∀i, Clarity.value (V i)=∑ j∈L, x j • Clarity.value (p j i)): Offer (∑ j∈L,(x j:ℂ) • H j) V := by
   constructor
   · rw [show _root_.Finset.sum L _= _ from funext fun p=> (show ((∑ j∈ L,(x j:ℂ) • H j):SpecK G) p= _ from Finset.sum_apply ..)] ; exact ContDiffAt.sum fun i hi=> ((he i hi).smooth).const_smul (x i:ℂ)
   simp_rw [hp]; exact combination L (A:=fun j i=> Clarity.value (p j i)) (fun i hi=> (he i hi).referral) x

lemma payment {S:Type*}(L:Finset S)(x:S→ℝ) {H:S→SpecK G} {p:S→FamilyCoeff G n}(he:∀i∈L,Offer (H i) (p i)): probe₂ (∑ j∈L,(x j:ℂ) • H j) a=∑ j∈L,(x j:ℂ) * probe₂ (H j) a := by
    induction L using Finset.induction with
    | empty=> rw [sum_empty,sum_empty,zero_probe]
    | insert z V hz ih=> rw [sum_insert hz,sum_insert hz]; have hU (i) (h:i∈V):= he i (mem_insert_of_mem h); rw [probe_add _ (V:=(x z:ℂ) • H z) ((he z (mem_insert_self ..)).smooth.const_smul (x z:ℂ)) (show ContDiffAt ℂ ω (∑ j∈V,(x j:ℂ) • H j) 0 from ?_), probe_smul, ih hU]
                         rw [show _root_.Finset.sum V _= _ from funext fun p=> (show ((∑ j∈ V,(x j:ℂ) • H j):SpecK G) p= _ from Finset.sum_apply ..)]; exact ContDiffAt.sum fun i hi=> (hU i hi).smooth.const_smul (x i:ℂ)
end Offer

end YM.Comparison.RG02.Symphony
