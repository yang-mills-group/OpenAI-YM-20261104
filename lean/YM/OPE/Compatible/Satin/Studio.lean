import YM.OPE.Compatible.Copper.Harvest
/-!
# Pivot readout linear forms (P root coefficients and balance) at fixed child map

Need powers for DIFFERENCE, not charging the matched v term alone. Obtain signed bounds via replacing b at cost \|Q-space residual\| in the indicated *full weight d level*; slots are linear on the quotient at each horizon (right sides sometimes use loaded letters with that grading). Matching into projected root before Real transfer. Keep overlapping arrays per copy; algebra only at quotient.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S)(P:Prescription T.sector.derivatives){u:X}
variable (p:X→ C.book.Token)(n d:ℕ){z:X→ E4}
set_option quotPrecheck false
local notation "Y"=> brim D (Arboreal.trim U u)
local notation "V"=> shore D U u
local notation "H"=> (picked Y z)
local notation "H'"=> picked V z
local notation "p'"=> picked V p
local notation "m"=> T.sector.derivatives
variable [Fintype I] (c:Viewers T){x:I→ E4}(w:I→ C.book.Token)
-- linear observe front plus measure continuity. quotient
variable (h:Crown U)(hp:u∈ rest U)(hx: Injective (beside (picked (brim D (Arboreal.trim U u)) z) x))
include h hp hx
lemma pointed (a:C.label d) : observe (spectator T c) (beside H x) (beside (picked Y (update p u (⟨d,a⟩: C.book.Token))) w) = Cov.insert S (spectator T c) (z u) (beside H' x) (beside (picked V (S.classTokens ∘ p)) (S.classTokens ∘ w)) d (S.project d a):=by
    let P':= spectator T c; let u₀:S.Tag := ⟨d,S.project d a⟩; have hz:= spectate T c; let s:= update p u (⟨d,a⟩: C.book.Token) -- remove let
    have hK:= Cov.kernel_observe (S:=S) hz.laws.toSymmetric (spectate_respects T c) hx (beside (picked Y s) w)
    have hQ: S.classTokens ∘ beside (picked Y s) w=beside (picked Y (update (S.classTokens ∘ p) u u₀)) (S.classTokens ∘ w):=by
        funext i; cases i
        next i=> by_cases hi:i.val=u
                 · change S.classTokens (update p u _ i.val)= update (S.classTokens ∘ p) u u₀ i.val; rw [hi,update_self,update_self]
                 change S.classTokens (update p u _ i.val)= update (S.classTokens ∘ p) u u₀ i.val; rw [update_of_ne hi,update_of_ne hi]; rfl
        rfl
    rw [hQ] at hK
    have hy: Injective (beside (sole (z u)) (beside H' x)):=by
        let P := (Equiv.sumAssoc Unit V I).symm.trans (Equiv.sumCongr (trails D U u h hp) (Equiv.refl I)); rw [show beside (sole (z u)) (beside H' x)= beside H x ∘ P from funext fun i=> by rcases i with i|i|i <;> rfl]; exact hx.comp P.injective
    rw [Cov.insert_apply S hz.laws.toSymmetric (spectate_respects T c) (z u) _ _ d (S.project d a) hy,passing D U u hz.laws.toSymmetric z (S.classTokens ∘ p) u₀ x _ h hp hx]; exact hK.symm
variable (z)
omit hx
-- totalized coefficients linear for input fields. At off collar reading=0. linear. `Cov.insert` with relative center for detector. Need x:a(v) moved - root; root center fixed 0 here.
def stationReading (e:Exterior C.book):S.Field d→ₗ[ℂ]ℂ:= if Injective (beside (picked (brim D (Arboreal.trim U u)) z) (bearing e)) then Cov.insert S S (z u) (beside (picked V z) (bearing e)) (beside (picked V (S.classTokens ∘ p)) (S.classTokens ∘ e.letter)) d else 0
include T
lemma tagged (a:C.label d)(e:Exterior C.book): Prescription.reading S (picked Y z) (picked Y (update p u (⟨d,a⟩: C.book.Token))) 0 e=stationReading D p d z (u:=u) (U:=U) e (S.project d a):=by
    unfold stationReading Prescription.reading; dsimp only; simp only [sub_zero]; split; next he=> exact pointed _ T p d (x:=bearing e) none _ h hp he a
    rfl -- 0 map
-- printed operators
local notation "H₀"=> picked (brim D (Arboreal.trim U u)) z
omit h hp
def tipMark (U:Finset X)(u:X)(b: Mode T.sector.derivatives): S.Field d→ₗ[ℂ]ℂ:=∑ e∈(P.sheet b).support, (P.sheet b e) • stationReading D p d z (U:=U) (u:=u) e
include h hp
lemma printed (a:C.label d)(b:Mode T.sector.derivatives): P.ope b H₀ (picked Y (update p u (⟨d,a⟩: C.book.Token))) 0= tipMark D T P p d z U u b (S.project d a):=by
    unfold tipMark Prescription.ope; simp_rw [LinearMap.sum_apply]; refine sum_congr rfl fun i _=>?_ ; rw [tagged D T _ _ _ h hp]; rfl -- args
-- truncated map at root for secondary term
variable {z}
include hx
lemma pole_balance : ∃ L': S.Field d→ₗ[ℂ]ℂ, ∀ a:C.label d,
     observe (spectator T c) (beside H x) (beside (picked Y (update p u (⟨d,a⟩: C.book.Token))) w)- P.truncated (spectator T c) n H (picked Y (update p u (⟨d,a⟩: C.book.Token))) 0 x w=L' (S.project d a):=by
    let V'(b:Mode T.sector.derivatives):= observe (spectator T c) (beside (sole (0:E4)) x) (beside (sole (P.letter b)) w)
    refine ⟨Cov.insert S (spectator T c) (z u) (beside H' x) (beside (picked V (S.classTokens ∘ p)) (S.classTokens ∘ w)) d-∑ b∈bands m n,V' b • tipMark D T P p d z U u b,fun a=>?_⟩; rw [pointed _ _ _ _ _ _ h hp hx]; unfold Prescription.truncated; simp_rw [LinearMap.sub_apply, LinearMap.sum_apply]; congr 1; refine sum_congr rfl fun i _=>?_; unfold Prescription.termRead; rw [printed D T P _ _ _ h hp] -- params
    change _= V' i* _; exact mul_comm ..
end YM.OPE.Arboreal.Trace
