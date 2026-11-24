import YM.FVAAlt2.Shop.Solution
/-!
# The **one** RichBook, from the actual localSection, for every weight and rank
Off shell stencil Family `S` at engineering h embeds precisely the given pure letter
(top `film` under `Γi.a`). W_N inverse with slots and full top cover kernel. Then
mark binding for the ACTUAL normalized bare columns. Linear on either complex or
real vectors with (prefixing) engineering embedding understood.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Shop
open Function Finset Filter Topology Wilson Labels Source Source.Drops
open Comparison.Stencils.Corona (Crumb Primary Binds Tally demonstrates act_simple plated scape bonded stage_zero printed)
open MS MS.Koszul MS.Native MS.Landau MS.Menus MS.Book MS.Cylinder MS.Cylinder.Taylor MS.Tone MS.Landau.Detect MS.Plane MS.Theater
open MS.Lifting MS.Local.Physical MS.Book.Convolve MS.Native.Studio MS.Native.Paint MS.Native.Wilsonian
open PertExtension PertExtension.Orb PertExtension.Orb.SlotEvaluation PertExtension.LatticePT
open Lattice
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{d k:ℕ}{F: Labels.Frame G d}
local notation "Θ"=> Lane4 G
variable (B:Deck G)
def seat (i:B.BIndex d k) : Label G d:= ⟨ film B i (h:=d),limitH ((cinema ..).mp (filmW B i (h:=d))).1, ((cinema ..).mp (filmW B i (h:=d))).2.1⟩
lemma isSeated (i:B.BIndex d k): seat B i∈ Grade (d,k):= (pure_grade (d,k) _).2 ( ( nodeId _ (d,k)).1 ((cinema ..).mp (filmW B i (h:=d))).1) -- parentheses
lemma single_p (i:B.BIndex d k): realBar (seat B i (d:=d))=seat B i:= Subtype.ext ( ((cinema ..).mp (filmW B i (h:=d))).2.2 )
def purchase (F:Labels.Frame G d)(v:B.BIndex d k) := F.coords (seat B v)
-- off listed grade
lemma cancel (p:F.Index)(v:B.BIndex d k)(he:F.grades p≠ (d,k)):purchase B F v p=0:= F.power_coefficient p he.symm (isSeated ..)
lemma track_real (p:F.Index)(v:B.BIndex d k):star (purchase B F v p)=purchase B F v p:= by
 let V:=seat B v (d:=d);
 rw [← F.conj_basis (purchase B F v) ]; unfold purchase; rw [LinearEquiv.symm_apply_apply,single_p]
-- quantities go **in** this stencil's order in all of the purchased history
variable (S:SectionData F){H:Hol G}(h:S.Sound H)(hp:Bid.pop S)
def valueP (v:B.BIndex d k)(p:F.Index): ℂ:= ∑ a:F.Index,purchase B F v a * (↑(topBasis S H h hp a p):ℂ)
lemma value_real (v:B.BIndex d k)(p:F.Index):star (valueP B S h hp v p)=valueP B S h hp v p:=by unfold valueP; rw [star_sum]; apply sum_congr rfl; intro i _; rw [star_mul', track_real]; simp
-- triangles. Proof after RG09/Head/Mint (independent of integration and MRank).
lemma mint_top(i j:F.Index)(he:(F.grades i).2 ≤ (F.grades j).2): (↑(topBasis S H h hp i j):ℂ)=(Pi.single i 1:F.Coeff) j:=by
 let T:= topMatrix S H h hp; let L:= T.conversion (covarianceSymbol G)
 rw [Vertex.true_coefficients]; change L.symm (Pi.single i 1) j=_; let u: F.Coeff := L.symm (Pi.single i 1); let Q:= covarianceSymbol G
 have hv : (∑ x:F.Index,u x • T.joint (Next.Rank.Normal.milk Q (T.basis x))) j=( Pi.single i 1:F.Coeff ) j:= congrFun (L.apply_symm_apply _) j
 rw [Finset.sum_apply,Finset.sum_eq_single j,Pi.smul_apply,T.coefficientMatrix (i:=j) (j:=j) le_rfl, Pi.single_eq_same, smul_eq_mul,mul_one] at hv; exact hv
 · intro b _ hb; by_cases hx:T.slots b ≤ T.slots j; · rw [Pi.smul_apply,T.coefficientMatrix hx,Pi.single_eq_of_ne (Ne.symm hb), smul_zero]
   rw [Pi.smul_apply,show u b=0 from T.inverse_slots (Q:=Q) (Pi.single i 1) (T.slots i+1) (fun a hz=> Pi.single_eq_of_ne (by intro h;rw [h] at hz; omega) _) b ( by have h':T.slots i≤T.slots j:=he; omega ),zero_smul]
 simp
lemma current_p(p:F.Index)(v:B.BIndex d k)(he:k ≤ (F.grades p).2): valueP B S h hp v p=purchase B F v p:=by
 unfold valueP; rw [sum_eq_single p,mint_top S h hp p p le_rfl, Pi.single_eq_same,mul_one]
 · intro x _ hx; by_cases ht:F.grades x=(d,k); · rw [mint_top S h hp x p (ht.symm ▸ he), Pi.single_eq_of_ne (Ne.symm hx),mul_zero] -- ▸ may require
   rw [cancel B x v ht,zero_mul]
 simp

abbrev priceS (S:SectionData F)(p:F.Index): ℕ→ Dot G Cover := Book.levels (F.grades p).2 ( origin S p )
def RBook (u:B.BIndex d k) := ∑ i:F.Index,valueP B S h hp u i • priceS S i
lemma pays_rank (u:B.BIndex d k)(j:ℕ): Limit (RBook B S h hp u j).val ((j:ℤ)+(k:ℤ)):=by
 unfold RBook; rw [Finset.sum_apply,sum_stack]; apply Limit.sum; intro i _; by_cases hv:(F.grades i).2≤k; · exact Limit.up (Limit.smul _ (Limit.mod (origin S i).val ((j:ℤ)+((F.grades i).2:ℤ)))) (by omega)
 rw [current_p _ _ _ _ _ _ (by omega),cancel B i u (fun ht=> by rw [ht] at hv; exact hv le_rfl),zero_smul]; exact fun _ _=>rfl
lemma summ_fit (u:B.BIndex d k): Fits (RBook B S h hp u 0) (B.raw d k u) k d false:=by
 suffices ht: Lifting.Face wfield (mask k (Tone.run (RBook B S h hp u 0))) (orbit G (seat B u (d:=d)).val) d false by rwa [← lamp_here B u]
 rw [ show orbit G _ = ∑ p:F.Index, purchase B F u p • orbit G (F.basis p).val from ?_ ]; swap
 · conv_lhs=> rw [← F.basis.sum_repr (seat B u)]
   simp_rw [Submodule.coe_sum,Submodule.coe_smul,map_sum,map_smul]; rfl
 unfold RBook; simp only [Finset.sum_apply,map_sum,Pi.smul_apply]; refine Lifting.face_sum fun i _=>?_ ; by_cases he:F.grades i=(d,k)
 · rw [current_p _ _ _ _ _ _ (he ▸ le_rfl), map_smul,map_smul]; apply Lifting.face_mul; have he' : mask k (Tone.run (priceS S i 0))=Tone.run (priceS S i 0):= by unfold priceS Book.levels; rw [Nat.cast_zero,zero_add, he]; simp_rw [Tone.grade, Glyph.mask_sq]; -- inspect
   rw [he']; exact (congr_arg (fun x:ℕ×ℕ=> (x.1:ℤ)) he) ▸ fitsCore S h hp i
 rw [cancel B i u he,zero_smul]; by_cases hx:k≤(F.grades i).2; · rw [current_p _ _ _ _ _ _ hx,cancel B i u he,zero_smul,map_zero,map_zero]; exact face_zero _
 have hx':mask k (Tone.run (valueP B S h hp u i • priceS S i 0))=0:=by
    have hy:Limit (Tone.run (priceS S i 0)) (F.grades i).2:= by
       unfold priceS Book.levels; rw [Tone.grade,Nat.cast_zero,zero_add]; exact Limit.mod _ _ -- pp
    rw [map_smul,map_smul]; rw [ maskOff (by omega : ( ((F.grades i).2:ℕ):ℤ) < (k:ℤ)) hy,smul_zero]
 rw [hx']; exact face_zero _
lemma rich (u:B.BIndex d k) : MarkFull (RBook B S h hp u) (B.raw d k u) d k:= by
 refine ⟨summ_fit B S h hp u, fun j=>?_, fun j=>?_, pays_rank B S h hp u, fun g=>?_ ⟩
 · unfold RBook; rw [Finset.sum_apply]; apply MS.Cylinder.Lab.Tune.sum; intro i _; refine ( TuneModel ( aura S i h hp ).phase ((j:ℤ)+ (F.grades i).2 ) ).cash _ (value_real ..)
 · unfold RBook; rw [Finset.sum_apply]; exact Colorless.csum _ fun i _=> Colorless.smul _ (ColorMod (aura S i h hp|>.lit) ((j:ℤ)+(F.grades i).2))
 let L:=actB (Spectrum G)+ blocks (Spectrum G) (core G); change L (∑ i:F.Index,valueP B S h hp u i • priceS S i)=0; rw [map_sum]; apply Finset.sum_eq_zero; intro i _; rw [map_smul,show L _=0 from (aura S i h hp).closed g,smul_zero]
def richBook (L:Frames G)(H:Hol G)(S:∀ d:ℕ,SectionData (L.level d))(h:∀ d:ℕ,(S d).Sound H)(hp:∀ d:ℕ,Bid.pop (S d)) : RichBook B where
 menu d _ i:= RBook B (S d) (h d) (hp d) i
 rich d _ i:= Shop.rich B (S d) (h d) (hp d) i

end YM.FVAAlt2.Shop
