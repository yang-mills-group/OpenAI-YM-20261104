import YM.OPE.Compatible.Copper.Jackpot
import YM.OPE.Compatible.Atlas.Commission
/-! Account centered coordinate move and tag overrides on the signed root marker support. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset Extraction Word Spec
open Allot Pixel
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {X I : Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){U F: Finset X}
    {G:Gauge}{C:Family G}{Λ:Extraction.Order}{S:Table C.book}(T:Final C Λ S){P:Prescription T.sector.derivatives}{u:X}
variable (p:X→ C.book.Token){v:F→ C.book.Token}
variable {W n b d e:ℕ}
set_option quotPrecheck false
local notation "V'"=> brim D U
local notation "H"=> brim D (Arboreal.trim U u)
local notation "V"=> glen D U u
variable {x:X→E4}(hx:angleClear D U x ∅)(h:Crown U)
lemma take_plan {U':Finset X}(h:U' ⊆ allUp D U)(y:X→E4)(hs:∀ i∈allUp D U,y i=x i):picked U' y=picked U' x:= funext fun i=> hs i.val (h i.2)
include hx
lemma onAny (S:Finset X)(hs:S⊆ U)(hS:Crown S): Screen (picked (brim D S) x):=by
   intro a b c hh; apply Subtype.ext; by_contra ht
   exact hx _ (brim_under D U S hs b.2) _ (brim_under D U S hs c.2) (brim_apart D S hS b.2 c.2 ht) (brim_apart D S hS c.2 b.2 (Ne.symm ht)) (fun i hi=> False.elim (Finset.notMem_empty _ hi)) a hh -- doesn't use h
local notation "ρ"=> C.S.gridPoint W
variable {y:X→ Cover}(hv:∀ i∈allUp D U,C.S.gridPoint W (y i)=x i)(hu:u∈U)
omit hx
include hv hu
lemma centeredAway : C.S.gridPoint W ∘ picked V (fun a=>y a-y u)= picked V (fun a=> x a-x u):=by
    funext i; change C.S.gridPoint _ (y i.val-y u)=_; rw [← Pixel.grid_diff,hv i.val (mem_union_right _ (mem_filter.mp i.2|>.1)),hv u (mem_union_left _ hu)]; rfl
include hx h
lemma shore_screen : Screen (C.S.gridPoint W ∘ picked V (fun a=>y a-y u)) :=by
    rw [centeredAway D hv hu]; intro i j k hz; have hS:= Trace.shutter_final D U h x hx
    have he:x j.val i-x u i=x k.val i-x u i := by change (x j.val-x u) i=(x k.val-x u) i at hz; exact hz
    have hV: (⟨j.val,(Finset.mem_filter.mp j.2).1⟩:brim D U)= ⟨k.val,(Finset.mem_filter.mp k.2).1⟩ := hS i (sub_left_inj.mp he); exact Subtype.ext (congr_arg (fun a:brim D U=>a.val) hV)
-- local reading at center. equality always. translate x v
omit hx h
lemma inCentered (a:Mode T.sector.derivatives): P.ope a (picked V x) (picked V p) (x u)=P.ope a (C.S.gridPoint W ∘ picked V (fun i=>y i-y u)) (picked V p) 0:=by
    rw [centeredAway D hv hu]; unfold Prescription.ope; refine Finset.sum_congr rfl (fun i h=>congr_arg _ ?_); unfold Prescription.reading; simp only [sub_zero]; rfl
omit hu hv
-- labels transported
omit [OrderBot X][PartialOrder X][Fintype X] in
lemma coverPaint (v:∀ i:F,C.label ((p i.val).1))(hp:∀ i:F,S.project _ (v i)=S.project _ (p i.val).2) : ∃ p':X→ C.book.Token, picked F p'=(fun i:F=>(⟨(p i.val).1,v i⟩:C.book.Token)) ∧ ∀ i∈F,S.classTokens (p' i)= S.classTokens (p i):=by
    let q i:= if h:i∈F then (⟨(p i).1,v ⟨_,h⟩⟩:C.book.Token) else p i
    refine ⟨q,funext fun i=> dif_pos i.2,fun i hi=>?_⟩; unfold q; rw [dif_pos hi]; change (⟨_,S.project _ (v ⟨i,hi⟩)⟩:S.Tag)=_; rw [hp]
-- collar fits all active
lemma allure {s:I→X→ℝ}{η M c:ℝ}{φ: Filter I}{T:I→ℝ}(hc:0<c)(H': Glowing D U φ T s η):∀ᶠ i in φ,∀ x:X→ E4, Ridge (s i) η M D U x→ ∀ a∈allUp D U, ‖x a‖ < c∧∀ b∈allUp D U, ‖x a-x b‖<c:=by
    have he := H'.crowned.base; have hz := (H'.fade ⊥ he).mono_right nhdsWithin_le_nhds; filter_upwards [(show Tendsto (fun i=>M*s i ⊥) φ (𝓝 0) from by simpa using (hz.const_mul M)).eventually (gt_mem_nhds (by positivity:0<c/2))] with i hi x hx a ha
    have hb(x':X)(hh:x'∈ allUp D U): ‖x x'‖ < c/2:=by
        have he:= hx.near _ _ he hh (bot_le); rw [hx.belly,zero_sub,norm_neg] at he; exact he.trans_lt hi
    refine ⟨(hb _ ha).trans (by linarith),fun x' hx=> ?_⟩; refine (norm_sub_le ..).trans_lt (lt_of_lt_of_le (add_lt_add (hb _ ha) (hb _ hx)) ?_); exact (add_halves c).le
end YM.OPE.Arboreal.Trace
