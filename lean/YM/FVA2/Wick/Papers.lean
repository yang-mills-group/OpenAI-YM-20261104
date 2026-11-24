import YM.FVA2.Wick.RankJet
import YM.FormalOPE.RG10.MultiGauge.Engine
/-!
# Encoding the body polynomials in the Taylor algebra

An immediate bridge to and from RG10's `Permit`, no `g`-dependent finite-order lift choices. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Wick.Boson
open Function Set Finset Filter MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit MS.Orbit.Cog MS.Swirl MS.Book Convolve MS.Cylinder Taylor
open FormalOPE.RG10.MultiGauge
open Formal (overlay)
open PertExtension.Series.Radial
open scoped BigOperators Topology ContDiff Matrix
variable {E A B J : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
namespace Poly
local notation "T" => Permit E
variable {x : E→ℝ}
lemma smooth (c:T) : ContDiff ℝ ω c.val :=
  Papers.induction (P:=fun c:E→ℝ=> ContDiff ℝ ω c) (fun l=>l.toContinuousLinearMap.contDiff)
    (fun _=>contDiff_const) (fun _ _ _ _ h g=> h.add g) (fun _ _ _ _ h g=>h.mul g) c.property

variable (e : A→E) [Fintype A]
local notation "Λ" => Raw (Index A J) ℂ
local notation "p" => sector (A:=A) (J:=J)
local infixl:70 " ≫ " => product p

/-- All leg ranks in this symbol, no factorials, no ghosts. -/
def encode (e:A→E) : Permit E→ₗ[ℝ] Λ where
  toFun x:=Inks e x.val
  map_add' x y:= ink_add _ (smooth x|>.contDiffAt) (smooth y|>.contDiffAt)
  map_smul' c x := ink_smul _ (smooth x|>.contDiffAt) c

local notation "σ" => encode (J:=J) e
section
omit [Fintype A]
lemma encode_product (x y : T) : σ (x*y)= σ x ≫ σ y:= ink_mul _ (eased_p e) (smooth x|>.contDiffAt) (smooth y|>.contDiffAt)
lemma encode_cost (x:ℝ): σ (algebraMap ℝ T x)=coin (x:ℂ):= ink_const ..
lemma encode_unit : σ 1 = coin 1:= by rw [← map_one (algebraMap ℝ T), encode_cost, Complex.ofReal_one] -- potential rewrites
lemma encode_alone (x:T) : σ x∈ Alone p := alone_Inks _ _
lemma encode_sym (x:T) : Symm p (σ x):= ink_s _ (eased_p _) (smooth x|>.contDiffAt)
omit e in
lemma ink_linear {a:A→E}(l:Module.Dual ℝ E)(i:A) : D i (ink a l)=coin ((l (a i):ℝ):ℂ):= by
  let L:=l.toContinuousLinearMap; rw [inktip a i];
  have h : layer (a i) l= fun _ : E=> l (a i):= funext fun x => by change fderiv ℝ L x (a i) = _; rw [L.fderiv]; rfl
  rw [h, ink_const]
lemma length (x:T) : σ x∈ Mini (Index A J) := by
  change Inks _ x.val∈ _
  refine Papers.induction (P:=fun x:E→ℝ=> Inks e x∈ Mini (Index A J)) (fun l=>?_) (fun x=> ?_) (fun x y hx hy hX hY=>?_) (fun x y hx hy hX hY=>?_) x.property
  · apply minH («v»:=1)
    intro w hw
    cases w with
    | nil=> simp at hw
    | cons i w=>
      cases w with
      | nil=> simp at hw
      | cons j w=> rw [Inks, D_eval i (ink _ _), ink_linear]; rfl
  · unfold Inks; rw [ink_const]; exact minH (coinN _)
  · let i : T:= ⟨x,hx⟩; let j:T:= ⟨y,hy⟩; change σ (i+j)∈ _; rw [map_add]; exact (Mini _).add_mem hX hY
  · let i : T:= ⟨x,hx⟩; let j:T:= ⟨y,hy⟩; change σ (i*j)∈ _; rw [encode_product]; exact miPair hX hY
lemma fee (x:T) : σ x∈ FeeP p:= ⟨encode_sym e x,length e x⟩
end
end Poly
end YM.FVA2.Wick.Boson
