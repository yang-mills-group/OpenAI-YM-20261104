import YM.RegulatorIR.Atlas.Shelves

/-!
# Roll out length-caps to coverage engines

`OfAge` lives on Page not Flap. Requires polynomial epoch charges but can
be paid from log epsilon & log P and Z allocations. Only terminal inverse
is budgeted at the specified side (bounded). No costs hidden in periodic
translations or in heat iterations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Atlas
open Function Filter Finset Budget Uniform
open Lattice RG Gauge Prim Binding Epoch Epoch.League Geometry Step Taping Precision Oracle Venture Laurent Bloch Halo Profiles Calibration Momentum
open YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky
open scoped ENNReal NNReal Topology BigOperators Classical
variable {X:Type}{M: X→ℕ}{n:Page M→ Side}{W:Meter X}{D:Choice M}
variable {K:KernelChoices}(S:Circuit M n)(G:Gauge)(R:Program K)(Z:∀ P:Patch,P.Branches K G)
variable {B:Marked M}

def OfAge (B:Marked M)(W:Meter X) := Poly (coverL M W) B.age_t.val
variable (hb:∀ w,B.peak (D.choose w)=0) (H: OfAge B W)
include H
lemma darkA {f:Page M→ℝ≥0∞} (h:Poly B.age_t f): Poly (coverL M W) f:= renewed h H
lemma darkF {f:Flap M→ℝ≥0∞} (h:Poly B.age_f f): Poly (flapL M W) f:= renewed h (H.us Flap.prev)
include hb
lemma covered_u : Poly W (fun w=>↑(M w)):=by
 have hv:= B.ruff_size D hb; have he: Poly (coverL M W) (Marked.ruff D):= darkA H hv
 convert (he.us (Page.opening M)).add (he.us (Page.finallyW M)) using 1; try rfl
 ext1 x; rw [Marked.ruff_b D (Page.opening M x) (show D.age x≥0 from Nat.zero_le _),Marked.ruff_c D (Page.finallyW M x) (show D.age x≤M x from D.young x)]
 change (↑(M x):ℝ≥0∞)= ↑(D.age x-0)+↑(M x-D.age x); rw [Nat.sub_zero,←Nat.cast_add,Nat.add_sub_of_le (D.young x)] -- test lemma

variable {γ:ℝ} {p u:ℕ} (k:SatisfiesQ G R S Z B p u γ)
variable {s: Tent M} (c:G.ColorIndex)(hG:G.Simple)
include k
lemma growing (hs:Notebook S R G Z c D s p)(hG:G.Simple): S.Credit R G Z (sheet s) W u p :=by
 have ht:= scripts_v G R S Z k
 obtain ⟨_,hQ⟩:= dome S R G Z ht k.θ_pos c hG _ D hb hs
 refine ⟨covered_u hb H,R.min_one G u _ _ _ S (hPre G R S Z k),darkF H ht.tariff_v,darkF H ht.bands.down,darkF H ht.bands.rays,fun i hi=>darkF H (Poly.us (hQ i hi) Flap.prev),fun i j hp h=>darkF H (wall_pay G R S Z k i j hp h)⟩
lemma wardrobe (hs:Notebook S R G Z c D s p)(hG:G.Simple): Circuit.Vacancy S R G Z (sheet s) W p u:=by
 intro i hi j;obtain ⟨f,hf,F⟩:= (dome S R G Z (scripts_v G R S Z k) k.θ_pos c hG _ D hb hs).1 i hi j; exact ⟨_,darkA H hf,F⟩
lemma reservations (hs:Notebook S R G Z c D s p)(hG:G.Simple)(hx:∀ w,S.l (D.choose w)=1): SchemeBeam (S.lane R G Z (sheet s)) (S.payroll R G Z (sheet s)) (S.pushP R G) (S.takeP R G) W (S.leadA R G u) p u ∧ Lantern (S.dialect R G Z (sheet s)) D W (S.leadA R G u) γ:=by
 refine ⟨S.habits R G Z (sheet s) W (growing S G R Z hb H k c hs hG) (wardrobe S G R Z hb H k c hs hG), S.happens R G Z (sheet s) W D hx k.θ_pos k.θ_low.le ?_ (leadS G R S Z k)⟩
 apply darkF H; have hp:= k.capital.fromF; convert hp using 1; ext1 i; rw [Marked.day,k.shapeS]
omit hb
lemma closures (c:ℕ)(hc:∀ w,(n (Page.finallyW M w)).val≤c)(s:Tent M): Reel.Endings (S.lane R G Z (sheet s)) W := S.enduras R G Z _ W c hc (let h : Poly B.age_t (fun i=>ENNReal.ofReal (R.receipt.η (S.J i))⁻¹) := k.accountP.mono (fun _=> le_add_self); (darkA H h).us (Page.finallyW M))
omit H k
-- Proof from log allocation. `l` and age normalized equal; reference at 1.
structure Ports (S:Circuit M n)(D:Choice M)(B:Marked M)(W: Meter X):Prop where
 rail i:B.l i=S.l i
 photo i:S.l (D.choose i)=1
 fundZ : Poly W fun i=> ENNReal.ofReal (1+B.Z i)
 fundV : Poly W fun w=> ENNReal.ofReal (Real.log (S.P w))
 fundU : Poly W fun w=> ENNReal.ofReal (-Real.log (S.l (Page.opening M w)))
variable (T:Ports S D B W)
include T
lemma port_ref w:B.peak (D.choose w)=0:=by rw [Marked.peak,T.rail,T.photo,Real.log_one]
include Z R G
lemma co_age (s:Tent M) : OfAge B W:=by -- remove s?
 apply Poly.mono (Poly.us ((T.fundZ.add T.fundV).add T.fundU) Page.bindW)
 intro i; let w:=i.bindW; let x:= Page.opening M w
 have hv : B.peak i=Real.log (S.l i):=by rw [Marked.peak,T.rail]
 have hc: S.l x ≤ S.l i:= (S.dialect R G Z (sheet s)|>.heads i)
 have hx:S.l i ≤ S.P w:= le_trans (le_mul_of_one_le_right (S.l_p _|>.le) (by exact_mod_cast (n i).property : (1:ℝ)≤(n i).val)) (S.comet i).le
 change ENNReal.ofReal _ ≤ _+_
 cases le_or_gt (B.peak i) 0 with
 | inl h=>
    unfold Marked.credit; rw [abs_of_nonpos h]; refine le_trans (ENNReal.ofReal_add_le ..) ?_; apply add_le_add (le_self_add) (ENNReal.ofReal_le_ofReal ?_);rw [hv]; exact neg_le_neg (Real.log_le_log (S.l_p _) hc)
 | inr h=>
    unfold Marked.credit; rw [abs_of_pos h]; exact (ENNReal.ofReal_add_le ..).trans ((add_le_add_right (ENNReal.ofReal_le_ofReal (hv.trans_le (Real.log_le_log (S.l_p _) hx))) (ENNReal.ofReal (1+B.Z i.bindW))).trans le_self_add)
end YM.RegulatorIR.Atlas
