import YM.X.Bend.Rook
/-!
# σ measuring.Frame on T (before κ inversion). full FO positivity by prepared Ledger.Anchor all weights. guide formula.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Bend
open Lattice Wilson Next.Rank Normal LiftMark Crate Porch Rays Shelf Tot Fund
open Maxwell Maxwell.Free Extra.FD MvPolynomial Labels Pert.Position Pert.RawLabels
open Interval Size Filter Function MeasureTheory Set Reed Stems Haze Fielding PertExtension LatticePT Chir Sage Bare Tri Pulse
open scoped Topology BigOperators Classical
variable {G:Gauge}{F:Labels.Frames G} {d k m:ℕ} {q:ℕ+} {V I:Type*} {r R s:ℝ}
local notation "K"=>(atTop:Filter ℕ)
variable (B:Bare.Shop F) (hq:1<q.val)(hg:G.Simple)
local notation "D"=> Ribbon.firstX B q hq hg 6 -- namespace?
local notation "ξ"=> talent F (Nat.le_refl 6)
local notation "T"=>Fin 3
variable (χ:Floor R) (hr:R<r)
abbrev Aspect : Points 3 → ℂ:= presence B (Tri.xAway B q χ) hq hg (fun p=> robust B χ p hq) (light_res B χ hr hq) (talent F (Nat.le_refl 6))
local notation "M"=>Aspect B hq hg χ hr
variable {x:Points 3}
lemma cut_view (hx:x∈Pulse.Region 3 r)(v:(i:ℕ)→Grid.offsets q 3 i)(hv:clockP x v) : ∃ J:Ter, RootJ q (foamy v 1) (foamy v 2) (foamy v 0) J ∧ M x= ↑(4*Sage.count G* SpinLimit J (x 1) (x 2) (x 0)):= by
    let X:=foamy v; choose a ha using fun i=>hasOrigin q i; have e:=evident B (xAway B q χ) hq hg (fun p=> robust B χ p hq) (light_res B χ hr hq) a ha v hv ξ hx; have ht := cut_out B (xAway B q χ) hq hg (fun p=> robust B χ p hq) a ha v hv ξ; have hb(i:T): plot q (X i) (x i):= Grid.sample_each hq hv i; have hd(i j:T)(he:i≠j): Tot.Clear q r (X i) (X j):= ⟨_,_,hb i, hb j,hx i (by simp) j (by simp) he⟩;
    obtain ⟨b,c,d,hZ⟩:= Sage.faith hg; have h: Geom q r (X 0) (X 1) (X 2):= ⟨hd _ _ (by decide),hd _ _ (by decide),hd _ _ (by decide)⟩; obtain ⟨J,hJ⟩:= encounter (X 1) (X 2) (X 0) b χ (h.circles q ..) hq hr; refine ⟨J,hJ,?_⟩; have he := current (X 0) (X 1) (X 2) χ h hr hq B (Nat.le_refl 6) a; rw [furnish X] at he; unfold X at he; simp_rw [hose a] at he; let Z':ℝ:=4*Sage.count G; let z'(k:ℕ):ℂ:= probeX q B (xAway B q χ k) k (storefront q k (v k) (a k)) ξ
    have hu:Tendsto z' K (𝓝 (M x)):= by
        have hf:= e.sub ht; rw [sub_zero] at hf; exact hf.congr (fun i=> sub_sub_self ..)

    have hh(i:T)(hi:(0:T)≠i) : x i ≠ x 0:= Ne.symm (sub_ne_zero.mp (norm_pos_iff.mp (lt_trans (lt_trans χ.positive hr) (hx _ (by simp) _ (by simp) hi))))
    apply tendsto_nhds_unique (he.goes.mp hu) (?_)
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp ((spin_limit (X 1) (X 2) (X 0) hq (hh 1 (by decide)) (hh 2 (by decide)) (hb 1) (hb 2) (hb 0) J hJ).const_mul _)
def Avoid (q:ℕ+)(r0:ℝ):Prop:= ∀ x y z:E4, ∀ J:Ter, Crowd q x y z J → r0≤ ‖z‖ → SpinLimit J x y z<0
lemma limit_eye {s:ℝ}(hs:4096 ≤ s)(hx:Avoid q s)(w:Curve (mainT s hs) ⊆ Pulse.Region 3 r) (hX:x∈tsupport (mainT s hs)): star (M x)=M x ∧ (M x).re<0:= by
     let X(k):= Grid.signal q k x; have hg':= Grid.choose_sample hq x; obtain ⟨J,hJ,hP⟩:= cut_view B hq hg χ hr (w (Subcell.includes _ hX)) X hg'; obtain ⟨hy,hZ⟩:=farT s hs x hX; rw [hP]; refine ⟨by simp,mul_neg_of_pos_of_neg (mul_pos (by norm_num) (counted hg)) ?_⟩; exact hx _ _ _ J ⟨hy, ⟨_,_,_,sample_i hq X x hg' 1,sample_i hq X x hg' 2,sample_i hq X x hg' 0,hJ⟩⟩ hZ
-- prep
omit hq
lemma prepare_v (t:Test 3):∃ r:ℝ,r>0 ∧ Curve t⊆ Pulse.Region 3 r ∧ ready B hg r := by
    apply ((show ∀ᶠ r:ℝ in 𝓝[>] 0,r > 0 from self_mem_nhdsWithin).and ((Ribbon.region_time (region_compact t) (conf_curve _)).and (prepared_at B hg))).exists
variable (t:Test 3)(w:ready B hg r)(ht: Curve t⊆ Pulse.Region 3 r)
include w ht hq
lemma has_tip : (Ribbon.firstX B q hq hg 6) 3 t (talent F (Nat.le_refl 6))= t.applyTo M:= by
    have he := press_early B hq hg χ (deity F (Nat.le_refl 6)) (measureS F t) (lead_B ..) (lumen B hq t) w (show Curve t⊆ _ from ht) hr
    have hV(x:Bank F 6): Splot.result F (measureS F t) x (deity F (Nat.le_refl 6))= x 3 t ξ:= by
       change x 3 t (Function.update ξ 0 _)=_; have h:talent F (Nat.le_refl 6) 0=deity F (Nat.le_refl 6):= rfl; rw [←h,Function.update_eq_self]
    simp_rw [hV] at he; let hp := (inside B t (xAway B q χ) hq hg (fun p=> robust B χ p hq) (light_res B χ hr hq) ξ ht).2; exact tendsto_nhds_unique he hp
end YM.PositionX.Bend
