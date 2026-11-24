import YM.RegulatorIR.Venture.Oasis

set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Venture
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Gradient Pupil Cluster Precision Oracle Oracle.Quarry Matrix Exterior Skein Momentum Warm Profiles Centered Clocks Stage
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
open Calibration
open Epoch VacDay
/-! Gain plus slack and damping on χ. Does not bind projections. -/
open Epoch.League
variable {X I:Type} {M:X→ℕ}{n:Page M→Side} {K:KernelChoices}(S:Circuit M n)(Y:Program K)(G:Gauge)(Z:∀ P:Patch,P.Branches K G)(s:Page M→Scale){B:Marked M}
variable {p e u r:ℕ} {γ θ:ℝ} {Q : Page M→ℝ≥0∞}
local notation "A₀"=> curtain S Y G
local notation "A₁"=> pathL S Y G
local notation "N₀"=> lnk S G
local notation "T₀"=> S.scroll_j Y G
local notation "K₀"=> valley S Y G Z s

variable (C:Scripted S Y G Z p u B γ) {T:Page M→Orders (Foot G)} {F:Page M→Packet (Foot G) (r+1)}
include C
-- caret paid on strict valuation ancestors. bound rollout separately
omit C in
lemma fundedS (T: Page M→Orders (Foot G))(e:ℕ)(h:∀ w,Ranks 2 (T w))(hx:∀ i<e,∀ j,0<j→j≤ i+2→VacDay Q B.age_t (N₀ u) fun w=>T w i j):∃ f:Page M→ℝ≥0∞,Carry B.age_t Q f ∧∀ i<e,∀ r,0<r → ∀ w,localQ (lnk S G u w) (T w i r) (f w):=by -- doesn't need C, Y Z
 let V:= (Finset.range e) ×ˢ Finset.range (e+3)
 let f(j:ℕ×ℕ)(w:Page M):= ⨆ i:Fin j.2, ⨆ x:Foot G, Stalk.scopeQ (fun u:Tuple (Foot G) j.2=>u i) (T w j.1 j.2) (lnk S G u w).diameter x
 have hp(j:ℕ×ℕ)(ht:j∈V): Carry B.age_t Q (f j):=by
    obtain ⟨he,hQ⟩:=Finset.mem_product.mp ht
    have hv:j.1<e:= Finset.mem_range.mp he; by_cases hk:0<j.2 ∧ j.2≤j.1+2
    · obtain ⟨c,hc,H⟩:=hx _ hv j.2 hk.1 hk.2;apply hc.mono; intro v; apply iSup_le;intro i; exact iSup_le (H v i)
    apply Carry.mono (Carry.zeroQ Q) -- remove b
    intro w; apply iSup_le; intro i;apply iSup_le;intro v
    have hT:T w j.1 j.2=0:= Classical.not_not.mp (fun he=> hk ⟨Nat.zero_lt_of_lt i.isLt,h w _ _ he⟩)
    rw [hT]; exact Packet.local_zero (c:=0) i v
 refine ⟨_,Carry.sum V f hp, fun i hi j hj w=>?_⟩
 by_cases hz:j≤ i+2
 · intro t z;apply le_trans _ (Finset.single_le_sum (s:=V) (f:=fun v=>f v w) (fun _ _=> zero_le) (show (i,j)∈V from mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr (by omega)⟩)); unfold f;apply le_iSup_of_le t; exact le_iSup _ z
 rw [show T w i j=0 from Classical.not_not.mp (fun hp=> hz (h w _ _ hp))];exact local_zero _
-- decide width.Z Script min helps older.
include s

lemma caretakerP (T:Page M→Orders (Foot G))(e r) (h:∀ w,Ranks 2 (T w))(hx:∀ i<e,∀ j,0<j→j≤ i+2→VacDay Q B.age_t (N₀ u) fun w=>T w i j) : VacDay (Q∘Flap.prev) B.age_f (fun i=>lnk S G u i.next) (fun i=>Gradient.correction (Gain.halo (A₀ i) (A₁ i)) (T i.prev) e r):=by
 obtain ⟨f,H,hV⟩:= fundedS S G T e h hx -- params
 let P(i: Flap M) :=fun j=>starM S Y G j u i
 refine ⟨_,Carry.mul_right (H.us Flap.prev) (taxes S Y G Z C e r),fun i=>?_⟩
 let K:=S.dialect Y G Z s;exact Skein.caretaker _ (Tariff.native _ (S.l_p i.next) u) (localL (S.l i.prev)) (localL (S.l i.next)) (P i) (fun p _=>living_v S Y G p _ (scope S Y G Z s _ _ rfl)) _ (fun g hg j hj=> Stage.enters S Y G Z s u (show localQ (K.census.cone u i.prev) _ _ from hV g hg j hj i.prev)) -- K typing scope
omit s C in
lemma loc_m (T:Page M→Orders (Foot G))(F: Page M→ ℝ≥0∞)(e:ℕ)(hx:∀ i<e,∀ r,0<r→∀ w,localQ (lnk S G u w) (T w i r) (F w))(hv:∀ i,gradedSymmetric (T i))(i:Page M): LowerQ (T i) e u (F i*(1+(e+2)*5:ℝ≥0∞)^u):=by -- cast error
 intro j hj r hr; cases r with
 | zero=> intro v; exact Fin.elim0 v
 | succ r =>
    apply keeps_r (hv _ _ _); intro x
    apply (bound_h (T i j (r+1)) u x).trans;apply le_trans (earnsP _ (S.l_p i) (hx j hj (r+1) (by omega) i));apply mul_le_mul_right
    apply pow_le_pow_left'; apply add_le_add_right; apply mul_le_mul_left; norm_cast;omega

-- Data for protected rank. use `parent focus F` $T$ like above.
omit s C
structure Vessel (T:Page M→Orders (Foot G))(r:ℕ)(F: Page M→Packet (Foot G) (r+1)) (e u:ℕ): Prop where
 branch i:W1 (T i) e
 sym i:gradedSymmetric (T i)
 grade i:Ranks 2 (T i)
 laps i:∀ j≤e,∀ r,Limits (T i j r)
 matter i:IsSym (F i)
 duty i:amount (F i) u≠⊤
 flat i: 1=r → MomentsP (F i) (5-(r+1)) 0
 lift i: 1≠r → T i e (r+1)=F i
 levy i: let D:=T (Flap.prev i) e (r+1)-F i.prev; Limits D∧ crest S Y G Z s i D
 successors w : Limits (F w)
variable (D:Vessel S Y G Z s T r F e u)
include s D
local notation "R₀"=>river S Y G
lemma charter_v (i:Flap M): K₀ i (F i.prev)=R₀ i (F i.prev)-Gradient.correction (Gain.halo (A₀ i) (A₁ i)) (T i.prev) e (r+1):=by
 let P:= T i.prev e (r+1); let ζ:=F i.prev;let d:= P-ζ
 obtain ⟨h,H⟩:= D.levy i;have hp:= V_house S Y G Z s (D.branch i.prev) (le_refl e) (D.laps i.prev) (D.sym i.prev) (D.grade i.prev) i (r+1)
 have he:= inherits S Y G Z s i (D.laps i.prev e le_rfl (r+1)) (D.successors i.prev); change K₀ i d= _ at he
 rw [show K₀ i d= _ from H] at he; rw [hp] at he; change R₀ i (P-ζ)= _ at he; rw [adopts S Y G Z s i (show Limits P from D.laps i.prev e le_rfl (r+1)) (show Limits ζ from D.successors _)] at he
 let g:=Gradient.correction (Gain.halo (A₀ i) (A₁ i)) (T i.prev) e (r+1); change R₀ i P-R₀ i ζ=R₀ i P-g-K₀ i ζ at he; change K₀ i ζ = R₀ i ζ-g; grind -- abelian
include C
lemma rive_v (hx:1 ≤ r)(h:r+1≤ e+2)(hp:e≤p)(hv:∀ i<e,∀ j,0<j→j≤ i+2→VacDay Q B.age_t (N₀ u) (fun w=>T w i j)) {Z':Flap M→Packet (Foot G) (r+1)} (hh:VacDay (Q ∘ Flap.prev) B.age_f (fun i=>N₀ u i.next) (fun i=> Z' i - K₀ i (F i.prev))) : ∃ f: Flap M→ℝ≥0∞,Carry B.age_f (Q∘ Flap.prev) f ∧ ∀ i, Epoch.amount (Z' i) u ≤ t_budget S Y G u r i * Epoch.amount (F i.prev) u+f i:=by
 obtain ⟨d,hd,H⟩:= fundedS S G T e D.grade hv
 have hC(i:Page M):= loc_m S G T d e H D.sym i -- s params
 let g(f:Flap M):= river S Y G f (F f.prev)
 have hΔ: VacDay (Q∘ Flap.prev) B.age_f (fun p=>N₀ u p.next) (fun f=> Z' f-g f):=by
    let c:= caretakerP S Y G Z s C T e (r+1) D.grade hv
    convert VacDay.sub hh c using 1;ext1 w;rw [charter_v S Y G Z s D]; unfold g; abel
 have ht:= Epoch.amount_profits (u:=u) (fun w:Flap M=> S.l_p w.next) hΔ
 let m(i:Page M):=d i*(1+(e+2)*5:ℝ≥0∞)^u; let c:=cork G 3 1 e (r+1); let b(j:Flap M):= sp_budget S Y G u r j*(c*m j.prev);let s' := 5-(r+1)
 have hm: Carry B.age_t Q m:= hd.mul_right (Poly.standard _ (by finiteness))
 have hf: Carry B.age_f (Q∘Flap.prev) b:= Carry.mul_left (poll_u S Y G Z C r) (Carry.mul_left (Poly.standard _ (show c≠⊤ from cork_f (by finiteness) (by finiteness))) (hm.us Flap.prev))
 refine ⟨_,hf.add ht,fun i=>?_⟩
 apply Epoch.amount_cap;intro x; let W:=F i.prev; let k:=Epoch.amount W u; let d:=sp_budget S Y G u r i
 have hs: MomentsP W s' (c*m i.prev):=by
    by_cases he:1=r
    · intro z P A H y; exact (D.flat i.prev he z P A H y).trans bot_le
    have hV : Held (T i.prev e (r+1)) u k:= (D.lift i.prev he) ▸ bound_h W u
    rw [← show T i.prev e (r+1)=W from D.lift _ he]; exact prism_h (D.branch i.prev) (hC _) hV (by have hz:=C.minimum;omega) (D.sym _ _ _) (le_refl _) h (D.duty _) (by omega)
 let p:= S.sizeL i;have ht':=C.funding
 have hv: Held (g i) u (t_budget S Y G u r i*k+b i):=by
    have hp:= Epoch.League.discount_p S Y G i s' u (le_trans (show s'≤3 from by unfold s';omega) (ht'.terms i)); let R:= fun _:Fin (r+1)=>A₀ i; have h:= Momentum.obtains_h (K:=R) (L:=p) (fun _=>hp) (bound_h W u) (show s'≤u from by have hc:= ht'.depth;unfold s';omega) hs (self_r G (P:=S.pactP i) _) 1 (by unfold s';omega) (pack_c_f G _ _ _) (D.duty i.prev)
    simpa only [pow_one] using! h
 specialize hv x; let k':=amount (Z' i-g i) u; change quota _ _ ≤ t_budget S Y G u r i *_ + (b _+_);
 have he : Z' i = g i+(Z' i-g i):=by abel
 rw [← add_assoc]; calc
    _ = quota (Momentum.anchored x (g i+ (Z' i-g i))) (wall (Momentum.area x) 1 u):= by rw [← he]
    _ ≤ _:= (quota_add (Momentum.anchored x (g i)) _ _).trans (add_le_add hv (bound_h (Z' i-g i) u x))
end YM.RegulatorIR.Venture
