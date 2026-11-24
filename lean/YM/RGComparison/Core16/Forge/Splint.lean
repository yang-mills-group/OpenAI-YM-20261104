import YM.RGComparison.Core16.Forge.Brook
/-!
# Sturdy pin in Wilson case. All graded postblock multiplier costs: no size dependency.
All orders of entropic tails at this stage. Takes `Q g` global link bound at coarse V;
inductive generalization from flat, work in a fixed real-sector slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Forge.Hut
open Filter Function Finset Lattice RG Tree Wilson MeasureTheory Pressure
open Precision Push.BetaTransport Push.GridApprox Further.RootedInteractingRemainder.Vault Work.E02
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge} {c f : Side}{S:StepData c f} (T:Forest S.ratio) (t : S.Choices) {g Q:ℝ} (hS:Bid.Larger (G:=G) S)
    {V:Config G c}(hg:0≤g)(hQ:0<Q)(hv: ∀ i,G.chord (V i)≤Q*g)
local notation "B"=> seam S T V
local notation "R"=> width S.patch

def lowClip (G:Gauge)(P : Patch)(K:KernelChoices)(Q:ℝ):ℝ:= (Descent.edgeUnit G K P * Real.sqrt 2 + Descent.noiseUnit K + Q)^2

def upstairs (P:Patch)(K: KernelChoices)(Q:ℝ): ℝ:= 16+ K.penalty*(Q+4*farePrice P K)^2
lemma up_pos (P:Patch)(K:KernelChoices)(Q:ℝ):0<upstairs P K Q:=by unfold upstairs; have h:=K.penalty_pos; positivity

variable (x:Sky G T.Free)

private lemma footing {o : Site f} (j:Rooms c f) (p:ℕ)(h:separation o (root S j)≤p) : (B).cost t x j ≤ g^2 + ∑ i∈neighborsOf (root S) p o,(B).cost t x i :=
    (single_le_sum (f:=(B).cost t x) (fun i _=> cooks S T V x t i) ((member ..).2 h)).trans (le_add_of_nonneg_left (sq_nonneg g))
include hS hg hv hQ
lemma lower (i : T.Free)(ht : 0< S.likelihood (T.drape x) t) : nib x i ≤ lowClip G S.patch S.kernel Q * (g^2 + ∑ j∈neighborsOf (root S) R (pad T i),(B).cost t x j):= by
    let U:= T.drape x; let j := pad T i; let d:= S.ratio.parent j; let W:= i.val; let l:=Real.sqrt (2:ℝ); let A:= g^2 + ∑ j'∈neighborsOf (root S) R j,(B).cost t x j'; let a:=Real.sqrt A
    have hA : g^2 ≤ A:= le_add_of_nonneg_right (sum_nonneg fun i _=> cooks ..); have hu:0≤A:=(sq_nonneg _).trans hA; have ha:0≤a:=Real.sqrt_nonneg _; have had:a^2=A:=Real.sq_sqrt hu; have hl: 0≤l:=Real.sqrt_nonneg _; have hl₁:l^2=2:=Real.sq_sqrt (by norm_num)
    have hb : 2*separation j (hold S d)≤ S.patch.L.val := Lattice.Corona.near S.ratio j; let p:=port S d U
    have hr : p ≤ Descent.macroCount S.patch*(l*a):=by
       apply (Work.F01.port_le S U d).trans; refine (sum_le_sum (g:=fun _=> ∑ _:PlaqAxes,l*a) (fun x' hx=> sum_le_sum fun j' _=> ?_)).trans_eq ?_
       · let v: Face (Per f):= (wrap f x'+hold S d,j'); apply (sq_le_sq₀ (G.chord_nonneg _) (mul_nonneg hl ha)).mp; rw [mul_pow,hl₁,had]; change G.chord (faceValue U v)^2 ≤ _; rw [G.chord_price]; apply mul_le_mul_of_nonneg_left (footing T t (V:=V) (g:=g) x (.inl v) R ?_) (show (0:ℝ)≤2 by norm_num)
         apply (separation_triangle _ (hold S d) v.1).trans
         have hh : separation (hold S d) v.1≤ macroR S.patch := box_sep (show v.1∈window (hold S d) (macroR S.patch) from ⟨_,hx,rfl⟩); unfold width; omega
       simp [Descent.macroCount,mul_assoc]
    let N:= Descent.noiseUnit S.kernel; let f': Bond c:=(d,W.2); let v:=wire (S.prediction U t) V f'
    have hN:= show 0<N from Real.sqrt_pos.mpr (div_pos (by norm_num) S.kernel.penalty_pos)
    have hK:= S.kernel.penalty_pos
    have hx':v ≤ N*a:=by
        let k:= S.kernel.penalty; have hi : (B).cost t x (.inr f') ≤ A:=footing T t x (.inr f') R (show separation j (hold S d) ≤ R by unfold width; omega)
        let Y:= V f' * (S.prediction U t f')⁻¹; change k* G.price Y ≤ _ at hi
        apply (sq_le_sq₀ (G.chord_nonneg _) (mul_nonneg hN.le ha)).mp
        change G.chord Y ^2 ≤ _; rw [G.chord_price,mul_pow,had,show N^2=2/k from Real.sq_sqrt (div_nonneg (by norm_num) hK.le)]
        rw [div_mul_eq_mul_div,le_div_iff₀ hK]; nlinarith only [hi]
    have hw:= (answer G S.patch.L S.patch.J S.kernel); let C:=hw.choose; have hc:0≤C:= hw.choose_spec.1.le
    have hR : G.chord (U W*(replica S.ratio V W)⁻¹) ≤ C*p+ v :=by
        apply (hw.choose_spec.2 c f S rfl rfl rfl hS.2.1 hS.2.2 T U (fun i hi=> T.on_tree _ ⟨i,hi⟩) V W t (wraps S t ht _)).trans
        apply add_le_add (show _ ≤ C*p from le_refl _) _; split; exact G.chord_nonneg _; rfl
    have hΔ: G.chord (replica S.ratio V W) ≤ Q*a:= by
        unfold replica; split
        · rw [G.chord_one]; positivity
        exact (hv _).trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hg ha).mp (had ▸ hA)) hQ.le)
    unfold nib; rw [show x i=U W from (T.off_tree ..).symm]
    let u:= Descent.edgeUnit G S.kernel S.patch
    let w:=(u*l+N+Q)
    have hz : G.chord (U W) ≤ w*a:=by
        refine le_trans (b:=G.chord (U W * (replica S.ratio V W)⁻¹)+ G.chord (replica S.ratio V W)) ?_ ((add_le_add (hR.trans (add_le_add (mul_le_mul_of_nonneg_left hr hc) hx')) hΔ).trans (?_))
        · simpa only [inv_mul_cancel_right] using G.chord_triangle (U W*(replica S.ratio V W)⁻¹) (replica S.ratio V W)
        unfold w u Descent.edgeUnit; change C * _ + _ + _ ≤ _; apply le_of_eq; ring
    apply (pow_le_pow_left₀ (G.chord_nonneg _) hz 2).trans_eq; rw [mul_pow,had]; rfl

omit hS hv hg hQ
private lemma ensconsed {i:Site f}(Y:ℕ) : ∃ y:Sky G T.Free,(∀ q∈neighborsOf (pad T) Y i,x q=y q) ∧ T.drape y∈ RG.calm G f (4*Real.sqrt (g^2+threat (pad T) i x Y)) := by
   let t:= neighborsOf (pad T) Y i; let y (j:T.Free) := if j∈t then x j else 1; let w:= g^2 + threat (pad T) i x Y; let b:= Real.sqrt w
   have hw: 0≤w:=add_nonneg (sq_nonneg _) (threat_nonneg ..); have hb:b^2=w:=Real.sq_sqrt hw; have hz:0≤b:=Real.sqrt_nonneg _
   refine ⟨y,fun j h=> (if_pos (show j∈t from h)).symm,fun i _=> ?_⟩; change G.chord (T.drape y i) ≤ (4*b)/4; rw [show (4*b)/4=b from by ring]; by_cases h:i∈T.trunks
   · rw [T.on_tree y ⟨i,h⟩,G.chord_one]; exact hz
   let j:T.Free:=⟨i,h⟩; change G.chord (T.drape y j.val) ≤ _; rw [T.off_tree]; by_cases hh:j∈t
   · rw [show y j=_ from if_pos (show j∈t from hh)]; apply (sq_le_sq₀ (G.chord_nonneg _) hz).mp; rw [hb]; exact (single_le_sum (f:=nib x) (fun i _=> Base.nib_nonneg x i) hh).trans (le_add_of_nonneg_left (sq_nonneg _))
   rw [show y j=_ from if_neg (show j∉t from hh), G.chord_one]; exact hz
include hS hg hv hQ
lemma upper (j : Rooms c f): (B).cost t x j ≤ upstairs S.patch S.kernel Q * (g^2+threat (pad T) (root S j) x R):=by
    let A:= g^2+threat (pad T) (root S j) x R; let a:=Real.sqrt A; have ha : g^2 ≤ A:= le_add_of_nonneg_right (threat_nonneg ..); have hw:0≤a:=Real.sqrt_nonneg _; have hu:0≤A:=(sq_nonneg _).trans ha; have hb:a^2=A:=Real.sq_sqrt hu
    obtain ⟨y,hx,hy⟩:= ensconsed T (g:=g) x (i:=root S j) R; let U:=T.drape y
    let k:= S.kernel.penalty; have hv₁:0<k:=S.kernel.penalty_pos; let u:=farePrice S.patch S.kernel
    let z:=Q+4*u
    have hU: upstairs S.patch S.kernel Q = 16+ k*z^2:=rfl
    rcases j with j|j
    · let Y := faceValue U j; change G.price _ ≤ _ * A; rw [stele (b:=j) hx]; apply (mul_le_mul_of_nonneg_right (show (16:ℝ) ≤ upstairs S.patch S.kernel Q from ?_) hu) |>.trans' (show G.price Y≤16*A from ?_)
      · rw [hU]; nlinarith only [mul_nonneg hv₁.le (sq_nonneg z)]
      have he : G.chord Y ≤ 4*a:= faceBound hy j; nlinarith only [sq_nonneg a, hb, pow_le_pow_left₀ (G.chord_nonneg Y) he 2, G.chord_price Y]
    · have h1 : S.prediction (T.drape x) t j=S.prediction U t j:= congrArg (fun b=> S.patch.predict S.kernel b (t.2 j)) (stitch hS.1 (t:=t.1) (s:=t.1) rfl rfl hx)
      let u':=S.prediction U t j; let Y:=V j*u'⁻¹; change k*G.price (V j*(S.prediction (T.drape x) t j)⁻¹) ≤ _*A; rw [h1]
      have hh:G.chord (V j) ≤ Q*a:= (hv _).trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hg hw).mp (hb ▸ ha)) hQ.le)
      have ht : G.chord Y ≤ z*a:=by
         unfold Y; refine (G.chord_triangle _ _).trans ?_; rw [G.chord_inv]; have h : G.chord u' ≤ u * (4*a) := prediction_good S U t (4*a) (by positivity) hy j
         refine (add_le_add hh h).trans_eq ?_; ring
      have hp:G.price Y ≤ z^2*A:=by nlinarith only [pow_le_pow_left₀ (G.chord_nonneg Y) ht 2,G.chord_price Y,hb, mul_nonneg (sq_nonneg z) hu]
      apply (mul_le_mul_of_nonneg_left hp hv₁.le).trans; rw [hU,add_mul,← mul_assoc]; nlinarith only [hu]
end YM.RGComparison.Core16.Forge.Hut
