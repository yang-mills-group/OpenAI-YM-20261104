import YM.OPE.Yarn.Dial
/-!
# Resource for the correcting array. Its sanctuary wallet is polynomial at
lens capture, so `score` can start at the child-parent bill even after
shrinks from other group surgeries. Need for genuine discrepancy gain (ratios
beyond clock-polynomial). Alternative branches can use ordinary estimates when
that gain is itself absorbed. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Yarn
open Function Filter Set MeasureTheory Finset Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Overlay
open MergeProof Accent Ribbons ManyCopies MergeProof.Float PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {I J:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n: Side} {C:Family G} {k j z l m p N d b:ℕ}
variable {W r D}{σ χ:ℕ→ℝ} (H:Tune C W r D σ χ)
set_option quotPrecheck false
local notation "P" => C.path
local notation "δ" => renal C.path.levels
local notation "η" => near C.path.levels
local notation "ζ" => fly C.path.levels
local notation "ψ" => waybill C.path.levels
local notation "R" => C.path.rep N p
local notation "h*" => C.path.levels.clock.hatBeta
local notation "V" => Site (C.side m p)
variable {F:I→ Config G (C.side N p)→ℂ}{o:I→ ∀ i:ℕ, Site (C.side i p)}{w:I→ℝ}{u:I→Pod}{v:J→Pod} {d₀:Finset I}{Y:I→∀ i:ℕ,Lamp G (C.side i p)}{X:I→Lamp G (C.side k p)}
variable {U:Coefficient (C.labels.level d) (C.side k p)} {x a:ℝ} {B:Album C N k p d}
    {hm:m≤k}{hn:k≤N}(hB:Chant W D (fly C.path.levels) (waybill C.path.levels) (near C.path.levels) U (ebb C d k x) B hn)
include H hB
local notation "q*"=> (Size.axis (C.labels.level d))
local notation "F₁"=> C.labels.level d
local notation "xo"=> fun i=>(0:Site (C.side i p))
variable (ht:C.ref d ≤ j)(hk:j≤k)(hz:C.ref 0 ≤ k)(hx:0<x)(hb:0 < b)
include ht hk hz hx hb
-- basis of correcting script
local notation "y*"=> submit C d b l j k x
local notation "x*"=> (8*ebb C d k x*(submit C d b l j k x))
def willing (C:Family G)(d k:ℕ) := fly C.path.levels d k*C.S.a k^d/4
lemma willingness (l:ℕ)(i:(F₁).Index) : willing C d k*bond P N p B.song k (-B.ear i) ≤ ζ d k:=by
    have hp:= fitted H ht hk hz hx hb l; let F':= (F₁); let E:= (B.song.tone k).index; have he:= (hB.window (submit C d b l j k x) j ht hk hp.1 hp.2.2|>.desks i).bias
    have hy : F'.coeffSize (E (-(B.ear i))) ≤ 4:=by
       rw [map_neg,show F'.coeffSize (-(E _))= _ from (by simp [Labels.Frame.coeffSize]: F'.coeffSize (-(E (B.ear i)))=F'.coeffSize (E (B.ear i)))]; rw [show E (B.ear i)= - (q* i - E (B.ear i)) + q* i from by abel]; apply le_trans (Size.add ..); rw [show F'.coeffSize (-(q* i-E (B.ear i))) = F'.coeffSize (q* i-E (B.ear i)) from by simp only [Labels.Frame.coeffSize,Pi.neg_apply,norm_neg]]; linarith only [he, (Size.size_axis (F₁) i)] -- F'
    have hh:= H.cuts.system.grows d k (ht.trans hk); have hs:= C.S.a_pos k; unfold willing bond; rw [alto_norm]; exact le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy (by positivity)) (by positivity)) (le_of_eq (by field_simp))
lemma activated (a:I) (i:(F₁).Index) (hr:CrewBook C N p m k D hm hn F ∅ o u w Y X) (ho:o a=xo)
    (hH: (X a).watch=soarF P (C.localSection d) N p B.song (-B.ear i) (1,false) xo k)(hL: (X a).rays (R k)= soarK P N p B.song (-B.ear i) (1,false) xo k)
    (hR:GridApprox.room C.path.levels m k (lensScope C d))
    (hh:stair η (8*ebb C d k x * (submit C d b l j k x)) j k ≤ pocket C (u a) k 1 (w a)) : ∃ S,CrewBook C N p m k D hm hn (Function.update F a (F a+GridApprox.backTo C.path N p hn (lens C N k p d (q* i)))) {a} o (Function.update u a (some j)) (Function.update w a x*) (Function.update Y a S) (Function.update X a (S k)) := by
    let z:= ebb C d k x; have hz':0<z:= ebb_pos d hx; have hp:= fitted H ht hk hz hx hb l
    obtain ⟨S,hS,h1,h2⟩:= score_aid H.seed H.cuts.system hn ht hk hp.1 hz' (hB.window _ j ht hk hp.1 hp.2.2) i; exact ⟨S,CrewBook.additive H a hr (mul_pos (mul_pos (by norm_num) hz') hp.1) (ho.symm ▸ hS) (hH.symm ▸ h1) (h2.trans hL.symm) hh (visible C N k p d _ H.seed hn) hR ⟩
omit hB ht hk hz hx hb
section
variable {B:Type}{T X x y:B→ℝ}{k j:B→ℕ}{a b:ℝ}{φ:Ultrafilter B}
-- Very tiny: faster than every polynomial of this clock.
def Whistle {φ : Filter B} (T x:B→ℝ) := ∀ {b:B→ℝ}, Coins φ T b → ∀ᶠ i in φ, ‖x i‖≤‖b i‖
omit H in
lemma speeds (hp:¬ Cheap φ T (fun i=>(x i)⁻¹)) : Whistle (φ:=φ) T x:=by
    intro b h; by_contra he; rw [← Ultrafilter.eventually_not] at he; apply hp; refine (Coins.inv h).up.norm_le ?_ ; obtain ⟨k,h⟩:=h.down; filter_upwards [he,h] with i hi hh
    have ht : b i≠0:=by intro h'; simp only [h',norm_zero,norm_one,zero_mul] at hh; linarith only [hh]
    rw [norm_inv,norm_inv]; exact inv_anti₀ (norm_pos_iff.mpr ht) (le_of_lt (lt_of_not_ge hi))
omit H in
lemma whittle {φ : Filter B}(ht:Tendsto T φ atTop)(hp:Whistle (φ:=φ) T x)(h:Bill φ T y x) : Whistle (φ:=φ) T y:=by
   intro b hb; obtain ⟨K,h⟩:=h; let A i:= ‖T i‖^K; -- need T≥1 add
   let P' := fun i=>(T i)^K; have hx:Coins φ T P':= Coins.power (Coins.by_le (Cheap.id ..) ((ht.eventually_ge_atTop 1).mono fun i hi=> hi.trans (Real.le_norm_self _))) ht _
   filter_upwards [hp (Coins.div hb hx),h,ht.eventually_gt_atTop 0] with i hα hi hk; refine hi.trans ((mul_le_mul_of_nonneg_right hα (pow_nonneg (norm_nonneg _) _)).trans_eq ?_); rw [norm_div]; unfold P'; have hz := hk.ne'; rw [norm_pow,div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr hz))]
-- bill marcher
lemma gaining (d : ℕ)(ht:Tendsto T φ atTop) (hj: Height C.S (φ:Filter B) T j a)(hk: Height C.S (φ:Filter B) T k b)
    (hp:Whistle (φ:=φ) T (fun i=> C.S.a (k i)/C.S.a (j i)))
    (hb : Bi (φ:Filter B) T X (fun i=>C.S.a (k i)^d))(he:Bill (φ:Filter B) T x (fun i=>C.S.a (j i)^d)) (hX:∀ᶠ i in (φ:Filter B),0<x i ∧ 0<X i∧ C.ref d≤j i ∧ j i≤k i) : ∀ᶠ i in (φ:Filter B), stair (near C.path.levels) (x i) (j i) (k i) ≤ X i:=by
    let u:= C.S.a; let a i:=u (k i); let b i:= u (j i); let φ' := (φ:Filter B)
    obtain ⟨K,hE⟩:= he; have hZ:Coins φ' T (fun i=>(T i)^K):= Coins.power (Coins.by_le (Cheap.id ..) ((ht.eventually_ge_atTop 1).mono fun i hi=> hi.trans (Real.le_norm_self _))) ht _
    let v i:= (a i)^d/X i; have hv:Coins φ' T v:=by
       have hh:= Bi.div (Bi.refl φ' T (fun i=>(a i)^d)) hb (Eventually.of_forall fun i=> (pow_pos (C.S.a_pos _) _).ne'); simpa only [v,a,u, div_self (pow_pos (C.S.a_pos _) d |>.ne')] using hh
    have ha:= hp (Coins.inv (Coins.mul (Coins.mul hZ hv) (Coins.div (fly_coins ht hk d) (fly_coins ht hj d))))
    filter_upwards [hX,hE,ha,ht.eventually_gt_atTop 0] with i ⟨hi,hh,hq,heq⟩ hE hK hi'
    apply le_trans (seeing C d H.cuts.system hi (k i) (j i) hq heq); have h1:= H.cuts.system.grows d (j i) hq; have h2:= H.cuts.system.grows d (k i) (hq.trans heq); have hr:b i>0:= C.S.a_pos _; have hs:a i>0:= C.S.a_pos _; let g:=ζ d (k i)/ζ d (j i); have hz:0<g:= div_pos h2 h1
    unfold v at hK; let D:=T i^K; have hh₀:0 < D:=pow_pos hi' _; change ‖a i/b i‖ ≤ ‖(D*((a i)^d/X i)*g)⁻¹‖ at hK; rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)] at hK
    change ‖x i‖ ≤ ‖(b i)^d‖*_ at hE; rw [Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity),Real.norm_of_nonneg (by positivity)] at hE
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (pow_nonneg (show 0 ≤ a i / b i from by positivity) _)) hz.le).trans; change b i^d*D*( (a i/b i)^(d+1))*g ≤ _; generalize hD:a i/b i=c; rw [pow_succ, ← hD,div_pow]; -- calc
    calc _ = c*(D*a i^d*g):=by rw [← hD]; field_simp
         _ ≤ _ := (mul_le_mul_of_nonneg_right (hD ▸ hK) (by positivity : 0 ≤ D*a i^d*g)).trans_eq (by rw [inv_eq_one_div]; field_simp)

end
end YM.OPE.Yarn

