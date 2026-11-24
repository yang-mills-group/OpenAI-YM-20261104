import YM.GradedFar.GradientCore
/-!
# The antenna of the REAL packet

Local shape derivative through aperture; rotated tests explicit and contain original fields & contours.
Use only in (M.4). not changing outputs separately in M.2. Applies in orbitMargin neighborhoods.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Window
open Function Filter Set MeasureTheory Metric
open Extraction Table Spec OPE OPE.Orbits OPE.Nesting Orbits.Reader PhysMS
open Tariff
open scoped Topology BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S)(R: Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {n d: ℕ}
local notation "P"=> Reader.port R
local notation "Q"=> F.sector.derivatives
local notation "X"=> F.sector.turns
local notation "R*"=> (R)
abbrev target (d:ℕ)(o:E4)(r:ℝ)(x:Points n):= orbitMargin (P) d (sites o r x) o
local instance {n:ℕ} : ContinuousSMul ℝ (Points n) := IsBoundedSMul.continuousSMul
lemma physics_sites (o:E4)(r:ℝ) : ContDiff ℝ ∞ (sites (n:=n) o r):=by
    have h (i:Fin n) := (PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=>E4) i).contDiff (n:= (∞:WithTop ℕ∞)); exact contDiff_pi.mpr (fun i=> contDiff_const.add (show ContDiff ℝ ∞ (fun z:Points n=>r • z i) from (h i).const_smul _))
lemma target_open (o:E4)(r:ℝ)(d n:ℕ): IsOpen {x:Points n| target F R d o r x}:=(margin_open d («P»:=R.port)).preimage ((physics_sites o r).continuous.prodMk continuous_const)

lemma swung_margin {x : Fin n→ E4}{o:E4}{k:Ortho}{i:Mode (Q)}(h:orbitMargin (P) d x o)(e:Exterior C.book)
    (he:e∈((P).sheet i).support)(ht:i∈ bands (Q) d): Injective (beside x (swung e k o)):= by
 let y:=beside (away (Ortho.move k⁻¹ ∘ x) (Ortho.move k⁻¹ o)) (bearing e)
 have hx:beside x (swung e k o)= fun i=> (Ortho.move k ∘ y) i + o:= by
    funext i; rcases i with a|b
    · change x a=Ortho.motion k (Ortho.move k⁻¹ (x a)-Ortho.move k⁻¹ o)+o; rw [map_sub]; change x a= Ortho.move k (Ortho.move k⁻¹ (x a))-Ortho.move k (Ortho.move k⁻¹ o)+o; rw [Ortho.move_inv,Ortho.move_inv,sub_add_cancel]
    exact add_comm ..
 rw [hx]; exact fun i j e=> ((Ortho.move_injective k).comp (h _ ht k⁻¹ _ he)) (add_right_cancel e)
variable (d:ℕ)(o:E4)(r:ℝ)
-- common book arity, raw input physical labels. derive field-scale r after output in physical coordinates.
def elevate (v:Fin n→ S.Tag)(i:Fin n)(a:Axis):Fin n→S.Tag:= update v i ⟨(v i).1+1,F.sector.derivatives.deriv (v i).1 a (v i).2⟩
def illuminated (v:Fin n→S.Tag)(x:Points n)(k:Ortho) : S.Field d:= spinning (P) (X) d (sites o r x) o k (voices v)
private lemma spinUnit (k:Ortho): spinning (P) (X) d (sole o) o k (sole (0:S.Field d):Labels S (fun _:Unit=>d))=0:= by
 rw [scatter (P) (R*).continuum]; apply Finset.sum_eq_zero; intro i _; unfold bears; rw [show checkRow (P) i _ _ (roll (X) k⁻¹ (sole (0:S.Field d):Labels S (fun _:Unit=>d)))=0 from MultilinearMap.map_coord_zero _ (i:=()) (map_zero ((X).act _ _)), zero_smul]
local notation "Θ" => fun x v (e: Exterior C.book) (k:Ortho)=> whole S (sites o r x) (voices v) (swung e k o) (turnsPort (X) k e)
lemma spindle (k:Ortho)(v:Fin n→S.Tag){x:Points n}(hx:target F R d o r x): illuminated F R d o r v x k=
    ∑ i∈bands (Q) d,(∑ e∈((P).sheet i).support,(P).sheet i e * Θ x v e k) • (X).act d k ((P).loaded i d):= by
 obtain hv:= discrepancy_spin (P) R.law R.continuum F.phase.transport.motion (k:=k) (voices v) (0:S.Field d) hx; simp_rw [discrepancy,spinUnit F R,map_zero,sub_zero] at hv; exact hv
lemma spun (k:Ortho) (v:Fin n→ S.Tag)(x:Points n)(i:Fin n×Axis)(b:ℝ)(hx: target F R d o r (slopePath x (Points.direction i.1 i.2) b)) : HasDerivAt
    (fun s=> illuminated F R d o r v (slopePath x (Points.direction i.1 i.2) s) k)
    (r • illuminated F R d o r (elevate F v i.1 i.2) (slopePath x (Points.direction i.1 i.2) b) k) b:=by
 let K:=Points.direction i.1 i.2; let θ:= slopePath x K; let σ:= elevate F v i.1 i.2; let ξ (v) (s:ℝ)(i:Mode (Q))(e : Exterior C.book):=(P).sheet i e * (Θ (θ s) v e k)
 let L(v) (s:ℝ)(i:Mode (Q)) := ∑ e∈ ((P).sheet i).support, ξ v s i e; let X0(i):=(X).act d k ((P).loaded i d);
 have he:∀ᶠ s in 𝓝 b, target F R d o r (θ s):= (walking_cont x K).continuousAt.tendsto.eventually ((target_open F R o r d n).mem_nhds hx)
 have hi(v) u (ht:target F R d o r (θ u)): illuminated F R d o r v (θ u) k=∑ i∈bands (Q) d,L v u i • X0 i:= spindle F R d o r k v ht
 have hv(j)(hh:j ∈ bands (Q) d)(e:Exterior C.book)(hr:e∈ ((P).sheet j).support): HasDerivAt (fun s=> ξ v s j e) (r • ξ σ b j e) b:= by
    let e':=tags (turnsPort (X) k e); have hh':Injective (beside (sites o r (θ b)) (swung e k o)):= swung_margin F R hx _ hr hh; have hs:= smooth F none v e' o r _ hh'
    let F₀(s):= Θ (s:Points n) v e k; let f'(s:ℝ):= F₀ (θ s)
    have h':HasDerivAt f' (r • Θ (θ b) σ e k) b:= (slope_chain x K b hs).congr_deriv (at_slot F none v e' o r _ hh' i.1 i.2)
    refine (h'.const_mul ((P).sheet j e)).congr_deriv ?_; unfold ξ; simp_rw [Complex.real_smul]; ring
 rw [hi (elevate F v i.1 i.2) b hx, Finset.smul_sum]; apply HasDerivAt.congr_of_eventuallyEq _ (he.mono fun s hs=>hi v s hs)
 refine HasDerivAt.fun_sum (fun j hj=> ((HasDerivAt.fun_sum (fun e hr=> hv j hj e hr)).smul_const (X0 j)).congr_deriv ?_)
 rw [← Finset.smul_sum,smul_assoc]
end YM.Integration.GradedFar.Window
