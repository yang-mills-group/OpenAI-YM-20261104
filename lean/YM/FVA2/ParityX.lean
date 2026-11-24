import YM.FVA2.BetaWay
/-!
# X curvature factor sign. Transferring the calibration detector through dilation preserves this parity, though bare W and v clocks were *arbitrary*. A useful consequence about β. The ν quantity of beta coefficient numerical remains outside these lemmas.
-/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.FVA2.Forge.Parity
open Function Filter Set Finset MeasureTheory Pert Pert.Position Lattice Maxwell Maxwell.Free Pert.RawLabels PositionX PositionX.Jet PositionX.Ribbon PositionX.Detector PositionX.Bend Elegant PayAll Verne Panel Strat ColorCode Ember Legacy Taper
open MS MS.Plane MS.Land MS.Landau MS.Rake MS.High MS.Menus MS.Theater MS.Logarithm MS.Tide MS.Book MS.Book.Program MS.Book.Convolve Clock
open Hop Month
open scoped Topology ContDiff Classical
variable {G:Gauge} {F:Labels.Frames G} {r k j m d:ℕ} (A:Panel F)
abbrev negView (u:Bank F d) := pulls (par F d) u
-- sign relation turn⇔points
abbrev elliptic (u: Word (Bank F d)): Prop:= negView ∘ u=turn u
def tone (A:Panel F): Prop:= ∀ d, elliptic (A.lives d)
abbrev segment (t:ℕ) : ℝ:=(-1:ℝ)^t
lemma twist (i:ℕ)(K: Points m→ℂ)(v:Test m) : v.applyTo (fun t=> segment i • K t)=segment i • v.applyTo K:= by
    unfold Test.applyTo; simp_rw [ Complex.real_smul, mul_left_comm (v _), integral_const_mul ]
lemma song (h:A.clearP): elliptic (A.lives d)↔∀i m (x:Polyp m)(v:Fin m→ E F d),A.out d x i (par F d∘v)=segment i • A.out d x i v:= by
    constructor
    · intro hp i m x v; let Y(p:Fin m→ E F d) := fun x:Points m=> taste ( A.off d x ) p i; let L(t):= segment i • Y v t; have hx : EqOn (Y (par F d∘v)) L (conf m):= by
          apply ( Test.unique_kernel ( h d m i (par F d∘v) ) ( show ContinuousOn L (conf m) from ContinuousOn.smul (continuousOn_const (c:=segment i)) (h d m i v ) ) ).1;
          intro t; rw [ show t.applyTo L= _ from twist i _ t ]; change t.applyTo (fun x=> A.off d x i (par F d∘v))= _ • t.applyTo (fun x=> A.off d x i v); rw [← Panel.newly A t (par F d∘v) i h, ← Panel.newly A t v i h]; exact DFunLike.congr_fun (congr_fun (congr_fun (congr_fun hp i) m) t ) v;
      have ht:A.off d x.val i (par F d∘v)=segment i • A.off d x.val i v:= hx x.property; rwa [ Panel.sees A x.property ] at ht
    intro H; funext i m t; ext1 v; change A.lives d i m t ( par F d∘v )= segment i • A.lives d i m t v; rw [ Panel.newly A t _ _ h, Panel.newly A t _ _ h, ← twist ]; apply Test.apply_eq; intro x hx; simp_rw [Panel.sees _ hx ]; exact H _ _ ⟨x,hx⟩ _ -- rw λ body issue
lemma sign_Δ (s:ℝ)(p:E F d): Δ F s d ( par F d p )= par F d (Δ F s d p):= by unfold Δ par eng; rw [scalePol_mul, scalePol_mul, mul_comm ];
lemma tune (s:ℝ)(h:A.clearP)(hp:tone A): tone ( A.swell s ):= by
   intro d; refine (song _ (paid_scl A _ h)).2 ?_; intro i m x v; rw [ Panel.unfold_scl,Panel.unfold_scl ]; obtain hh:= (song A h).1 (hp d) i m ( shiftP s x ) (Δ F s d∘v); rw [ show Δ F s d ∘ ( par F d ∘ v )= par F d ∘ (Δ F s d ∘ v) from funext fun k=>sign_Δ s (v k),hh ]
lemma swop {I:Type*}[AddCommMonoid I][Module ℝ I] (w:Word I): turn (turn w)=w:= funext fun i=>by unfold Jet.turn; rw [smul_smul,← mul_pow]; simp
lemma meter {u:Word (Bank F d)}(D:Detector F d)(hu:u 0=pureBank F d)(he:elliptic u): elliptic ( predMarket ( D.report u ) u ):= by
   let T:=D.report u; let V:=pureBank F d; let Z:= cPar F ( d:=d ); let U:=pulls (par F d); have ht:= Elegant.solves_only D u hu; have hp := ht.2.1;
   let B:=Z ∘ turn T; have hZ(u:Word (Bank F d)):turn (U ∘ u)= U ∘ turn u:= funext (fun i=> Eq.symm (map_smul U _ _)); have hQ(w): U (U w)=w:= pulls_p ..; change U ∘ u=turn u at he;
   have hU : U (u 0)=u 0:= (congr_fun he 0).trans (turn_zero _)
   have hx: U ∘ turn u=u:= by rw [← he ]; exact funext fun i=> hQ (u i);
   have h : predMarket B u=U ∘ turn (predMarket T u):= by
       conv_lhs => rw [ show u=U ∘ turn u from hx.symm ]; -- rw also T? hidden let. 
       unfold B Z U; rw [ pred_par,pred_turn ];
   have hT : B=T:= by
      apply ht.2.2; change Z (turn T 0)=0; rw [ turn_zero, show T 0=_ from hp,map_zero ];
      unfold announce; rw [ h ]; funext i; change D.D ( U ( ( segment i ) • predMarket T u i ))=_; rw [map_smul,map_smul, D.color ]; change ((-1:ℝ)^i) • ( Z ( ( D.D ∘ predMarket T u ) i ))= _; rw [ show D.D ∘ predMarket T u= _ from ht.1 ]; unfold just; split
      next hi=> subst i; rw [ pow_zero,one_smul ]; rw [hu] at hU; exact (D.color V|>.symm).trans (congr_arg D.D hU)
      next _=> rw [map_zero,smul_zero]
   rw [hT] at h; change U ∘ predMarket T u=_; exact funext fun i=> Eq.trans (congr_arg (fun p=> U (p i)) h) (hQ (turn (predMarket T u) i))
-- use assumption Knocker.Compiled
variable (V:Warehouse G)(h:G.Simple) {O:Booked (wings G)}(M:MS_Data G O){v s:ℝ}(T:Booth s V.F)(Sx: Pic.pass V h M T)
variable (H₁:Knocker h T (q:=3) (hq:=by decide) ( BoxOffice.warehouse V ))
local notation "F'" => V.F
local notation "K'"=> BoxOffice.warehouse V
local notation "δ"=> nested V.F h K'
local notation "Θ"=> Xray V h M T v Sx
local notation "Q"=> Pic.X V h M v T
include Sx H₁
lemma tuneX : tone Q:= by
   intro d; obtain hv:= Pic.underlying V M v T Sx d (3:ℕ+) (by decide); let p(i):=renormal K' 3 h T i d; let B(k):= (Q).lives d k; let f v:=pulls (par F' d) v; let ζ (s:Pert.Position.Section F' d):=lookie V.F s;
   have hc(k:ℕ)(s:Pert.Position.Section F' d) : Tendsto (fun i=> ζ s ( f (p i k))) atTop (𝓝 (ζ s ( f ( B k ) ))):= by unfold ζ f; simp_rw [pulls_at ]; exact hv k _
   funext i k t; ext1 v; let s:Pert.Position.Section F' d := ⟨ k,v,t ⟩; let R:=ζ s; apply tendsto_nhds_unique ( f:=fun j=> R ( f (p j i))) (hc i s); apply ( show Tendsto (fun j=> R (segment i • p j i)) atTop (𝓝 ( R ( segment i • B i ))) from ?_ ).congr'; swap; · simp_rw [R, map_smul ]; exact ( hv i s ).const_smul _
   filter_upwards [ H₁.tensorP d ] with k hk; exact (congr_arg R (congr_fun hk i)).symm
lemma ratePar (t:ℝ) : Jet.turn ( ψ Θ t )= -( ψ Θ t ):= by
    let Y:= (Q).swell t; have he : Y= Hop.act Q (Θ t):= ( real_X V h M T v Sx ).eats t;
    have hh:Y.Fresh:= he.symm ▸ ( Hop.approach _ _ ( Pic.innerX .. ) );
    have ht : tangible Q δ T:= vitalX V M T v Sx; have hm := tune Q t ( Pic.innerX V M v T|>.1 ) ( tuneX V h M T Sx H₁ ); obtain hd: elliptic ( predMarket ((δ 6).report ( Y.lives 6 )) (Y.lives 6) ) := meter _ (hh.2 6) (hm _);
    have hw : ψ Θ t= testable Y δ T:= by rw [he, Hop.interest _ _ _ T ( Pic.innerX .. ), Pic.modeX V M v T Sx, head_ren (Θ t|>.rooted) ]; -- fix
    rw [hw]; exact Bend.meter_odd T _ hd
lemma beta_first (i:ℕ)(hi:Even i): Month.β Θ i=0:= by
    have hv(t:ℝ): ψ Θ t i=0:= by
       obtain he:= congr_fun ( ratePar V h M T (v:=v) Sx H₁ t ) i; change (-1:ℝ)^i • ψ Θ t i= -(ψ Θ t i) at he; rw [hi.neg_one_pow,one_smul] at he; exact ( by linarith );
    unfold Month.β; rw [funext hv]; simp
-- implies shape for Ms. β_m(g)=g³..., W major. derive quadratic zero via law(not odd automatically). also CHECK.Note.
open Meter PowerSeries
lemma second₀ : Month.β ( Mray V h M T v Sx ) 2=0:= by
    let U:= Mray V h M T v Sx; let f:= transfer V M T v Sx; let X:=Xray V h M T v Sx; let μ:=Month.β U; let t:=Month.β X;
    have hp : t 0=0 ∧ t 1=0:= ( Forge.real_X V h M T v Sx ).zeroβ; have hx : t 2=0:= beta_first V h M T Sx H₁ 2 (by decide)
    have hm:μ 0=0∧μ 1=0:= (Forge.real_ms V h M T v Sx).zeroβ;
    have he : (↑(Jet.ren f.f μ 2) :ℂ)= (μ 2:ℂ):= by rw [Elegant.renReal _ ( f.rooted ),Finset.sum_range_succ,ageT (litK f.rooted),bill_q, f.primary, Finset.sum_range_succ, sum_range_succ,sum_range_zero, hm.1,hm.2 ]; simp
    apply Complex.ofReal_injective; nth_rw 1 [ ← he ]; obtain hk:= PowerSeries.ext_iff.mp ( Forge.β_law V h M T v Sx ) 2; -- exists?
    rw [ show Jet.ren f.f μ 2=PowerSeries.coeff 2 (PS (Jet.ren f.f μ)) from Eq.symm (coeff_mk ..), hk, coeff_mul ]; -- maybe let opacity
    apply congr_arg Complex.ofReal; refine Finset.sum_eq_zero fun j hj=>?_ ; have h':j.2≤2:= by obtain hv:= mem_antidiagonal.mp hj; omega
    change _ * coeff _ (PS t)=_; simp only [PS,coeff_mk ]; interval_cases j.2 <;> simp_all
end YM.FVA2.Forge.Parity
