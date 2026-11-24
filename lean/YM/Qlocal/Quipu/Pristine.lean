import YM.Qlocal.Quipu.Tracks
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
-- witness gauge.Flow limit plus at any fixed position all short canonical slip entries. Costs next. gauge U(t) definition fixes spelling uppercase. Use engine `rule` with `exteriorL`. no unit dilations hidden.St.V.
local notation "S"=> Coarse G
local notation "Ω"=> rule (Coarse G) n
local notation "X"=> fieldDir G n 1
namespace Macarons
set_option quotPrecheck false
variable (χ:G.El) (O:Lattice.Order) (p:Site n) {x:rule (Coarse G) n}
local notation "T"=> lifts O p χ x
abbrev gaze (χ:G.El) (n:ℕ) : G.El → G.Color:= G.adjoint χ ∘ (theta G n) ∘ G.curvature
local notation "W"=> gaze χ k
local notation "p₀"=> ports G n
variable {u:Cover} (i: Axis)
abbrev hue (i:G.ColorIndex)(t:G.Color):= t i
abbrev fly (O:Lattice.Order) (v:Cover)(x:rule (Coarse G) n)(i:Axis)(i':G.ColorIndex) (χ:G.El)(k:ℕ)(t:ℝ) := (gaze χ k (travel (passing x t) p (trail O v i))) i'
abbrev airport (u:Cover)(i:Axis)(z:G.ColorIndex):Leaf n (Coarse G) := (bent p u, coord i,z)
local notation "p'"=> (airport p)
lemma glow (v:Walk) : ContDiffAt ℝ ω (fun t:ℝ=> gaze χ k (travel (passing x t) p v)) 0:= by -- replace θk
   let l(t:ℝ):= travel (passing x t) p v; let C:=G.curvature ∘ l; have hl: ContDiffAt ℝ ω C 0:= curve_c G (mellow x p v) -- arity x argument order read #check.Mellow
   exact (G.adjoint χ).toContinuousLinearMap.contDiff.contDiffAt.comp _ ((theta_cont G k).contDiffAt.comp (f:=C) _ hl)
lemma tinted(v:Cover)(j:G.ColorIndex): ContDiffAt ℝ ω (fly p O v x i j χ k) 0 := (EuclideanSpace.proj (𝕜:=ℝ) j).contDiff.contDiffAt.comp _ (glow χ p (x:=x) (k:=k) (trail O v i))
lemma brightLine {u : Cover} (he: 2*(size u +1)<n.val) (i':G.ColorIndex) : Act k (fly p O u x i i' χ k) (someJ fun t:ℝ=>t*lifts O p χ x t (airport p u i i')):= by
   let e := airport p u i i'; let l(t:ℝ):= travel (passing x t) p (trail O u i); let M:=blade O p χ x; let m(t:ℝ) : G.El:= M t (bent p u,i); let w(t:ℝ):= G.mat (m t); let T0:=lifts O p χ x; have hf:m 0=1:=by unfold m M; rw [bornQ]; rfl
   have hx(t:ℝ): m t= χ*l t*χ⁻¹ := joins (passing x t) O p χ u i he; have hm:ContDiffAt ℝ ω w 0:= planeQ O p χ x (bent p u,i); let gφ:= (theta G k) ∘(G.curvature ∘ m)
   let f₀: ℝ→G.Color:= G.plog ∘ w; let Φ:= EuclideanSpace.proj (𝕜:=ℝ) i'
   have hX : Act k gφ (someJ f₀):= ⟨(theta_cont G k).contDiffAt.comp _ (curve_c G hm),fun j hj=> by rw [someJ,someJ, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]; rw [show iteratedFDeriv ℝ j gφ 0=_ from (legacy G k hf hm j hj)]; rfl ⟩ -- Eq rfl may
   have hl:Φ ∘ gφ = fly p O u x i i' χ k := by funext t; change (theta G k (G.curvature (m t))) i'= _; rw [hx t,G.curvature_conjugate,theta_moves]; rfl
   have hh: (fun t:ℝ=> t * lifts O p χ x t (airport p u i i'))=(Φ ∘ f₀):= by
     funext t; change (t • lifts O p χ x t) e = Φ (G.plog (w t)); rw [rhythm]; change G.plog (G.mat (M t (bent p u, _))) i'= _ -- maybe change
     rw [show axisEquiv.symm ((outsider G n e).1.2)=_ from axisEquiv.symm_apply_apply i]; rfl
   rw [hh,← hl]; have hp : ContDiffAt ℝ ω f₀ 0 := ( (show w 0=1 by simp [w,hf]).symm ▸ G.plog_diff : ContDiffAt ℝ ω G.plog (w 0)).comp _ hm
   refine ⟨hX.linear.nice,fun j hj=>?_⟩; exact ((hX.linear (L:=Φ)).writes _ hj).trans (((eo_Act k hp).linear (L:=Φ)).writes j hj).symm
section postage
variable {F:Set α}{s:Senses R}{w:Slip (Point ((Coarse G) ⊕α))}(h: Dais.good s.val (Dais.chain w))
local notation "I"=> (Fin (List.length (Dais.coin w)))
local notation "v₀"=> position h (Sonnet.root s)
variable (z:α→Site n)
local notation "pℓ"=> z (Sonnet.root s)
local notation "Xκ"=> (there z h)
local notation "Y"=> (lifts O (z (Sonnet.root s)) χ x)
abbrev ent (x:rule (Coarse G) n)(i:I)(t:ℝ):= fly pℓ O (purse w (Dais.position (s:=s) (P:=chain w) h (Sonnet.root s)) i) x (papers w i) (tend w i) χ k t -- h.S parse
private abbrev happy(i:I) := (fun t:ℝ=>t*(Y t) (airport (z (Sonnet.root s)) (purse w (Dais.position (s:=s) (P:=chain w) h (Sonnet.root s)) i) (papers w i) (tend w i)))
local notation "u₁"=> (ent χ O h z x (k:=k))
noncomputable abbrev flock (χ:G.El)(O:Lattice.Order) {s:Senses R}{w:Slip (Point ((Coarse G) ⊕α))}(h: Dais.good s.val (Dais.chain w))(z: α→ Site n)(x:rule (Coarse G) n)(k:ℕ) (t:ℝ) := ∏ i : Fin (coin w).length, ent χ O h z x i t (k:=k)
variable (hk:2*(meter w+1)<n.val)
private lemma flute(v:Finset I): ContDiffAt ℝ ω (fun t=>∏ i∈v,u₁ i t) 0:= contDiffAt_prod fun i hi=> tinted ..
include hk
private lemma pays(v: Finset I) : Act k (fun t=> ∏ i∈v,u₁ i t) (someJ (fun t=> ∏ i∈v, happy (x:=x) χ O h z i t)):= by
 let f i:=happy (x:=x) χ O h z i; have ht (i : I): Act k (u₁ i) (someJ (f i)):= brightLine χ O _ _ (show 2*(size (purse w (Dais.position (s:=s) (P:=Dais.chain w) h (Sonnet.root s)) i)+1)< _ by have hh:= face_v h i; omega) (tend w i); have hf(i : I):ContDiffAt ℝ ω (f i) 0:= contDiffAt_id.mul ((contDiffAt_pi.mp (necessary_shift ..)) _) -- α arg order
 induction v using Finset.induction_on with
 | empty=> simp only [Finset.prod_empty]; exact eo_Act _ contDiffAt_const
 | insert i s hi ih=>
    refine ⟨flute ..,fun j hj=>?_ ⟩; let G0(t:ℝ):=∏ i∈s,f i t; have hp : Act k G0 (someJ G0):= eo_Act k (contDiffAt_prod fun i _=> hf i)
    simp_rw [Finset.prod_insert hi]; exact ((exact_prod (ht i) ih).writes _ hj).trans (((exact_prod (eo_Act k (hf i)) hp).writes j hj).symm)
lemma invoice_eq : Act k (flock χ O h z x k) (someJ (fun t:ℝ=> t^(List.length (Dais.coin w)) * invoice (there z h) (Dais.coin w) (lifts O (z (Sonnet.root s)) χ x t))) := by
   let v:=pays χ O h z (k:=k) hk (Finset.univ:Finset I) (x:=x); rw [show (fun t:ℝ=> t^ (List.length (Dais.coin w))* _)= (fun t=>∏ i:I,happy (x:=x) χ O h z i t) from ?_]; swap
   · ext1 t; rw [paid_terms]; unfold happy; rw [prod_mul_distrib,prod_const,Finset.card_univ,Fintype.card_fin]; rfl -- for rw β red
   exact v
end postage
end Macarons
end Incline
end YM.Qlocal.Quipu.Eluder
