import YM.MSbar.Mosaic.Bubble
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
open Measuring Cane Laurent Bloch UVNext.PricedKernels Spruce Lapaz
open Next.SectorChange Bulk Posture
variable {ι:Type}{X f g A B R U C E V K P:ι→ℝ}{D M N z :ι→ℕ}{φ:Filter ι}
namespace Run
variable (hX:Tendsto X φ atTop) {p k m:ℕ}{b v:ℝ}
include hX
lemma payD (G:Gauge)(p:ℕ)(v:ℝ)(ht:Run φ X f (-(1/2)))(he:Run φ X A 0)(hb:Run φ X C 0)(hp:Run φ X V 0) : Run φ X (fun x=>Tilt.coal G p v (A x) (f x) (C x) (V x)) (epsW p):=by
    refine Run.count hX (range (p+1)) (fun i x=> f x^i * (fCost v (f x) (C x) (p-i)* A x*((G.lieDim+1:ℕ)*V x))) ?_; intro i hi
    have hr:= (ht.raise hX (p-i+1)).Yrat hX (hb.Ypow hX (p-i+1)); have hx:= ((ht.raise hX i).mulR hX (((hr.mulY hX v).Yrat hX he).Yrat hX (hp.mulK hX ((G.lieDim+1:ℕ):ℝ))))
    apply Run.loosen hx; have hh : i + (p-i+1) = p+1:=by have he:=mem_range.mp hi;omega
    rw [←mul_add, ←Nat.cast_add (R:=ℝ),hh]; exact_mod_cast (show -(1/2:ℝ)*(p+1:ℕ)≤ epsW p from (by push_cast; linarith only [(mp0 p).1])) -- fix
variable (S:Patch)(G:Gauge)(c1 c2 c3 c4 c5 c6 c7:ℝ)
variable (ht:Run φ X f (-(1/2)))(he: Run φ X V 0)(hb: Run φ X U 0)(hd: Run φ X K (pawn p))(hw:Run φ X P 0)(hC:Run φ X E 0)(hn:Run φ X (fun i=> (M i:ℝ)) 0)(hk:Run φ X (fun i=> (D i:ℝ)) 0)
local notation "A'" i=> Issue.Ages' c1 c2 c3 c4 (V i) (U i) c7 (E i) c5 c6 (K i) (P i)
include ht he hb hd hw hC hn hk
lemma tariff : Run φ X (fun i=> Ages.cost (A' i) (f i) p G S (M i) (D i)) (epsW p):=by
    let q(x):= c2*f x*V x^2; have hq:Run φ X q (-(1/2)):= (ht.mulK hX _).Yrat hX (he.Ypow hX _); let Q(x):ℝ:= ((D x*G.lieDim:ℕ):ℝ); have hQ:Run φ X Q 0:= by unfold Q; push_cast; exact hk.mulY hX _
    let k(x):=4*V x; have hg:Run φ X k 0:=he.mulK hX _; let u:=- (1/2:ℝ); have hL:pawn p+u≤ epsW p:=by unfold u epsW; linarith only
    unfold Ages.cost; refine Run.addR hX (Run.addR hX ?_ ?_) ?_
    · dsimp only [Issue.Ages']; exact Run.addR hX (Run.addR hX (Run.loosen (hd.mulR hX (hQ.Ycost hX (hq.mulK hX 2))) hL) (Run.loosen ((hd.mulR hX hq).Yrat hX (hQ.Ymul hX (hw.mulK hX 2))) hL)) ((Run.payD hX G p _ ht he hg hC).Yrat hX (Run.Ymul hX hQ (hg.addR hX hg)))
    · refine Run.Ycost hX ?_ (Run.tr hX ht); dsimp only [Issue.Ages']; exact (((hn.mulY hX _).Ymul hX ( Run.mulK hX (Run.Ypow hX hb _) _))) -- W₀*cities Nat cast? `W0*cities*ℝ` coerces nat mul
    apply Run.Ycost hX ?_ (Run.tr hX ht); dsimp only [Issue.Ages']; exact ((hn.mulY hX _).Ymul hX (Run.mulK hX (Run.Ypow hX hb _) _))
end Run
end YM.MSbar.Mosaic
