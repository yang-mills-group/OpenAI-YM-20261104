import YM.MSbar.Mosaic.Pay
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
open Next.SectorChange Bulk Posture JetTab
variable {G:Gauge}
namespace Run
variable {ι:Type}{X f' g V W E D r:ι→ℝ}{φ:Filter ι} [φ.NeBot] (hX:Tendsto X φ atTop) {p q:ℕ}{b:ℝ}
include hX
lemma rails (a:ℝ)(i j k m:ℕ)(hv:Run φ X V 0): Run φ X (fun x=>Whisk.rail i j k a (V x) m) 0:=by
    induction m with
    | zero=> exact hv
    | succ m ih=> unfold Whisk.rail Whisk.stair; exact ih.addR hX ((ih.addR hX (Run.mulK hX ih a)).addR hX (Run.mulK hX ((Run.addR hX (ih.Ypow hX _) ((ih.Ypow hX _).mulK hX _)).mulK hX _) _))
lemma park(a:ℝ)(p q:ℕ)(hv: Run φ X V 0):Run φ X (fun x=> Spruce.cardK p q a (V x)) 0:= by unfold cardK Whisk.driver; exact ((rails hX a _ _ _ _ (hv.addR hX hv)).mulK hX _)
lemma harbor(p:ℕ)(hv:Run φ X V 0)(hw:Run φ X W 0):Run φ X (fun x=>Cash.glow_cost (V x) (W x) p) 0:=by
    induction p with
    | zero=> exact Run.token hX 1
    | succ i ih=> unfold Cash.glow_cost; refine Run.addR hX (Run.addR hX (Run.addR hX ih ?_) ?_) ?_; exact (Run.Ymul hX hv ih|>.mulK hX _); exact hv.Ymul hX hw; exact (hv.Ypow hX _).Ymul hX hw
variable (J:Voice G)(P:Palisade)
variable {σ Δ U:ι→ℝ}{c d k:ℝ} (hT:Run φ X (fun i=>(r i)⁻¹) (1/2))
include hT
lemma probe (p j:ℕ)(b:ℝ): Van φ X (fun i=> peg (r i) (Issue.thorn (X i) p) (pillow (X i)) (topP J P (X i)) (spotN (X i)) b):=by
    have he:= Issue.nearB hX 1 one_pos p 0|>.1; let φ'(i):=Real.exp (-Issue.thorn (X i) p*spotN (X i)); let h i:= topP J P (X i)+pillow (X i); have hv:Run φ X h (-(1/2)):=by obtain ⟨_,_,h₂,_,h₃⟩:= height hX P J; exact (h₃.loosen (by norm_num)).addR hX h₂
    have hf : Run φ X (fun i=> (b*h i)*(r i)⁻¹) ((-(1/2))+(1/2)):= (hv.mulK hX b).mulR hX hT
    intro t; have hv: Van φ X (fun i=> φ' i*((b*h i)*(r i)⁻¹)):= Van.mulL hX hf he; exact (hv t).alter (Eventually.of_forall (fun i=>by unfold peg h φ'; ring))
variable (he:Run φ X E 0) (hp:Run φ X V 0)(hz:Run φ X D 0)
include he hp hz
-- compare global to local α.Vault donor N.
lemma tariffs (p n:ℕ)(b d:ℝ):
       let X'(i):= Issue.thorn (X i) n; let r'(i):=spotN (X i); let c(i):= topP J P (X i); let a(i):=pillow (X i)
       Van φ X (fun i=>tower (r i) (X' i) (a i) (c i) d b (V i) (E i) p (r' i) n+finC n (r' i) (r i) (X' i) (a i) (c i) b d (D i) (E i) (V i)):=by
    intro Y Q C A
    have hv':Van φ X (fun i=> Real.exp (-Y i* ↑(Q i))) := (Issue.nearB hX 1 one_pos n 0).1; let K:= fun i=>Real.exp (-Y i*↑(Q i)); let L(i):= Spruce.peg (r i) (Y i) (A i) (C i) (Q i) d; have he':Van φ X L:=probe hX J P hT n p d
    let v1(x):= 1+V x; have hL:Run φ X v1 0:= (Run.token hX _).addR hX hp; let W'(x):=E x*(1+V x)^(n+1); have hV: Run φ X W' 0:= he.Ymul hX (hL.Ypow hX _); have ht':Van φ X (fun i=> (Real.exp (-Y i* ↑(Q i))*(d*b)+L i)):= Van.summa hX he' (Van.mulL hX (Run.token hX _) hv'); let V':= fun i=>V i+stepW (n+1) b; have hχ:Run φ X (fun i=>Spruce.spend n (V i) b (D i)) 0:=by unfold Spruce.spend; refine harbor hX _ ?_ ?_; exact (hL.addR hX (Run.token hX _)); exact (hz.mulY hX _).Ymul hX ((hp.addR hX (Run.token hX _)).Ypow hX _)
    have ht:Van φ X (fun i=> Spruce.toll n (Q i) (Y i) b d (L i)):=Van.summa hX (Van.mulL hX (Run.token hX _) (Van.mulL hX (Run.token hX _) hv')) he'
    intro x; unfold tower finC; apply Run.addR hX; apply Run.mulK hX; exact Run.Ycost hX (park hX _ _ _ hV) (ht' x)
    exact (Run.mulK hX (((ht x).Yrat hX hχ).Yrat hX hV) _)
end Run
end YM.MSbar.Mosaic
