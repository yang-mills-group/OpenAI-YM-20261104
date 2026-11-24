import YM.MSbar.Mosaic.Cue
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
variable {G:Gauge}(s:Side){ι τ:Type*}{X f g:ι→ℝ}{Z: Filter ι}{L:ℝ}
variable (hX:Tendsto X Z atTop){p:ℕ}
local notation "☉"=>Run Z X
noncomputable def epsW (p:ℕ):ℝ:= pawn p-1/16
noncomputable def lease(p:ℕ):ℝ:= pawn p-1/32
lemma mp0 (p:ℕ): (-1:ℝ)/2*(p+1)≤ epsW p∧epsW p< pawn p∧pawn p≤-1/8:=by unfold epsW pawn; constructor; linarith; constructor; linarith; linarith only [Nat.cast_nonneg (α:=ℝ) p]
local notation "q!"=>pawn p
local notation "ε"=>epsW p
local notation "P"=>- (1/2:ℝ)
local notation "V"=> Run Z X
namespace Run
variable {k a b d:ℝ}
include hX
lemma transfer(t:ℕ)(hk:f= g):V f ε → V g ε:= by rw [hk]; exact id
lemma tr(h:V f P): V (fun i=> (f i)^(p+1)) ε:= by apply (raise hX h _).loosen; push_cast; linarith only [(mp0 p).1]
open Lapaz
lemma merit(h:Run Z X f 0)(p:ℕ):Run Z X (fun i=>bag p (f i)) 0:= Run.count hX (Finset.range (p+1)) (fun j i=>(j.factorial:ℝ)⁻¹*(f i)^j) (fun j _=>Run.mulK hX (Run.Ypow hX h j) _)
lemma breeze(hf:Run Z X f P)(hp:Run Z X g 0)(l:ℝ) (p:ℕ): Run Z X (fun i=> bores p (f i) (g i) l) (epsW p) := by
    have he := hf.Yrat hX hp; refine Run.addR hX (Run.mulY hX (he.tr hX) _) ?_; apply Run.count hX (Finset.range (p+1)) (fun j i=> ((j:ℝ)*(f i)^(p+1)*(g i)^j)/(j.factorial:ℝ)); intro j _; simp_rw [div_eq_mul_inv]; exact Run.mulY hX ((Run.mulK hX (hf.tr hX) _).Yrat hX (Run.Ypow hX hp j)) _
variable {A B d E D Q T R U W F G K:ι→ℝ}{c r:ℝ}{m:ι→ℕ}
variable (hτ:Run Z X f P)(h: Run Z X A (epsW p)) (hb: Run Z X B (epsW p)) (hh:Run Z X D (pawn p))
include hτ h hh
lemma slice (hu:Run Z X U 0)(r : ℝ) : Run Z X (fun i=>deltaC (A i) (D i) (U i) 0 0 r (f i) p) ε :=by
    obtain ⟨hx,he,hY⟩:=mp0 p; have hh0 : pawn p<0:= hY.trans_lt (by norm_num)
    have hz:= Run.bouquet hX hh hh0; have hv: Tendsto (fun i=>r+D i + A i) Z (𝓝 r):=by simpa using! ((hz.const_add r).add (h.bouquet hX (he.trans hh0)))
    have hR: Run Z X (fun i=> Real.exp (r+D i+A i)) 0:= Run.exp hX hv
    have hP:= ((hh.raise hX 2).Yrat hX (Run.exp hX hz)).mulK hX (Real.exp r); have hQ:= (hh.mulY hX (Real.exp r)).mulR hX (hτ.Yrat hX hu); unfold deltaC; apply Run.addR hX; exact Run.addR hX (breeze hX hτ hu r p) (Run.Ycost hX hR h)
    apply Run.addR hX; exact hP.loosen (by push_cast; unfold epsW; linarith only [hY]); exact hQ.loosen (by unfold epsW; linarith)
omit hτ h hh
variable (hm:Run Z X (fun i=> (m i:ℝ)) 0)
include hm
lemma sheet(c:ℝ)(n:ℕ):Run Z X (fun i=>boreo (m i) c n) 0:=by unfold Lapaz.boreo; exact Run.addR hX (Run.token hX _) (Run.mulY hX hm _)
lemma spanP (p j:ℕ) (c :ℝ)(hf:Run Z X F 0): Run Z X (fun i=> cloudK (m i) p j c (F i)) 0:= Run.mulK hX (Run.Ymul hX (merit hX hf p) (sheet hX hm c _)) _ -- F var
lemma divP (p:ℕ)(hf:Run Z X f 0)(hp:Run Z X g 0):Run Z X (fun i=> division (f i) (g i) p) 0:=by -- omit hm
    unfold division; exact (Run.mulK hX hf _).Ymul hX ((Run.addR hX (Run.token hX _) (Run.mulK hX hp _)).Ypow hX p)
lemma spanL (p j:ℕ) (c :ℝ)(hA: Run Z X f 0)(hB:Run Z X g 0):Run Z X (fun i=> Lapaz.cloudL (m i) p j c (f i) (g i)) 0 := by unfold cloudL; apply divP hX hm; exact Run.mulK hX ((hB.Ymul hX (merit hX hA p)).Ymul hX (sheet hX hm c _)) _; exact spanP hX hm _ _ c hA
-- fish.Storm
variable (hp:Run Z X Q (epsW p))(hv:Run Z X (fun i=>(Q i)⁻¹) L)(hρ:Van Z X R)
include hp hv hρ
lemma fishing (x:ℕ)(c:ℝ)(hf:Run Z X f 0):Run Z X (fun i=>fish (m i) x c (f i) (Q i) (R i)) ε:=hp.Yrat hX ((hf.Ypow hX _).Ymul hX (sheet hX hm c _))|>.addR hX (Van.mulL hX hv hρ _)
variable (hs:Run Z X K 0)(ht:Run Z X G 0)(hu:Run Z X U 0)(hd:Run Z X W 0) -- payQ payH; m; spacePin.
include hτ h hh hm hp hv hρ hs hu --
lemma primary (j:ℕ)(c r:ℝ):Run Z X (fun i=> deltaC (A i) (D i) (U i) 0 0 r (f i) p+(fish (m i) (j*p) c (bag p (K i)) (Q i) (R i) + fish (m i) 0 c (D i) (Q i) (R i))) (epsW p):=by
    apply Run.addR hX (slice hX hτ h hh hu r); apply Run.addR hX; exact fishing hX hm hp hv hρ _ _ (merit hX hs _); exact fishing hX hm hp hv hρ _ _ (hh.loosen ((mp0 p).2.2.trans (by norm_num)))
include hb ht hd
lemma stamped (j:ℕ)(r c:ℝ):Run Z X (fun i=> expBill p j (m i) (Q i) c (f i) (K i) (G i) (D i) (A i) (B i) r (U i) (W i) (R i)) (epsW p):=by
    obtain ⟨hx,he,hY⟩:=mp0 p; have hh0:pawn p <0:= hY.trans_lt (by norm_num)
    let S(i):=cloudL (m i) p j c (K i) (G i); let Tx(i):= cloudK (m i) p j c (K i); let Hδ(i):= deltaC (A i) (D i) (U i) 0 0 r (f i) p; let H(i):= Hδ i+(fish (m i) (j*p) c (bag p (K i)) (Q i) (R i)+fish (m i) 0 c (D i) (Q i) (R i)); let Vx(i):= debit p (U i) r (D i) (A i) (f i) (B i) (Hδ i) (W i)+(fish (m i) (j+j*p) c (G i*bag p (K i)) (Q i) (R i)+fish (m i) j c (D i*G i) (Q i) (R i))
    have hP:Run Z X H ε:=primary hX hτ h hh hm hp hv hρ hs hu _ _ _; have h0:Run Z X Hδ ε:=slice hX hτ h hh hu _; have hS:Run Z X S 0:=spanL hX hm _ _ _ hs ht; have hT:Run Z X Tx 0:= spanP hX hm _ _ _ hs
    have hv' : Run Z X (fun i=> Vx i) ε:=by
        unfold Vx debit; apply Run.addR hX
        · have hx:Tendsto (fun i=>r+D i+A i) Z (𝓝 r):=by simpa using! (((hh.bouquet hX hh0).const_add r).add (h.bouquet hX (he.trans hh0)))
          exact (((((Run.exp hX hx).Ycost hX hb).addR hX (Run.Ycost hX hd h0)).addR hX (((hh.mulR hX hτ).Yrat hX hd).loosen (by unfold epsW;linarith))).addR hX (Run.Yrat hX (Run.tr hX hτ) ((merit hX hu p).Ymul hX hd)))
        exact (fishing hX hm hp hv hρ _ _ (Run.Ymul hX ht (merit hX hs _))).addR hX (fishing hX hm hp hv hρ _ _ (Run.Ymul hX (hh.loosen hh0.le) ht))
    let Δ':= (-1)/(8:ℝ); have hy : Run Z X (fun i=> f i*Tx i + D i+ H i) Δ':= by
             apply Run.addR hX; · exact (((hτ.Yrat hX hT).loosen (by unfold Δ'; norm_num)).addR hX (hh.loosen hY))
             exact hP.loosen (he.le.trans hY)
    unfold expBill Survey.fee; refine Run.mulK hX (Run.addR hX (Run.addR hX (Run.addR hX (Run.addR hX ?_ hv') (Run.Ycost hX hS hP)) ?_) ?_) _
    · exact Run.Yrat hX (Run.tr hX hτ) (Run.Ymul hX hS hT)
    · exact (Run.mulR hX hh (hτ.Yrat hX hS)).loosen (by unfold epsW; linarith)
    exact ((((hh.Yrat hX ht).Yrat hX (sheet hX hm c _)).addR hX (hh.Yrat hX hS)).mulR hX hy).loosen (by unfold epsW Δ'; linarith)
end Run
end YM.MSbar.Mosaic
