import YM.MSbar.Chord.Roots
import YM.Push.STATIONARY_UNIFORM.HessCost
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Midpoint
open Function Filter Rolling Lattice RG Wilson Push Uniform
open Precision Gauge MSbar.Wave StressFlux
open scoped Topology Matrix.Norms.Frobenius ContDiff Classical BigOperators InnerProductSpace
open AnalyticBridge.VerifiedReset Work.F03 Next.Free Finset
variable {G:Gauge}{n:Side}{Q:FaceRail n G}{Z:ℝ}
local notation "S₀"=> Site n
local notation "X"=> Positions (Primary n G)
local notation "H"=> tint G (Exterior.Body 1 n)
local notation "N"=> (n.val:ℝ)
-- un-translate for anchors; gross read is used through-out, not forcing all arrays translation in its definition
noncomputable def grossH (Q:FaceRail n G)(e:G.Color):ℝ := (Fintype.card (Site n):ℝ)⁻¹*gross (fun x y=>Q x y) e
lemma ticker (t:S₀)(s:G.Color)(i:S₀): bandE 1 t (tuner s (i+t))=tuner s i:=by
    have he:=gradient_shift ((i,1):Edge S₀) t 1 s; rw [show sign 1 (1:Axis)=1 from rfl, one_smul, show sendEdge 1 t (i,1)=(i+t,1) from (by simp [sendEdge,Step.used,posDir,affine])] at he; exact he
lemma ticketG (x y s:S₀)(l: Axis): coord (x+s) (y+s) l=coord x y l:=by unfold coord; rw [show y+s-(x+s)=y-x by abel]
lemma close (h:Ribbon Q)(e:G.Color) : grossH Q e= anchor n Q e:=by
    let K(i:S₀)(j:S₀):= Q (tuner e i) (tuner e j)*coord i j 0 ^ 2
    have hA:anchor n Q e=∑ j,K 0 j:=by unfold anchor Moment; refine Finset.sum_congr rfl (fun j _=>?_); unfold K cell tuner mold middle halfE zone; simp only [↓reduceIte,zero_ne_one, List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,halfE];ring
    have hz(i:S₀)(j:S₀): K i j=K 0 (j - i):=by
        have hp(s:S₀)(u v:S₀): K (u+s) (v+s)=K u v:=by unfold K; rw [ticketG, ← h.axial 1 s, ticker s e u,ticker s e v]
        simpa only [zero_add,sub_add_cancel] using hp i 0 (j-i)
    have hf(i:S₀): ∑ j,K i j=anchor n Q e:=by rw [hA,funext (hz i)]; exact Equiv.sum_comp (Equiv.subRight i) (K 0)
    unfold grossH gross; change _*(∑ i:S₀,∑ j:S₀,K i j)= _; simp_rw [hf,sum_const, Finset.card_univ,nsmul_eq_mul]; exact inv_mul_cancel_left₀ (by positivity) _
-- formulas.
variable (R:PathData G)(q:Clip)
variable {σ C Λ:ℝ}(hp:R.Bounds q σ C Λ)
noncomputable abbrev collectT (n:Side)(R:PathData G)(p:Clip): Positions (Primary n G)→ℝ:= main n p R ∘ (tint G (Exterior.Body 1 n))
local notation "δ"=> innerSL ℝ (E:=G.Color)
lemma tendQ {D:Type}[NormedAddCommGroup D][NormedSpace ℝ D](f:D→ℝ) (h:ContDiffAt ℝ 2 f 0) (g:D→ℝ)(hp:∀ x:D,Tendsto (fun t:ℝ=> f (t•x)/t^2) (𝓝[≠] 0) (𝓝 (g x))) : f 0=0 ∧ fderiv ℝ f 0=0 ∧ ∀ x:D,iteratedFDeriv ℝ 2 f 0 ![x,x] = 2*g x:=by
   have hx (x:D):ContDiffAt ℝ 2 (fun r:ℝ=> f (r•x)) 0:= by apply h_place h x
   have hs(x):=Work.F03.value_slope_of_sq_limit (hx x|>.continuousAt) (hp x); have hu:f 0=0:=by simpa using (hs 0).1
   have hV:fderiv ℝ f 0=0:=ContinuousLinearMap.ext (fun x=> (Push.side f (h.differentiableAt (by simp)) x).unique (hs _|>.2)); refine ⟨hu,hV,fun x=>?_⟩; have he:= tendsto_nhds_unique (taylor_limit_two (hx x) (hs x).1 (hs x).2.deriv) (hp x); rw [Work.F03.line_second h hV] at he; linarith
where
 h_place (h : ContDiffAt ℝ 2 f 0)(x:D):ContDiffAt ℝ 2 (fun r:ℝ=> f (r•x)) 0 := (show ContDiffAt ℝ 2 f ((0:ℝ)•x) from by rw [zero_smul]; exact h).comp (f:=fun t:ℝ=> t•x) (0:ℝ) (contDiffAt_id.smul contDiffAt_const)
-- applications Γ. h-turn pair exact.Pay.Coupleing
noncomputable def unionC (s:Signed)(R:PathData G) (b:Face (Per n))(x: Positions (Primary n G)) :=ellLine R b (Bid.pulled (tint G _ x) s)
local notation "v!" => unionC
noncomputable def profitH (n:Side)(R:PathData G)(p:Clip)(x y:Positions (Primary n G)) := Patch.average fun s:Signed=> ∑ i:Face (Per n),(p.direct*inner ℝ (curlX s i x) (curlX s i y)+ inner ℝ (unionC s R i x) (unionC s R i y))
include hp
lemma square_price (x:Positions (Primary n G)) : rim (collectT n R q) x x = profitH n R q x x:=by
    let F:=collectT n R q; have hv:ContDiffAt ℝ 2 F 0:= ((show ContDiffAt ℝ ω _ (H 0) from (Work.F02.mainTerm_contDiffAt (n:=n) hp (fun i=> (represent_smooth i).contDiffAt))).comp _ (tint G (Exterior.Body 1 n)).contDiff.contDiffAt).of_le le_top
    let g(x'): ℝ:=profitH n R q x' x' /2; have ht(z:X): Tendsto (fun t:ℝ=> F (t•z)/t^2) (𝓝[≠] 0) (𝓝 (g z)):=by
        have hs(s:Signed):= ((gear_limit hp (Bid.pulled (H z) s)).add
            (uncut_limit (k:=0) (Bid.pulled (H z) s) R.cubic hp.width hp.three)).add
            (uncut_limit (k:=1) (Bid.pulled (H z) s) R.quartic hp.width hp.four)
        simp only [add_zero] at hs
        unfold F collectT Function.comp; simp_rw [map_smul]; unfold g profitH Patch.average main mainTerm Patch.average; simp_rw [mul_div_assoc,Finset.sum_div,add_div,represent_pulled, real_inner_self_eq_norm_sq]; simp_rw [mul_div_assoc]; simp_rw [wheel, Finset.sum_div,add_div,mul_div_assoc] at hs; exact (tendsto_finsetSum _ fun i _=> hs i).const_mul _
    have he:= tendQ F hv _ ht|>.2.2 x; rw [iteratedFDeriv_two_apply] at he; refine he.trans ?_; unfold g; ring -- codomain Type small D issue
private lemma union_add (s:Signed)(b:Face (Per n))(x y:X): unionC s R b (x+y) = unionC s R b x+unionC s R b y:=by
    unfold unionC ellLine; rw [← Summable.tsum_add (ellLine_summable R hp b (Bid.pulled (H x) s)) (ellLine_summable R hp b (Bid.pulled (H y) s))]; refine tsum_congr (fun i=>?_); change _ • basin s _ (x+y)=_; rw [map_add, smul_add];rfl -- notation
lemma rates (x y:Positions (Primary n G)): rim (collectT n R q) x y= profitH n R q x y:=by
   let V:=collectT n R q; let A:= rim V; let Y:=profitH n R q; have ht:ContDiffAt ℝ 2 V 0:=((show ContDiffAt ℝ ω _ (H 0) from (Work.F02.mainTerm_contDiffAt (n:=n) hp (fun i=>(represent_smooth i).contDiffAt))).comp _ (tint G (Exterior.Body 1 n)).contDiff.contDiffAt).of_le le_top
   have hp(z:X): A z z=Y z z:=square_price R q hp z
   -- Y symmetry
   have hh(a b:X): Y a b=Y b a:=by unfold Y profitH; simp only [real_inner_comm (curlX _ _ a),real_inner_comm (unionC _ _ _ a)]
   have he(a b c:X): Y (a+b) c=Y a c+Y b c:=by
       unfold Y profitH Patch.average; rw [←mul_add]; refine congr_arg _ ?_; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i _=>?_); rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun j _=>?_); rw [union_add R q ‹R.Bounds ..›,show curlX i j (a+b)=curlX i j a + curlX i j b from map_add (basin i j) a b, inner_add_left,inner_add_left,mul_add];ring
   have hv:= hp (x+y); rw [he,hh x,hh y,he,he] at hv -- order rewrite issues. need force
   rw [map_add,map_add,_root_.add_apply,_root_.add_apply,show A x y=A y x from ht.isSymmSndFDerivAt (by simp) _ _,hp,hp] at hv
   change A x y= Y x y; rw [show A x y=A y x from ht.isSymmSndFDerivAt (by simp) _ _]; linarith only [hv, hp x, hp y, hh x y]
end YM.MSbar.Midpoint
