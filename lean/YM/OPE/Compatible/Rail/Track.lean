import YM.OPE.Compatible.Rail.Filly
/-!
# Actual readers third fourth loop. Along rays adequate, sym per polarization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free WithLp Work.F08 Matrix Bloch Precision Wilson Tree Exterior Asymptotics Work.F05 Stationary
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type} {G:Gauge}{c f:Side}{S: StepData c f}{F:Forest S.ratio}{R T:PathData G}{s α U V b γ Λ:ℝ}{p q:Clip}{N:ChartRatio G}
namespace Virgin
local notation "C"=>Bid.Dir G c
local notation "P"=>AxisChart G F
abbrev pane (F: Forest S.ratio) (t:S.Choices)(p:Clip)(R:PathData G):= uncurry (score F t p R)
lemma viewer (t:S.Choices){g:C→P}(h: Critical F p R g): Stayed (pane F t p R) (cabin g):=by obtain ⟨hz,hh,hA,hB⟩:=solvedPath h t;exact ⟨hA,hz,hh,hB⟩
lemma marchX (t:S.Choices){g:C→P}(h:Critical F p R g)(hx:ClassicalMatch F p q R T g)(x:C):
    let K:= fun x:C => mainTerm q T (represent x)
    let A:=pane F t p R
    let u:=fieldT (cabin g) x
    let v:=fieldU (cabin g) x x
    iteratedFDeriv ℝ 3 K 0 ![x,x,x]=iteratedFDeriv ℝ 3 A 0 ![u,u,u] ∧ iteratedFDeriv ℝ 4 K 0 ![x,x,x,x]=iteratedFDeriv ℝ 4 A 0 ![u,u,u,u]+3*iteratedFDeriv ℝ 3 A 0 ![v,u,u] :=by
    intro K A u v; let Y:=cabin g; have hs:=viewer t h; have hw: (fun i=>tested F t p R i (g i))=ᶠ[𝓝 0] A ∘ viewS Y:=(crit_home h).eventually (scoreS F t p R); have he(n:ℕ)(hn:n≤4):iteratedFDeriv ℝ n K 0=iteratedFDeriv ℝ n (A∘viewS Y) 0:= ((hx n hn t).2.2).symm.trans (hw.iteratedFDeriv ℝ n|>.eq_of_nhds)
    rw [he 3 (by decide),he 4 (by decide),hs.tally x x x x]; exact ⟨hs.accrue x x x,by unfold u v A; ring⟩
def heatPay {X Y n:Type}[NormedAddCommGroup X] [NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][Fintype n][DecidableEq n](A:X × Y→ℝ)(M:Module.Basis n ℝ Y)(V: Funds n)(a b v:X × Y):ℝ:= (1/2:ℝ)*((V*HATCH A M v).trace+(V*ROACH A M a b).trace - (V*HATCH A M a * V* HATCH A M b).trace)
lemma luxury (t:S.Choices) {g:C→P}(h:Critical F p R g){M:Funds (Key F G)}(hx:damage (countingBasis F G) (score F t p R 0) 0=M)(hm:M.det≠0)(hr:R.Bounds p s U V)(hf:FiniteBound F R T p q α N g b γ Λ)(hh: LocalRatio N)(x y:C):
     let A:= pane F t p R
     let K:= cabin g
     let m:=countingBasis F G
     let u:=fieldT K
     iteratedFDeriv ℝ 2 (thermal F t p R g N) 0 ![x,y] = iteratedFDeriv ℝ 2 (springF F R) 0 ![ (u x).2, (u y).2]+heatPay A m M⁻¹ (u x) (u y) (fieldU K x y)-iteratedFDeriv ℝ 2 (taxY F N) 0 ![(u x).2,(u y).2]:=by
      intro A K m u; let T':= deposit A K m; have hs:Stayed A K:=viewer t h; have hv:Memo T' 0:=memo_pension m hs; have he: T' 0=M:=by rw [show T' 0=damage (countingBasis F G) (score F t p R 0) (K 0) from rfl,show K 0=0 from hs.zero]; exact hx
      let L:=fun i=>Real.log (T' i).det; have hL: ContDiffAt ℝ ω L 0:= hv.det_val.log (he.symm ▸ hm); obtain ⟨hz,hi⟩:= accountV F hh; obtain ⟨hf',hg⟩:= sophok F hr
      let U':= springF F R; let Z:= taxY F N; let Y:= (U' ∘ K)+(1/2:ℝ)•L-(Z∘K); have hc:ContDiffAt ℝ ω U' (K 0):= hs.zero.symm ▸ hf'; have hd: ContDiffAt ℝ ω Z (K 0):= hs.zero.symm ▸ hz; have hA: ContDiffAt ℝ ω ((U'∘K)+(1/2:ℝ) • L) 0:= (hc.comp _ hs.path).add (hL.const_smul (1/2:ℝ))
      have hY: harbor K p R t N=ᶠ[𝓝 0] Y:=by
         filter_upwards [(hs.zero ▸ hs.path.continuousAt.tendsto : Tendsto K _ (𝓝 0)).eventually (taxes F hh)] with i hi; exact congr_arg (fun x:ℝ=> _+ _ - x) hi -- elaboration
      have hb:=advert m hs x y
      rw [((pureHeat t h hh hf|>.trans hY).iteratedFDeriv ℝ 2).eq_of_nhds]; unfold Y
      rw [iteratedFDeriv_sub_apply (hA.of_le le_top) ((hd.comp _ hs.path).of_le le_top), iteratedFDeriv_add_apply (g:=(1/2:ℝ) • L) ((hc.comp _ hs.path).of_le le_top) ((hL.const_smul (1/2:ℝ)).of_le le_top),iteratedFDeriv_const_smul_apply (hL.of_le le_top)]
      simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply, smul_eq_mul]; rw [pay_second hc hs.path,pay_second hd hs.path,show K 0=0 from hs.zero,hg,hi, _root_.zero_apply,zero_add,zero_add]
      have hu x :(u x).2=fderiv ℝ K 0 x:=by
          let A:= ContinuousLinearMap.snd ℝ C P; have hp:fderiv ℝ K 0=A∘L fderiv ℝ (viewS K) 0 := by rw [show fderiv ℝ K 0=fderiv ℝ (A ∘ viewS K) 0 from rfl,fderiv_comp _ A.differentiableAt (hs.hl.differentiableAt (by simp)),A.fderiv]
          exact (DFunLike.congr_fun hp x).symm
      rw [show iteratedFDeriv ℝ 2 L 0 ![x,y]= _ from trace_log hv _ _ (he.symm ▸ hm),he,hb.1,hb.2,(advert m hs y y).1,mul_add,trace_add,hu x,hu y]; rfl -- maybe mul Add _root_
end Virgin
end YM.OPE.Flume
