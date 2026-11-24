import YM.OPE.Compatible.Lintel.Beat
/-!
# Quantitative hand sensitivity, exact representative in hull
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{n m c f:Side}{S:StepData c f}{p q:Clip}{R T:PathData G} {P:Patch}{K:KernelChoices}{V:ChartRatio G} {i j t r:ℕ} {s s' u α T₁ T₂ b b' d U ℓ:ℝ}
namespace Script
open Page Virgin
lemma polar_caps [NormedAddCommGroup I][NormedSpace ℝ I](B:Tensor.T I ℝ 2)(a b:I)(h:Tensor.Sym B):B ![a+b,a+b]- B ![a,a]-B ![b,b]=2*B ![a,b]:=by
    let T:= B.curryLeft; let R (v:I):= (T v).curryLeft; have ht(x y z:I): B ![x+y,z]=B ![x,z]+B ![y,z]:=by change T (x+y) ![z]=_;rw [map_add]; rfl
    have he (x y:I): B ![x,y]=B ![y,x] := by rw [show ![x,y]=![y,x] ∘ Equiv.swap (0:Fin 2) 1 from funext fun i=>by fin_cases i<;>rfl]; exact h ..
    calc
       _ = B ![a+b,a]+B ![a+b,b]-_-_:= congr_arg (fun i:ℝ=>i-B ![a,a]-B ![b,b]) (by rw [ht a b (a+b)]; exact congr_arg₂ _ (he ..) (he ..))
       _= _:=by rw [ht,ht,he b]; ring
lemma folkst (p:Script I r)(h:folk p):folk (stitch p):=fun i=> ⟨_, silt_cost (adjusted (h i).choose_spec) ⟩
lemma rescaleInk (R:PathData G)(p:Clip)(u:ℝ):expose (draftY p R u)= u • inkV R p 2 + leafV R 2:=by unfold draftY inkV leafV expose; rw [smul_add,smul_comm]
variable (S)(hr:Odd S.ratio.count.val) (X:Boxes G S.patch S.kernel)
local notation "F"=>forest S.ratio hr
lemma tug (t:S.Choices){g:Bid.Dir G c→AxisChart G F}{L:Matrix (Body 1 f) (Body 1 c) ℝ}{B: Bed}(h:licensed S hr X p R L B g)(he:R.Bounds p s u b)(hq:T.Bounds q s' U d)(hp: LocalRatio V)(hx:FiniteBound F R T p q α V g T₁ T₂ b'){K:ℝ}(hk:0≤K)(hh:∀ i x,(i.val:ℝ)*‖X.silo R p V i x-library i (X.talo R p V) x‖≤ K*∏ j,‖x j‖)(z w: Tab (Shade G) c):
   ‖library c (stitch (X.talo R p V)) ![deltaH z,deltaH w] - library c (expose (draftY q T α)) ![deltaH z,deltaH w]‖ ≤ (12*K/(c.val:ℝ))+(c.val:ℝ)^4 * T₁*b'*Real.exp (-T₂*c.val) :=by
      let P:= X.talo R p V; let S':=stitch P; let A:=thermal F t p R g V; let Q:=draft (c:=c) α T q; let C:=(spool G c).symm; let L:= iteratedFDeriv ℝ 2 A 0; let M:= L.compContinuousLinearMap (fun _=> C.toContinuousLinearMap); let x:=deltaH z; let y:=deltaH w; let T':=listV S' c; have heH:folk P:= folkT X.rocket2 (X.folk_crown he); have hS:Summable S':=folk_whole (folkst P heH); have hr(v u:deck (Shade G) c):M ![v,u]=L ![C v,C u]:= congr_arg L (a₂:=![C v,C u]) (a₁:=fun i: Fin 2=> C (![v,u] i)) (funext fun i=>by fin_cases i<;>rfl); let D:= T'-M; have hD(v): D v=T' v-M v:=rfl
      have hl(w): ‖deltaH (I:=Shade G) (N:=c) w‖ ≤ 1:= (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i=>by by_cases H:w=i; simp [deltaH,H]; simp [deltaH,Ne.symm H])
      let c':ℝ:= c.val; have hc:0<c':= Nat.cast_pos.mpr c.pos; let d':=12*K/c'; have hd:0 ≤ d':=div_nonneg (by positivity) hc.le
      have hv(z: deck (Shade G) c)(hy:‖z‖ ≤2): ‖D ![z,z]‖≤4*K/c' := by
         have hh:= hh c ![z,z]; apply (le_div_iff₀ hc).mpr; rw [mul_comm]; rw [hD,hr,show T' ![z,z]= _ from muses _ hS _, norm_sub_rev]; change _ * ‖iteratedFDeriv ℝ 2 A 0 ![C z,C z]-library c S' _‖≤ _; have he := hearing S _ X t h he hp hx (C z)
         rw [show library c S' ![z,z]=narrate c P z from (show library c S' ![z,z]=narrate c S' z from congr_arg _ (funext fun i=>by fin_cases i <;> rfl)).trans (regaled P (folk_whole heH) z), he]; simp_rw [show (spool G c) (C z)=z from (spool G c).apply_symm_apply z]
         rw [show narrate c P z= library c P ![z,z] from congr_arg (library c P) (funext fun i=>by fin_cases i <;> rfl)]; apply hh.trans; rw [Fin.prod_univ_two]; change K*(‖z‖ * ‖z‖) ≤ _; calc
            _≤ K*(2*2):=mul_le_mul_of_nonneg_left (mul_le_mul hy hy (norm_nonneg _) (by norm_num)) hk
            _ =_:= by ring
      have hg:= polar_caps D x y fun v i=> congr_arg₂ (·-·) (pointed (stampV P (folk_whole heH)) hS c v i) (Analysis.sym_Jet ((hx.born t).of_le le_top) (C∘v) i)
      have hb₁ := (hl z).trans (one_le_two);have hb₂ :=(hl w).trans one_le_two; have hz: ‖x+y‖≤ 2 := (norm_add_le ..).trans (by linarith [hl z,hl w])
      have HF: ‖D ![x,y]‖ ≤ d':=by apply le_trans (b:=(2:ℝ)* ‖D ![x,y]‖) (by linarith [norm_nonneg (D ![x,y])]); rw [← show ‖2*D ![x,y]‖=2*‖D ![x,y]‖ by rw [norm_mul];norm_num,← hg]; apply (norm_sub_le ..).trans ((add_le_add ((norm_sub_le ..).trans (add_le_add (hv _ hz) (hv _ hb₁))) (hv _ hb₂)).trans_eq (by unfold d'; ring))
      let u:= C x; let v:= C y; have hk := wield S _ hx t z w; change ‖(library c S' ![x,y])- _‖ ≤ d'+ _
      have h1:library c (expose (draftY q T α)) ![x,y]=iteratedFDeriv ℝ 2 Q 0 ![u,v]:=by
          refine (congr_arg (library c _) (a₂:= spool G c ∘ ![u,v]) (funext fun i=>?_)).trans (soothe _ _ _ (draftTal T q c α hq) ![u,v]); fin_cases i <;> exact ((spool G c).apply_symm_apply _).symm
      rw [h1,show library c S' ![x,y]- _= D ![x,y]+(iteratedFDeriv ℝ 2 A 0-iteratedFDeriv ℝ 2 Q 0) ![u,v] from ?_]; exact (norm_add_le ..).trans (add_le_add HF hk)
      rw [hD,hr,_root_.sub_apply]; unfold u v L T'; rw [muses _ hS]; ring
end Script
end YM.OPE.Flume
