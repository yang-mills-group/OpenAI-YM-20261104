import YM.RG11Scheme.Bell.Over
import YM.RG11Scheme.Stencil.Mine

/-! The top signal. A radial top input is exactly recovered; not claimed for general off-shell representative. Signed stencils sampling displaced/negative link endpoints included. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace YM.RG11Scheme.Bell
open Function Filter Set Lattice Mesh Stencil Stencil.Point Stencil.Shot Stencil.Cell Maxwell Tensor Pert Align
open Pert.Bare
open scoped BigOperators Classical Topology ContDiff
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]{G:Gauge} {A:Bond G} {d:ℕ}
local notation "α" => Bond G

def findout (A:link→E)(i:Axis)(x:Cover):= A (x,i)
omit [NormedSpace ℝ E] [CompleteSpace E] in
lemma vector_step (U:link→E)(x:Cover)(i j) : Stencil.curl U x i j = go [i] (findout U j) x-go [j] (findout U i) x := by unfold Stencil.curl; simp only [onwards,starting, findout]; abel
-- Finite read
lemma gem (A:α)(x:Cover)(γ:Fin d→Axis)(i j) : wideCore G d x A i j γ=(d.factorial:ℝ)⁻¹ • go (List.ofFn γ) (fun y=>Stencil.curl A y i j) x := by
   let u:Align.Atom d:= ⟨1,γ,i,j⟩
   have hs (i j:Axis)(U:α) : (Align.Atom.mk 1 γ i j).readK U 0 = go (List.ofFn γ ++ [i]) (findout U j) 0 := by
     let a:=Align.Atom.mk 1 γ i j
     have X : a.factor=1:=by simp [Atom.factor,a,Atom.tally]
     have Y:a.foot true=0:= by simp [Atom.foot, Atom.coverMul,a, Atom.tally,Atom.down,Atom.axisRate]
     have Z:a.dirs=List.ofFn γ++[i]:=by simp [Atom.dirs,a]
     change a.readK U 0= _; rw [Point.tuned,X,Y,Z,one_smul]; exact rfl
   have hk (U:α): wideCore G d 0 U i j γ=(d.factorial:ℝ)⁻¹ • go (List.ofFn γ) (fun y=>Stencil.curl U y i j) 0 := by
      have hv : wideLink G 1 U=U:=by funext l; simp [wideLink,posDir,Lattice.Step.rotate,Lattice.Step.used,affine]
      have ht:= Atom.core_combine u U (0:Cover)
      change wideCore G d (affine (1:Signed)⁻¹ 0 0) (wideLink G 1 U) _ _ _=_ at ht
      rw [hv,show affine (1:Signed)⁻¹ 0 (0:Cover)=0 by simp [affine]] at ht
      apply ht.trans
      congr 1
      change (Align.Atom.mk 1 γ i j).readK U 0-(Align.Atom.mk 1 γ j i).readK U 0 = _
      rw [hs,hs,go_concat,go_concat]
      simp_rw [vector_step U]
      change ladder _ _ _-ladder _ _ _=ladder _ _ _; rw [← Pi.sub_apply,← map_sub]; exact rfl
   suffices he: wideCore G d x A=wideCore G d 0 (pan x A) by
     rw [he,hk]; congr 1; rw [show (fun y=>Stencil.curl (pan x A) y i j)=(fun y=> Stencil.curl A (y+x) i j) by funext; simp only [Stencil.curl,Cell.pan]; rw [add_right_comm _ _ x,add_right_comm _ (step _) x]]
     simpa only [zero_add] using shifted (List.ofFn γ) (fun y=>Stencil.curl A y i j) x 0
   funext f l r; simp_rw [wideCore_apply,zero_add]; congr 1; apply Finset.sum_congr rfl; intro s _
   unfold wideCurl Cell.pan
   rw [add_comm x]; rw [add_right_comm _ (step f), add_right_comm _ (step l)]
lemma gleam {i j:Axis}(U:α) (T: Tensor.T E4 G.Color d)(h:Says (fun x=>Stencil.curl U x i j) T)(x:Cover)(γ:Fin d→Axis): wideCore G d x U i j γ=T (basis ∘ γ) := by
   rw [gem,shuffle _ _ _ (List.reverse_perm (List.ofFn γ)).symm,h.atlas (List.ofFn γ).reverse (by simp) x,deliver T h.sym,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
lemma gem_dark (U:α)(h:∀ i, findout U i∈hill G.Color d)(x:Cover): wideCore G d x U=0:=by
   funext i j γ
   rw [gem, show (fun x=>Stencil.curl _ x i j)= _ from funext fun y=> vector_step U y i j]; let D:=List.ofFn γ
   have he:go D ((go [i] (findout U j))-(go [j] (findout U i)))=0:=by
     change ladder D (_-_)=_; rw [map_sub]; change go D _ - go D _=0
     rw [← show go (D++[i]) _ = _ from funext (fun x=>go_concat (findout U j) x D [i]),← show go (D++[j]) _ = _ from funext (fun x=>go_concat (findout U i) x D [j]),h j _ (by simp [D]),h i _ (by simp [D]),sub_zero]
   change _ • go D (go [i] (findout U j)-go [j] (findout U i)) x=(_ : G.Color); rw [he, Pi.zero_apply,smul_zero];exact rfl

def brighten (P : Labels.Taylor G d) : α := fun l=>P.value l.2 (row l.1)
lemma signal_curl (P : Labels.Taylor G d)(i j) : Says (fun x=>Stencil.curl (brighten P) x i j) (Maxwell.takeCurl P i j):= by
   have he i:Says (findout (brighten P) i) (P.val i):=own (P.property.1 i)
   have hm:= ((he j).different i).minus ((he i).different j)
   simp_rw [vector_step]; rw [takeCurl,smul_sub];exact hm
lemma capital (P : Labels.Taylor G d)(x:Cover) : radialMap (wideCore G d x (brighten P))=P := by
   rw [show wideCore G d x (brighten P) = Bare.components P from funext fun i=> funext fun j=> funext (fun r=> gleam _ _ (signal_curl P i j) _ r)]; exact Bare.complete P
end YM.RG11Scheme.Bell
