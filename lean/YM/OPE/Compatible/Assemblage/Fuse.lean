import YM.OPE.Compatible.Assemblage.Eroded
/-!
# Step with a remount

Set the new seats in the closing-block estimates, execution retains
*all* required stencils through their requested steps before the
new census, on overlapping alternatives via the Guard. The event
spends an explicit grouping cost per affected slot including survivors.
Used finitely often, not scheduled again at every block.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem Mirror
open scoped Topology BigOperators Classical
variable {V I J W : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J][Fintype W][DecidableEq W]{G:Gauge}{n n':Side}
   {A:History G}{N p i:ℕ}{D: GaugeDoor (A.rep N p (i+1)) (A.rep N p i)}
   {e t:ℝ}{u d:ℕ→ℝ}{b:ℕ→ℕ}{P:Ensemble V}
   {X:I→ Stem V G (A.S.side (i+1) p)}{X':I→Stem V G (A.S.side i p)}{r:I→ℝ}{C:I→ℂ}
   {E:V→ Site (A.S.side i p)}{Y: Config G (A.S.side (i+1) p)→ Poly (Names V I)}
variable (L:Fibers (I⊕W) J)
-- discard the artificial slots when interpreting the word.
def assembly (s:(Names V J).Mode) : (Names V I).Mode := invM (inlets V I W) ((partialGroup V L).plena s)
def reunion : Words (V×I)→L[ℂ] Words (V×J) :=
    LinearMap.toContinuousLinearMap ({ toFun v:= Poly.inject (fun i=> v.part (assembly L i)), map_add':=fun _ _=>by ext; rfl, map_smul':=fun _ _=>by ext; rfl } : Words _ →ₗ[ℂ] Words _)
lemma reap_meets (p: Words (V×I)): (partialGroup V L).reap (Mirror.pad (inlets V I W) p)=reunion L p:=by ext; rfl
lemma out_live {Y:Config G n→Words (V×I)} (h:Integrable Y (prior G n)):Integrable (reunion L ∘ Y) (prior G n):=((reunion L).restrictScalars ℝ).integrable_comp h
lemma consumes {Y:Config G n→Words (V×I)}(O:StepData n' n){t:ℝ}(ho:O.IsKernel t G)(hy:Integrable Y (prior G n)): reunion L ∘ O.push t Y=O.push t (reunion L ∘ Y):=by
   funext U; let Z:=(reunion (V:=V) L).restrictScalars ℝ; change Z (O.push t Y U)= _
   unfold StepData.push; have he := Z.integral_comp_comm (StepData.push_slice ho U _ hy); simp_rw [ContinuousLinearMap.map_smul] at he; exact he.symm
set_option maxHeartbeats 200000 in
lemma formation (Z:W→ V→ Site (A.S.side i p)) (H l:ℕ)(χ:Guard (Names V I))(χ':Guard (Names V J))
   (hY:Owned χ (A.rep N p (i+1)) (fun v=>(A.levels.clock.op i p).ratio.embed (E v)) P X r e Y)
   (h:Admits D b (d i) t (u i))(hA:A.Selected)(hn:i<N)(ho:Arsenal (A.rep N p i))(ht:ClusterPars A d u b i)
   (hI: Integrable Y (prior G _))(he: (A.levels.budget (i+1)).supportExponent-4≤e)(hp:∀ j,Marked (A.rep N p i) E P (X' j))(hf:∀ j,Journey D (A.levels.clock.op i p) P (X j) (X' j) (r j) (C j))
   (hV:Occupancy (tags X) (b i))(hV':Occupancy (tags X') (b i))(h_V:Occupancy (tags (placeOn X' Z)) (b i))
   (hω:∀ j v, v≠P.v→Z j v= affine (P.move v).1 (E v) (Z j P.v))(hQ:∀ j:V×(I⊕W),
      coverNumber (A.levels.budget i).B ({tags (placeOn X' Z) (j.1,L.twig (L.bunch j.2)), tags (placeOn X' Z) j}:Support (A.S.side i p)) ≤ l)
   (hH:0<H) (h_card:Fintype.card (I⊕W)≤H)(hC:∀ j,χ'.safe j→χ.safe (assembly L j)) :
    let T:=placeOn X' Z
    let W':= grouped A d H l i (Sum.elim r 1) L
    ∃ U:J→Stem V G (A.S.side i p), (∀ j,(U j).home=(T (L.twig j)).home) ∧
       Owned χ' (A.rep N p i) E P U W' ((A.levels.budget i).supportExponent-3) (reunion L∘ (A.levels.clock.op i p).push (A.rep N p (i+1)).beta Y) ∧
       (∀ j,L.SingleFiber j → U j= T (L.twig j)) ∧ ∀ j,¬ L.SingleFiber j → Blade (A.rep N p i) ((U j).home P.v) ((U j).oil P.v) (profile (A.rep N p i).activities ((U j).gas P.v)) 0 (4*(1/W' j)):=by
   obtain ⟨Y',hy,hx,hw⟩:= hY.issues
   intro T W'; let R:= A.rep N p i; let K:= A.rep N p (i+1); let O:= A.levels.clock.op i p
   obtain ⟨ha,hL⟩:= spring_step P hw hy hA hn h he hp hf hV hV'
   let s':= Sum.elim r (1:W→ℝ)
   obtain ⟨ha',hL'⟩:= pad_fire P Z (fun _:W=>d i) ha (h.staff.hats.1.le) (hA.represents N p i hn.le|>.good.labels) hL
   rw [show Sum.elim (dropFunds (d i) r) (fun _:W=> d i)=dropFunds (d i) s' from funext (fun j=> by cases j; rfl; change _=_*(1:ℝ); exact (mul_one _).symm)] at ha'
   obtain ⟨U,hM,hh,hxT,hz⟩:= eroded L H l ha' ht h.staff hA hn.le ho h_card hH h_V (registered P Z hp hω) hQ hL' (fun j=>by cases j; exact hw.way _; exact zero_lt_one) (fun j=> by cases j; exact hf _ |>.carries; change 1*‖(1:ℂ)‖≤1; norm_num)
   refine ⟨U,hM,?_ ,hxT,hz⟩
   have hO : O.IsKernel K.beta G:= A.levels.transition_mass ..; let Q:= O.push K.beta Y; let V0:= O.push K.beta Y'; let f:= reunion L∘ V0; have hF:= χ.brought hx hI hy hO
   refine ⟨f,out_live L (StepData.push_integrable hO _ hy), fun U s hp=>?_,?_⟩
   · exact hF U (assembly L s) (hC s hp)
   rw [show f=fun x=>(partialGroup V L).reap (Mirror.pad (inlets V I W) (V0 x)) from funext fun i=> (reap_meets ..).symm]; exact hh
end YM.MergeProof.Ribbons.ManyCopies
