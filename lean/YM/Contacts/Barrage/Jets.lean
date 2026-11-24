import YM.Contacts.Barrage.Spout
set_option linter.unusedSectionVars false
namespace YM.Contacts.Barrage
open Function Set Finset Filter RG Wilson Lattice Precision Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix
open Milling.Garf Form House PertExtension.Series
open scoped Topology BigOperators MeasureTheory Matrix Classical NNReal ContDiff
noncomputable section
variable {X Y α β ι κ:Type}{s t:ℝ≥0}{b C:ℝ}{k n:ℕ}{m:Side}
-- local stencil nonlinear log-jet, finite pattern weight
variable [Fintype ι][Fintype α][Fintype β]
structure Pattern (ι α β:Type) [Fintype ι] where
  form : β→ι→ Node α
  image : β→ (ι→ℝ) →ℝ
  fired i : AnalyticAt ℝ (image i) 0
  zero i : image i 0 =0
namespace Pattern
variable (F:Pattern ι α β)
def stencil (m:Side)(x:House.Dir (Co m α)) (j:Co m β):= F.image j.2 (load (F.form j.2) j.1 x)
@[simp] lemma zero_stencil : F.stencil m 0=0:= by funext i; simp [stencil,F.zero]
lemma analytic : AnalyticAt ℝ (F.stencil m) 0 := by
   apply ContDiffAt.analyticAt (contDiffAt_pi.mpr (fun i =>?_)); refine (F.fired i.2).contDiffAt.comp (f:=load (F.form i.2) (m:=m) i.1) _ (by fun_prop)
def tap (i:ι): Row β α:= fun b a z=> if (z,a)=F.form b i then 1 else 0
lemma tap_short (s:ℝ≥0): ∃ B≥(0:ℝ),∀ t:ℝ≥0,t≤s → ∀ i,(F.tap i).strip t B := by
   let f (b: ι×β):= Real.exp (s*size (F.form b.2 b.1).1); let B:=∑ i:ι×β,f i; have ht (i:ι×β) : 0≤ f i:=by unfold f; positivity
   refine ⟨B,sum_nonneg fun i _=>ht i,fun t h i a b=>?_⟩
   let z:= (F.form a i).1; refine budget_of_sum (fun j=>by positivity) fun Z=>?_ ; by_cases h': (F.form a i).2=b
   · have H v (hv : v≠z): tap F i a b v=0:= if_neg (fun h=> hv (congr_arg Prod.fst h)); refine le_trans (b:= f (i,a)) ?_ (single_le_sum (f:=f) (fun _ _=> ht _) (mem_univ _)); by_cases hx:z∈Z
     · rw [Finset.sum_eq_single_of_mem z hx, show tap F i a b z=1 from if_pos (show (z,b)=_ from Prod.ext (show z= (F.form a i).1 from rfl) h'.symm), norm_one,mul_one]; unfold f; gcongr
       intro i _ hh; rw [H i hh,norm_zero,mul_zero]
     rw [Finset.sum_eq_zero (fun i hi=>by rw [H i (fun e=>hx (e ▸ hi)),norm_zero,mul_zero])]; exact ht (i,a)
   rw [Finset.sum_eq_zero (fun x _=>by rw [show tap F i a b x=0 from if_neg (fun h=>h' (congr_arg Prod.snd h).symm),norm_zero,mul_zero])]; exact sum_nonneg fun i _=> ht i
lemma tap_read (m:Side)(i:ι)(x:Co m β)(z:Co m α): (F.tap i).acts m x z=if z=road (F.form x.2 i) x.1 then 1 else 0:= by
   unfold Row.acts; rw [Matrix.of_apply,tsum_eq_single (b:=(F.form x.2 i).1)]; · simp_rw [Prod.ext_iff,tap, Prod.ext_iff,road,add_comm (x.1)]; split_ifs <;> first| rfl | tauto
   intro q hq; simp [tap, Prod.ext_iff,hq]
lemma tap_extract (x:House.Dir (Co m α))(i:ι)(z:Co m β): ((F.tap i).acts m*ᵥ x) z=load (F.form z.2) z.1 x i:= by simp only [Matrix.mulVec,dotProduct,tap_read,ite_mul,one_mul,zero_mul]; rw [Finset.sum_ite_eq']; simp; rfl
-- Faa loops. keep each fractional factor allocated only at reading
variable (p:OrderedFinpartition n)
abbrev Graph (p:OrderedFinpartition n) := ((i: Fin p.length) × Fin (p.partSize i))
abbrev Pad:= (i:Fin p.length)→Fin (p.partSize i)→ι
private lemma spout : Surjective (Sigma.fst : Graph p → Fin p.length):= fun i=> ⟨⟨i,⟨0,p.partSize_pos i⟩⟩,rfl⟩
def patron (u: Pad (ι:=ι) p) : Field (Fin p.length) β:= fun x=> ∏ i, words (F.image (x i)) (p.partSize i) (u i) * ((p.partSize i).factorial:ℝ)
variable (z:Field (Fin p.length) (Node β))
def layer (R:κ→Row β α) (Z:Field κ (Node β))[Fintype κ]:=allAt (fun i=> plane (R i)) Z
def sparkPlug (u: Pad (ι:=ι) p) (j:Graph p):= F.tap (u j.1 j.2)
def diagonalize (X:Type)(u: Pad (ι:=ι) p)(Z:Field (Fin p.length) (X×β)): Field (Graph p) (X×β):= fans Sigma.fst (faceCost X (patron F p u) Z)
def blend (z:Field (Fin p.length) (Node β)):Field (Fin n) (Node α):= printRun (∑ u, reorder p.equivSigma (layer (F.sparkPlug p u) (F.diagonalize p Cover u z)))
def folded (H:Field (Fin p.length) (Co m β)):Field (Fin n) (Co m α):= printRun (∑ u,reorder p.equivSigma (allAt (fun i:Graph p=>(F.sparkPlug p u i).acts m) (F.diagonalize p (Site m) u H)))
def sparksFee (F:Pattern ι α β)(s:ℝ≥0):ℝ:= (F.tap_short s).choose
lemma plumes (ht:t≤s) (u: Pad (ι:=ι) p) (v:Graph p) : Weirs (tunnel t) (plane (F.sparkPlug p u v)) ((Fintype.card β:ℝ)*F.sparksFee s) ((Fintype.card α:ℝ)*F.sparksFee s) := flight_stem ((F.tap_short s).choose_spec.2 t ht _) (F.tap_short s|>.choose_spec.1)
def shelfFee (s:ℝ≥0)(u:Pad (ι:=ι) p) := ((Fintype.card β:ℝ)*F.sparksFee s)*(∑ i:Fin p.length → β, ‖F.patron p u i‖)*(Fintype.card α*F.sparksFee s)^(Fintype.card (Graph p) -1)
variable {z}
lemma blend_root (u : Pad (ι:=ι) p)(ht:t≤s)(h:Rooted (terrain t _) z b): Rooted (terrain t _) (layer (F.sparkPlug p u) (F.diagonalize p Cover u z)) (shelfFee F p s u * b) := by
   let hW:=F.plumes p ht u; let H:= fans_root Sigma.fst (spout p) (faceCost_root h (F.patron p u)); let d:ℝ:= ∑ i:Fin p.length→β,‖F.patron p u i‖; let f:=sparksFee F s; let x:ℝ:=Fintype.card β*f; let y:ℝ:=Fintype.card α*f; let c:= Fintype.card (Graph p)-1
   have hy:0≤f:= (F.tap_short s).choose_spec.1; have hp:= h.cash; refine all_root H fareFoot hW ?_ ?_; · intro i; apply le_of_eq; calc
                  _= x*(d*b)* y^c := by dsimp only [x,d,y,c,f]; simp; left; left; left; congr!
                  _=_ := by dsimp only [x,d,y,f,c,shelfFee]; simp [mul_comm,mul_left_comm,mul_assoc]
   unfold shelfFee; have ht:Fintype.card β * F.sparksFee s≥0:= by change x ≥ 0; unfold x; positivity
   have hc:sparksFee F s ≥0:= by exact hy
   positivity
lemma blend_price (ht:t≤s)(h:Rooted (terrain t _) z b): Rooted (terrain t _) (F.blend p z) ((∑ u,F.shelfFee p s u) * b):= by rw [sum_mul]; exact (Rooted.aggregate Finset.univ fun u _=> (F.blend_root p u ht h).renew _).even
lemma peri [Fintype κ](e:κ ≃ Fin n) (G: κ → X→ Y→ ℝ)(Z:Field κ X): reorder e (allAt G Z)=allAt (G∘e.symm) (reorder e Z):= by
   funext t; unfold allAt reorder; dsimp only; rw [← Equiv.tsum_eq (Equiv.arrowCongr e.symm (Equiv.refl X))]; apply tsum_congr; intro i; simp only [Function.comp_apply]; rw [← Equiv.prod_comp e (fun j=> G (e.symm j) (i j) (t j))]; simp; left; rfl
lemma blend_shadow [NeZero n] {g:Field (Fin p.length) (Co m β)} (h: Rooted (terrain s _) z b)(he: Shadow (lower m) z g): Shadow (lower m) (F.blend p z) (F.folded p g):= by
   unfold blend folded; let f (u: Pad (ι:=ι) p):=F.blend_root p u le_rfl h
   letI:Nonempty (Graph p) := Nonempty.map p.equivSigma.symm inferInstance; refine (Shadow.aggregate _ Finset.univ (fun i _=>(f i).renew _) (fun i _ =>?_)).even (Rooted.aggregate Finset.univ fun i _ => (f i).renew _)
   unfold layer; rw [peri p.equivSigma,peri p.equivSigma]; cases n; exact not_isEmpty_iff.mpr (inferInstance:Nonempty (Fin 0)) (inferInstance:IsEmpty (Fin 0)) |>.elim; refine Pulse.basin ?_ (fun j=> row_ship _ m) ((fans_root _ (spout p) (faceCost_root h _)).renew p.equivSigma) fareFoot (fun j=> F.plumes p le_rfl i (p.equivSigma.symm j)); exact (fans_shadow _ (spout p) (faceCost_shadow (F.patron p i) he)).replace (e:=p.equivSigma.symm)
section read
lemma stem_read [Fintype X][Fintype Y][Fintype κ] (Z:Field κ X)(W:κ→Matrix X Y ℝ)(x:Y→ℝ): design (allAt W Z) x= ∑ v:κ→X,Z v*∏ i:κ, (W i *ᵥ x) (v i):= by
   rw [design_spec]; simp only [allAt,tsum_fintype,Matrix.mulVec,dotProduct,Fintype.prod_sum,Finset.sum_mul,Finset.mul_sum]; rw [sum_comm]; apply sum_congr ?_; swap; · congr!
   intro j _; apply sum_congr ?_; swap; · congr!
   intro i _; rw [prod_mul_distrib,mul_assoc]
variable (g:Field (Fin p.length) (Co m β))(x:House.Dir (Co m α))
lemma folded_read : design (F.folded p g) x=∑ w: Fin p.length→ Co m β, g w*∏ i,iteratedFDeriv ℝ (p.partSize i) (F.stencil m) 0 (fun _=>x) ((w i)):= by
   unfold folded design; rw [verse_print,verse_sum,map_sum]; simp_rw [verse_renew]; change (∑ i,design (allAt (fun j:Graph p=>(F.sparkPlug p i j).acts m) (F.diagonalize p (Site m) i g)) x)=_
   simp_rw [stem_read,sparkPlug, tap_extract]; let V:=F.form; let Y (w: Fin p.length→ Co m β) (i:Fin p.length):= load (V (w i).2) (w i).1 x; let K (w:Fin p.length→Co m β)(i:Fin p.length)(v:Fin (p.partSize i) → ι):ℝ:= words (F.image (w i).2) _ v * ∏ a,Y w i (v a)
   have hw (w:Fin p.length→Co m β)(i:Fin p.length): iteratedFDeriv ℝ (p.partSize i) (F.stencil m) 0 (fun _=>x) (w i) = ∑ v, (p.partSize i).factorial*K w i v:= by
      let k:=p.partSize i; let f:=F.image (w i).2; let y:=Y w i; let z:= w i; rw [← mul_sum,show (∑ v,K w i v)= _ from (show _= design (words f k) y from by rw [design_spec]; congr!), Garf.hash]; have he:= F.fired z.2; let X:= load (V z.2) z.1; have ht:= Garf.woven he X x k; have hv:= ((ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Co m β=>ℝ) z).iteratedFDeriv_comp_left (F.analytic.contDiffAt (n:=ω)) (i:=k) le_top);
      have hz:= congr_arg (fun (c:ℝ)=> (k.factorial:ℝ)*c) ht; unfold Radial.jet at hz ⊢; change (iteratedFDeriv ℝ k (F.stencil m) 0 _) z = _; rw [← hz]; field_simp; exact (DFunLike.congr_fun hv (fun _=>x)).symm
  
   simp_rw [hw,Fintype.prod_sum,mul_sum]; conv_rhs=> rw [sum_comm]
   apply sum_congr ?_; swap; · congr!
   intro u _ ; unfold diagonalize; rw [fans_sum (p:= (Sigma.fst:Graph p→_)) (spout p)]; apply sum_congr ?_; swap; · congr!
   intro w _; unfold faceCost patron K;
   simp_rw [prod_mul_distrib]; rw [Fintype.prod_sigma]; unfold Y V; simp only [Function.comp_apply]; ring
open Radial
lemma germ_read (s: House.Dir (Co m β)→ℝ) (hh:AnalyticAt ℝ s 0) (hq:Poem g)(h : ∀ x, jet s p.length x = design g x) : ((p.length.factorial):ℝ) * design (F.folded p g) x = iteratedFDeriv ℝ p.length s 0 (fun i=>iteratedFDeriv ℝ (p.partSize i) (F.stencil m) 0 (fun _=>x)):= by
   let v:= fun i:Fin p.length=>iteratedFDeriv ℝ (p.partSize i) (F.stencil m) 0 (fun _=>x); rw [folded_read]; have he:= Lumen.recital_exact s g hq hh h; have hx := DFunLike.congr_fun he v; change ((p.length.factorial:ℝ)⁻¹)*(iteratedFDeriv ℝ p.length s 0 v)=recording g v at hx; rw [recording_apply] at hx; apply Eq.symm; rw [show _= _ from (mul_inv_cancel_left₀ (show (p.length.factorial:ℝ) ≠0 by positivity) (iteratedFDeriv ℝ p.length s 0 v)).symm]; rw [hx]; apply congr_arg; apply sum_congr ?_; swap; · congr!
   intro i _; rw [mul_comm]
lemma atom_form (x:House.Dir (Co m α)) (g:Field (Fin n) (Co m β)): design (F.folded (OrderedFinpartition.atomic n) g) x=design g (fderiv ℝ (F.stencil m) 0 x):= by
   rw [folded_read,design_spec]; apply sum_congr ?_; swap; · congr!
   intro i _; congr! 1; apply prod_congr rfl; intro z _; change (iteratedFDeriv ℝ 1 (F.stencil m) 0 (fun _=>x)) _ = _; rw [iteratedFDeriv_one_apply]
lemma metro (s:House.Dir (Co m β)→ℝ)(x:House.Dir (Co m α))(G:Rack (Co m β))(hA:AnalyticAt ℝ s 0)(hk:∀ i:ℕ,i≤n→Poem (G i))(hh:∀ i:ℕ,i≤ n→∀ y,jet s i y=design (G i) y) : jet (s ∘ F.stencil m) n x = (n.factorial:ℝ)⁻¹ * (∑ v:OrderedFinpartition n, (v.length.factorial:ℝ)*design (F.folded v (G v.length)) x):= by
   unfold jet; apply congr_arg; have hv : AnalyticAt ℝ s (F.stencil m 0):= by rw [F.zero_stencil]; exact hA
   rw [iteratedFDeriv_comp hv.contDiffAt F.analytic.contDiffAt (show (↑n:WithTop ℕ∞)≤ω from le_top), FormalMultilinearSeries.taylorComp,_root_.sum_apply]; apply sum_congr rfl; intro i _; rw [F.germ_read i _ x s hA (hk _ i.length_le) (hh _ i.length_le)]; simp only [
    OrderedFinpartition.applyOrderedFinpartition_apply,FormalMultilinearSeries.compAlongOrderedFinpartition_apply,F.zero_stencil]; rfl
end read
end Pattern
end
end YM.Contacts.Barrage
