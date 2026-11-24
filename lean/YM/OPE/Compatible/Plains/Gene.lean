import YM.OPE.Compatible.Plains.Leg
/-! # Store congruent power collections -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Prairies
open Function MeasureTheory Set Topology Filter Lattice Laurent Wilson Exterior Cascade PertExtension Series Score Next.Foundations Matrix
open Next.Free Frequency Bloch MSbar.Tree MSbar.Tree.Resolvent Terp Stubble Weir
open GaussianScore Libra WithLp RG Precision Votive Glass Radial Flume Flume.Script Flock StageLight Balsam Nestle Maxwell YM.Pert.Bare
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {n:Side}{G:Gauge}{C:RG.KernelChoices}{P:ChartRatio G}{U:Gloam}{d k j r w e:ℕ}
inductive Saga (G:Gauge)(e k:ℕ) where
| mon {s:ℕ} : ∀ (v: Fin s→ Reed G), (∑ i,(v i).1.heat)=e→ s≤k→ Saga G e k
| empty: Saga G e k
| add: Saga G e k→ Saga G e k→Saga G e k
| sml: ℝ→ Saga G e k→Saga G e k
namespace Saga
def plain : (v: Saga G e k)→ (x:Site n) → Ice G n→ℝ
| mon l _ _,x,Q=> ∏ i, fence (l i) x Q
| empty,_,_=>0
| add Y Z,x,Q=>plain Y x Q+ plain Z x Q
| sml c X,x,Q=>c*plain X x Q
def terra : Saga G e k→ WickPol G
| mon l _ _=> ∏ i,planeLeg (l i)
| empty=>0
| add X Y=>terra X+terra Y
| sml t X=> (t:ℂ) • terra X
lemma ree {I:Type*}(s:Finset I)(V:I→Saga G e k):∃ H:Saga G e k,terra H= ∑ i∈s,terra (V i)∧∀ n:Side,∀ x:Site n,plain H x=∑ i∈s,plain (V i) x:=by
    induction s using Finset.induction with
    | empty=> exact ⟨empty, (Finset.sum_empty).symm,fun _ _=>(Finset.sum_empty).symm⟩
    | insert a s hm ih=> obtain ⟨P,ht,h⟩:=ih; refine ⟨add (V a) P,?_ , fun n x=>?_⟩; simp [terra,ht,Finset.sum_insert hm]; funext i; simp only [Finset.sum_insert hm,plain,h,Pi.add_apply]
end Saga
-- basis decomposition without carrying sums of scalars.
abbrev imprint (G:Gauge)(k:ℕ)(p: Marked G k): Response G k:=fun a b v=>toLp 2 fun s=> if p=(a,b,v,s) then 1 else 0
lemma stampId (A: Response G k): A=∑ i:Marked G k, (θ A i) • imprint G k i:=by
     funext a b v; ext1 t; rw [Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]
     let p:Marked G k:= (a,b,v,t); change chin t _ = chin t (∑ i:Marked G k, θ A i • imprint G k i _ _ _); rw [map_sum,Finset.sum_eq_single p]
     · rw [map_smul]; rw [show (chin t) (imprint G k p a b v)=1 from if_pos rfl,smul_eq_mul,mul_one];rfl
     · intro i _ hb; rw [map_smul]; rw [show (chin t) (imprint G k i a b v)=0 from if_neg hb, smul_zero]
     simp
abbrev life (u:TaylorTower G)(d:ℕ): Alphabet G d:=fun j=>gaugeJet (u j.val)
abbrev shownX (a:Labels.Taylor G k)(t:Fin d)(h:k=t.val):= monoX (G:=G) t (h ▸ a)
open Finset
-- sparse synchronized mon
abbrev Koh (_A:partX G r w d)(x:Site n)(y: Ice G n) : Alphabet G d:=pulp G d (fun b => y (x+Lattice.wrap _ b.1,b.2)) -- unused A.S
open Saga
set_option maxHeartbeats 200000 in
lemma scenery (A:partX G r w d)(k:ℕ)(h:r≤k):∃ V:Saga G (w+r) k,
   (∀ n:Side,∀ x:Site n,∀ y:Ice G n,V.plain x y= A.val (fun _=> pulp G d (fun b => y (x+Lattice.wrap _ b.1,b.2))))∧
   (∀ (u:TaylorTower G),Maxwell.probe u (terra V)=(A.val (fun _=>life u d):ℂ)):=by
    let X(v:Alphabet G d)(t:Fin r→Fin d):ℝ:= A.val (fun j=>monoX (t j) (v (t j)))
    have ha(v:Alphabet G d):A.val (fun _=>v) = ∑ t,X v t:= deckSum ..
    have he(t: Fin r→Fin d):∃ H:Saga G (w+r) k,(∀ n:Side,∀ x:Site n,∀ y:Ice G n,H.plain x y=X (Koh A x y) t) ∧ (∀ u:Maxwell.TaylorTower G, Maxwell.probe u (terra H)=(X (life u d) t : ℂ)):=by
       by_cases he: rankX t=w; swap
       · have hh(v:Alphabet G d):X v t=0:= (show Off G r w d A.val from A.property).Grades t (fun i=>v (t i)) he
         exact ⟨Saga.empty,fun n x y=>(hh _).symm, fun u=>by rw [hh,Complex.ofReal_zero,terra,map_zero]⟩
       let B(j:Fin r):=Marked G (t j).val; letI (j:Fin r): Fintype (B j):=by dsimp only [B];infer_instance
       let g(y:∀ i,B i):Fin r→Reed G:= fun j=> fLead (y j)
       have ht(i):(∑ a,(g i a).1.heat)=w+r:= by
           calc
            _ = ∑ a:Fin r,((t a).val+1+1) := sum_congr rfl fun i _=> pLeg _
            _ = _:= by rw [sum_add_distrib,show w= _ from he.symm]; simp
       let R(j:Fin r):Response G (t j).val→ₗ[ℝ] Alphabet G d:= (LinearMap.single ℝ (fun j:Fin d=>Labels.Taylor G j.val) (t j)) ∘ₗ radialMap
       let CC(i:∀ j,B j):=A.val (fun j=>R j (imprint _ _ (i j))); let W(i: Fin r):= ((((t i).val.factorial):ℝ))⁻¹
       let coeff(j):=(∏ i,W i)* CC j; let f(j):= sml (coeff j) (mon (g j) (ht j) h)
       obtain ⟨P,hP,ht⟩:= ree Finset.univ f
       have hw (Y:∀ j, Response G (t j).val)(v:Alphabet G d)(hx:∀ j, radialMap (Y j)=v (t j)):
          X v t=∑ i: (j:Fin r)→B j,(∏ j, θ (Y j) (i j)) * CC i :=by
             rw [show X v t=A.val (fun j=>R j (Y j)) from congr_arg A.val (funext fun j=>congr_arg (monoX (t j)) (hx j).symm), show (fun j=> R j (Y j))=(fun j=> ∑ i: B j, θ (Y j) i • R j (imprint _ _ i)) from ?_]
             · rw [A.val.map_sum_finset,Fintype.piFinset_univ]; exact sum_congr rfl fun i _=>A.val.map_smul_univ _ (fun j=>R j (imprint _ _ (i j)))
             funext j; simp_rw [← map_smul,← map_sum]; exact congr_arg (R j) (stampId (Y j))
       refine ⟨P,fun n x y=>?_,fun u=>?_⟩
       · rw [ht,Finset.sum_apply]; let v(b: Cover × Shade G):= y (x+Lattice.wrap n b.1,b.2); rw [hw (fun i=>slopeH G (t i).val v) (Koh A x y) (fun i=>rfl)]; refine sum_congr rfl fun i _=>?_ ; change _*CC i*(∏ j, fence _ x y)= (∏ j, θ (slopeH G (t j).val v) (i j))*CC i; simp_rw [show ∀ j:Fin r, θ (slopeH G (t j).val v) (i j)= _ from fun j=> (enroll y x (i j)),prod_mul_distrib]; ring
       let Y(j):= components (gaugeJet (u (t j).val)); rw [hP,map_sum, hw Y (life u d) (fun i=> complete _),Complex.ofReal_sum]; refine sum_congr rfl fun i _=>?_ ; unfold f; rw [terra, map_smul,terra,map_prod]; unfold g; simp_rw [spheric, ← Complex.ofReal_prod]; rw [smul_eq_mul, ← Complex.ofReal_mul]; apply congr_arg; unfold coeff CC W Y; rw [Finset.prod_mul_distrib,prod_inv_distrib]; field_simp
    choose V hV hW using he; obtain ⟨P,ht,hp⟩:= ree Finset.univ V; exact ⟨P,(fun n x y=>by rw [hp,Finset.sum_apply,ha]; simp_rw [hV]),fun u=>by rw [ht,map_sum,ha]; simp_rw [hW]; rw [Complex.ofReal_sum]⟩
end YM.OPE.Prairies
