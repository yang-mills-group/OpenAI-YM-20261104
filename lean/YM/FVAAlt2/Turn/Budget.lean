import YM.FVAAlt2.Turn.Space
/-! $H-acting budget/analytic continuation (4→D tower). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Motions
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum Outlook
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable {G:Gauge}{I E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]{i:ℂ}{m n k:ℕ}
variable (s:Spin (L 0))
local notation "B"=> motion G s
variable {z:UScale I}{a:I→ℝ} {F : I→ Mob G}
local notation "EP"=> Wire (Cfield G m) E (SectorP m)
private lemma rain {a:I→ℝ} (x:EP)(w:EP)(h:fell z a F) : veg z (fun i (y:E)=> ( (flagS (s.arch (Nat.zero_le m)) G).beam (fun l=>F i m (sail x y ++ l))) (sail w y)) a:= by -- variable i type inferred wrong
  induction w generalizing x with
  | nil=> change veg _ (fun i y=> beam _ _ []) _; simp_rw [Pilot.peeps,List.append_nil]; exact h m E x
  | cons i l ih=>
       let V:=flagS (s.arch (Nat.zero_le m)) G; let v:=s.arch (Nat.zero_le m); change veg z (fun j x'=> V.beam _ ((_ ,_) :: sail l x')) a -- projections
       simp_rw [Pilot.met]; refine Costs.sum _ ?_ ?_ -- ambiguous k
       intro j _; let y:= v.turn.toContinuousLinearMap.comp i.2; let f(b:I)(p:E):= V.beam (fun k=>F b m (sail (x++[(j,y)]) p++ k)) (sail l p); let c:= V.fieldC i.1 j
       have hf:= Costs.mul (at_rate (E:=E) (z:=z) (w:=fun _=>c) (a:=(fun _=> (1:ℝ))) (const_sc ..)) (ih (x++[(j,y)])) -- spelling from grep
       simp only [sail_join,sail_cons,sail_nil, List.append_assoc,List.singleton_append,one_mul] at hf; exact hf
       exact fun i _ _=> znon h i
lemma motion_fell (h:fell z a F): fell z a (fun i=>motion G s (F i)) := fun _ _ _ _ _ w=> rain s [] w h
variable {R H:Rack G m} {K: Spin (L m)} {D: Set ℂ}
local notation "ξ"=> flagS K G
set_option quotPrecheck false
local notation "μ"=> (flagS K G).fieldC
local notation "turnE"=> (flagS K G).volp
variable {A:ℂ→Rack G m}{f:ℂ→ Mob G}
lemma motion_point (l:Legs (Shore G m))(h:∀ w,DifferentiableAt ℂ (fun i=> A i w) i): DifferentiableAt ℂ (fun i=> beam ξ (A i) l) i:= by induction l generalizing A with| nil=> simpa using h []| cons i l ih=> simp_rw [Pilot.met]; exact DifferentiableAt.fun_sum (fun _ _=>(ih (A:=fun a=> Koszul.D (_,turnE i.2) (A a)) (fun w=> h _)).const_mul _)
lemma motion_hol (h:Rock.Hol D f): Rock.Hol D ((B) ∘ f):= ⟨fun i j he hx=>motion_fell s (h.price i j he hx), fun _ l i hi => motion_point (m:=_) (K:=s.arch _) (A:=fun j=> f j _) l (fun v=>h.top _ v i hi) ⟩
variable {T:Mob G}
lemma motion_form (h:Form0 false T): Form0 false (( B ) T):= ⟨motion_fell s h.price,motion_sturdy s h.token⟩

section travels
local notation "secG"=> field ( Landau.parity (A:=Arts.L m) (C:=G.ColorIndex) )
lemma moves_sym (hf:Symm (field Landau.parity) R) : Symm secG (beam (flagS K G) R):=by
   intro l i j w; induction l generalizing R with
   | nil=>
      -- two derivative linear shuffles
      change beam ξ R (i::j::w)= _ * beam ξ R (j::i::w); rw [Pilot.met]; simp_rw [Pilot.met,Finset.mul_sum]; conv_rhs=> rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _=> sum_congr rfl fun q _=>?_ ; by_cases he: μ i.1 p=0; simp [he]; by_cases hv: μ j.1 q=0; simp [hv]; -- see
      let P: Shore G m:=(p,turnE i.2); let Q: Shore G m:=(q,turnE j.2); rw [hf.commute Q P,map_smul]; dsimp only [ P,Q, field ]; rw [Pi.smul_apply,smul_eq_mul, ← (flagS K G).pair_zero i.1 _ he, ← (flagS K G).pair_zero j.1 _ hv ]; ring
   | cons a l ih=>
      rw [List.cons_append,List.cons_append,Pilot.met,Pilot.met,Finset.mul_sum]; refine Finset.sum_congr rfl fun p _=>?_ ; rw [ih (hf.drop _)]; ring
lemma turns_sp (p q:Cfield G m) : star ( (flagS K G).fieldC p q )= (flagS K G).fieldC p q:= by
   classical
   rcases p with ⟨⟨_|i,b⟩,p⟩ <;> rcases q with ⟨⟨_|j,c⟩,q⟩ <;> simp [flagS,leggo,Spin.prop,Spin.rayS,Spin.shadow] <;> split_ifs <;> simp
lemma moves_sight (l:Legs (Shore G m))(h:∀ w,R (invertMom w)=star (H w)): beam (flagS K G) R (invertMom l)=star (beam (flagS K G) H l):= by
 induction l generalizing R H with
 | nil=> simpa only [show invertMom ([]:Legs (Shore G m))=[] from rfl,Pilot.peeps] using h []
 | cons i l ih=>
     rw [show invertMom (i::l)= (i.1,-i.2)::invertMom l from rfl,Pilot.met, Pilot.met,star_sum ]; simp_rw [star_mul',turns_sp]; rw [map_neg]; exact sum_congr rfl fun j _=> congr_arg _ (ih fun w=> h ((j,turnE i.2)::w))
lemma turns_gh(p q:Cfield G m)(he:μ p q≠0): ghostNo p=ghostNo q:= by rcases p with ⟨⟨_|i,_|_⟩,j⟩ <;> rcases q with ⟨⟨_|i',_|_⟩,j'⟩ <;> simp [flagS,leggo,Spin.prop,rayS,Spin.shadow] at he <;> rfl
lemma moves_ghost {t:ℤ}(h:Rails (ghostNo ∘ Prod.fst) t R) : Rails (ghostNo ∘ Prod.fst) t (beam (flagS K G) R):=by
 intro l hl; induction l generalizing R t with | nil=> rw [Pilot.peeps]; exact h _ hl| cons i l ih=> rw [Pilot.met]; apply sum_eq_zero; intro j _; by_cases he: μ i.1 j=0; simp [he]; exact mul_eq_zero_of_right _ (ih (h.enter _) (fun hh=> hl (by rw [charge_int,hh]; simp only [Function.comp_apply]; rw [turns_gh i.1 j he]; simp)))
lemma moves_rank {k:ℤ}(hx: Book.Limit R k): Book.Limit (beam (flagS K G) R) k:= by intro l hl; induction l generalizing R k with | nil=> rw [Pilot.peeps]; exact hx _ hl| cons i l ih=> rw [Pilot.met]; exact sum_eq_zero fun j _=> mul_eq_zero_of_right _ (ih (hx.tip _ ) (by simp at hl; omega)) -- spelling
lemma branch (u:G.El)(i j:Cfield G m): ∑ b:Cfield G m,(dye (P:=SectorP m) u).fieldC i b * μ b j= ∑ b:Cfield G m, μ i b*(dye (P:=SectorP m) u).fieldC b j:=by
   rcases i with ⟨s,i⟩; rcases j with ⟨t,j⟩; rw [Fintype.sum_prod_type]; conv_rhs=> rw [Fintype.sum_prod_type]
   simp [Garment.dye, Spin.prop,leggo,flagS,ite_mul,mul_ite]; ring
-- commute proof template general Pilot
lemma trips {U W:Pilot ℂ ( SectorP m ) ( Landau.parity (A:=Arts.L m) (C:=G.ColorIndex))} (h:∀ i j:Cfield G m,(∑ b,U.fieldC i b*W.fieldC b j)=(∑ b,W.fieldC i b*U.fieldC b j))(hh:∀ z:SectorP m,W.volp (U.volp z)=U.volp (W.volp z)) (x:Legs (Shore G m)): U.beam (W.beam R) x=W.beam (U.beam R) x:= by
  induction x generalizing R with
  | nil=>simp
  | cons i l ih=>
      rw [Pilot.met,Pilot.met]; simp_rw [served,map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum, ← mul_assoc,hh]; rw [Finset.sum_comm]; conv_rhs=> rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul,h]; exact sum_congr rfl fun j _=> congr_arg _ (@ih (Koszul.D (j, U.volp (W.volp i.2)) R)) -- placeholder
end travels
lemma motion_shade (h:ShadeG T): ShadeG (( B ) T):=by
   intro m g; funext x; rw [burn, ← brush,trips (fun i j=> branch g i j) (fun _=> rfl),brush,h]
lemma motion_collar {t:ℤ}(h: Collar t T): Collar t (( B ) T):= ⟨fun i=> moves_sym (K:=s.arch _) (h.sym i),motion_shade s h.color, fun m=>moves_ghost (K:=s.arch _) (h.ghost m)⟩
end YM.MS.FVA.Motions
