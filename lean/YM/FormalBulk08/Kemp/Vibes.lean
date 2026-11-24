import YM.FormalBulk08.Kemp.Vail

/-! Earn per fixed grade, then board Kith and invariant mark. No proofs of
costs over a long chain here. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Kemp
open Reef Lava Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 PowerSeries Bank
open Stationary Lotus Shore Mesa Gorge City Cork Rift Next.Free Flat RG Precision Tree
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
variable {G : Gauge} {I J: Type*} {η θ A B C : ℝ} {l i u j t r D d : ℕ}{K : KernelChoices}
variable (a:Loc G 1)(P: Flight j t)(Y: Anthem D G)(W:Pot G)
lemma chief_h (x:Site P.L): chief P (lift x,a) a=(0,a):= by
    refine Prod.ext ?_ rfl
    change rent P.L (lift x)=0; exact (rent_raw (0:Cover) (lift x) x (by simp)).2
lemma wedge_step (hy:Wade a Y l)(hw: Story W (pink K.penalty P.wing))(hL:2≤P.L.val) (E:ℕ) : ∃ θ : ℝ,0<θ ∧
    (∀ e≤E,∀ r,∃ C,Bail (fame _) θ (W e r) C) ∧ ∀ e≤E,∀ r,∃ C:ℝ,0≤C ∧ ∀ p,∀ x:Site P.L, Knoxville (fame _) θ (lift x,a) (stepsong P Y hL p x e r) (C*‖p‖):= by
    let I:=Fin (E+1)× Fin (l+E+1)
    choose s B hs hB H using fun i:I=>step_bill a P Y hy hL i.1.val i.2.val
    obtain ⟨v,-,hv⟩:= Finset.exists_min_image Finset.univ s ⟨(⟨0,by omega⟩,⟨0,by omega⟩),Finset.mem_univ _⟩
    obtain ⟨τ,hτ,hU⟩:=demanded_finite P W hw E
    refine ⟨min τ (s v),lt_min hτ (hs v),fun e he r=> ?_,fun e he r=>?_⟩
    · obtain ⟨C,hC⟩:=hU _ he r; exact ⟨C,hC.shrink (min_le_left ..)⟩
    by_cases h:r≤l+E
    · let i:I:=(⟨e,by omega⟩,⟨r,by omega⟩); exact ⟨_,hB i,fun p x=> penn_shrink (H i p x) ((min_le_right ..).trans (hv i (Finset.mem_univ _)))⟩
    refine ⟨0,le_rfl,fun p x=>?_⟩; rw [show stepsong P Y hL p x e r=0 from ?_, zero_mul]; exact Knox_zeros _
    by_contra hp;have hh:=step_can a P Y hy hL p x e r hp;unfold Yield at hh;omega
-- cost on grouped recurrence family
variable {V X E: Type*}{H:Reach V}{c:X→ℝ}{o:V}
def LightPay (H:Reach V)(η:ℝ)(o:V)(T:X→Tile V r)(c:X→ℝ) := ∃ C:ℝ,0≤C∧∀ x, Knoxville H η o (T x) (C*c x)
lemma LightPay.plus {T U:X→Tile V r}(h:LightPay H η o T c)(hy:LightPay H η o U c): LightPay H η o (fun x=>T x+U x) c:= by obtain ⟨A,hA,H⟩:=h; obtain ⟨B,hb,V⟩:=hy; refine ⟨A+B,add_nonneg hA hb,fun p=>?_⟩;rw [add_mul];exact (H p).add (V p)
lemma LightPay.amp {T:X→Tile V r}(h: LightPay H η o T c)(e:ℝ): LightPay H η o (fun x=> e • T x) c:= by obtain ⟨A,hA,H⟩:=h; refine ⟨|e| *A,mul_nonneg (abs_nonneg _) hA,fun x=>?_⟩; rw [mul_assoc]; exact (H x).smul _
lemma LightPay.lengthen {T:X→Tile V r}(h: LightPay H η o T c)(he : r=l): LightPay H η o (fun x=> lengthen he (T x)) c:=by subst r; exact h
lemma LightPay.polish {T:X→Tile V r}(h:LightPay H η o T c): LightPay H η o (fun x=>sand (T x)) c:= by obtain ⟨A,hA,H⟩:=h; exact ⟨A,hA,fun x=>(H x).polish⟩
lemma pay_sums {T:E→ X→Tile V r}(A: Finset E)(h:∀ i∈A,LightPay H η o (T i) c): LightPay H η o (fun x=>∑ i∈A,T i x) c:= by
    induction A using Finset.induction with
    | empty=> exact ⟨0,le_rfl,fun i=>by simp only [Finset.sum_empty,zero_mul]; exact Knox_zeros _⟩
    | @insert i A he ih=> simp_rw [Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).plus (ih fun j hj=> h j (Finset.mem_insert_of_mem hj))
lemma light_income (E n:ℕ)(q:V→V→ℝ)(T:Waves V)(S:X→OrbitV V)(hs:0≤η)(h:Grate H η (fun a b=>q b a) C)
    (hp:∀ i j, i≤n → j≤E →∀ r:ℕ,0<r→ ∃ B,Bail H η (T i j r) B)(he:∀ j≤E,∀ r,LightPay H η o (fun x=>S x j r) c): ∀ e≤E,∀ r,LightPay H η o (fun x=>dipper q T (S x) n e r) c:= by
   induction n using Nat.strong_induction_on with
   | _ n ih=>
     intro e hv r; cases n with
     | zero=> simp_rw [dipper_first]; exact he e hv r
     | succ n=>
       simp_rw [dipper_succ]
       have ht(i)(hi:i≤n) (a)(ha:a≤E)(r):LightPay H η o (fun x=> dipper q T (S x) i a r) c:= ih i (by omega) (fun x j ht=>hp x j (by omega)) a ha r
       refine LightPay.amp (LightPay.plus ?_ (LightPay.amp ?_ _)) _
       · obtain ⟨B,hB,hj⟩:=ht n le_rfl e hv (r+1+1)
         refine ⟨(1/2*(r+2)*(r+1))*(C*B),mul_nonneg (by positivity) (mul_nonneg h.1 hB),fun x=>?_⟩; convert knox_stare (hj x) hs (fun a b=> (h.rough hs b a)) h.1 using 1;ring
       unfold brawl Lava.reach; apply pay_sums; intro a ha; apply pay_sums; intro b hb; apply pay_sums; intro i hi
       rw [Finset.mem_antidiagonal] at ha hb; simp_rw [visor_eq]; refine LightPay.lengthen (LightPay.polish ?_) _
       obtain ⟨A,H'⟩:=hp b.1 a.1 (by omega) (by omega) (i.val.1+1) (by omega); obtain ⟨B,hB,hj⟩:=ht b.2 (by omega) a.2 (by omega) (i.val.2+1)
       refine ⟨(1/2*(i.val.1+1)*(i.val.2+1))*(A*C*B),mul_nonneg (by positivity) (mul_nonneg (mul_nonneg H'.1 h.1) hB),fun x=>?_⟩; convert knox_bond h hs H' (hj x) using 1; ring
-- cover cut
lemma penn_port {x:Biglot I}{T:Tile (Biglot (J⊕I)) r} (h:Knoxville (fame _) η (coastRight _ _ _ x) T A): Knoxville (fame _) η x (jetty (coastRight _ _ _) T) A:=by
   refine cut_charge (f:=coastRight Cover J I) (W:=fame (J⊕I)) ?_ (fun _ _=>rfl) x h; intro a b hv; exact Prod.ext (show (coastRight _ J _ a).1=(coastRight _ J _ b).1 from congr_arg Prod.fst hv) (Sum.inr_injective (show (coastRight _ J _ a).2=(coastRight _ J _ b).2 from congr_arg Prod.snd hv))
end YM.FormalBulk08.Kemp
