import YM.Contacts.Procession.Dusk
/-!
# Ext finite mark specialization. μ optional register at each coarse site,
 extract each marker separately AFTER touching common partition.
-/
noncomputable section
namespace YM.Contacts.Procession.Xenon
open Function Set Filter Pulse Pulse.Form Finset Sun
open Milling Milling.Forge Matrix MvPolynomial
open scoped Topology BigOperators Classical Matrix
variable {T α β γ : Type}[AddCommGroup T]{B k i j v p r :ℕ}
def coreM (T α:Type) : Matrix (T×α) (Live T α) ℝ:= Matrix.of fun x y=> if core T α x=y then 1 else 0
def veil (A:Matrix (T×α) (T×β) ℝ): Matrix (Live T α) (Live T β) ℝ := Matrix.of fun a b=> a.2.elim (if b.1=a.1∧ b.2=none then 1 else 0) (fun i=> b.2.elim 0 (fun j=> A (a.1,i) (b.1,j)))
def quiet (A: (T×α) → (T×α)→ℝ) : Live T α → Live T α → ℝ:= fun a b=> a.2.elim 0 fun i=> b.2.elim 0 fun j=> A (a.1,i) (b.1,j)
lemma quiet_sc (A:(T×α) → (T×α)→ℝ) : Pulses (core T α) (quiet A) A:= by
   have hh (x:Live T α)(ht:x∉ Set.range (core T α)) : x.2=none := by rcases x with ⟨x,a|a⟩; exact rfl; exact (ht ⟨(x,a),rfl⟩).elim -- pattern none
   refine ⟨fun _ _=>rfl, fun a b h=>by simp [quiet,hh a h], fun a b h=>?_⟩; simp only [quiet,hh b h]; cases a.2 <;> rfl
def cloak (G: House (T×α)): House (Live T α):= fun i r=> hoist (coreM T α) (G i r)
def ringS {i:ℕ}(b:ℕ)(f:Pulse.Field (Fin i) (T×α))(A:House (T×α)) : House (Live T α) := cloak A + Pi.single b (Pi.single (i+1) (stem f))
def leafS (f:Pulse.Field (Fin i) α):House α:= Pi.single 0 (Pi.single i f)
def mote (s:ℝ)(x:Live T α):ℝ:= if x=(0,none) then s else 0
def star (s:ℝ)(x:T×α→ℝ)(i : Live T α):= i.2.elim (mote s i) fun a=> x (i.1,a)
abbrev small (j:T×α):=core T α j
@[simp] lemma stsmall (s:ℝ)(x:T×α→ℝ)(i:T×α): star s x (small i)=x i:= rfl
@[simp] lemma stnone (s:ℝ)(x:T×α→ℝ)(i:T): star s x (i,none)=(if i=0 then s else 0):= by unfold star mote; simp
lemma onePass (s:ℝ)(x:T×α→ℝ)(r:Plate (Live T α)): aeval x (castP (core T α) (mote s) r)=aeval (star s x) r:= by
   refine merch _ _ _ _ (fun i=>?_) _; rcases i with ⟨i,_|a⟩; · unfold Sun.sign; rw [dif_neg]; exact aeval_C ..; rintro ⟨q,h⟩; simpa [core] using (congr_arg Prod.snd h) -- simplify
   rw [← core_apply, sortPass,aeval_X]; rfl
variable [Fintype T][Fintype α][Fintype β]
lemma grate (z:Live T α→ℝ)(x:T×α): (coreM T α*ᵥ z) x=z (small x):= by simp [Matrix.mulVec,dotProduct,coreM,ite_mul]
lemma pose (s:ℝ)(y:T×β→ℝ)(A:Matrix (T×α) (T×β) ℝ): veil A*ᵥ star s y=star s (A *ᵥ y):= by
   funext i; rcases i with ⟨i,_|a⟩; · change _=star s (A *ᵥ y) (i,none); rw [stnone]; simp [Matrix.mulVec,dotProduct, Fintype.sum_prod_type, Fintype.sum_option,veil,ite_mul] -- norm notation
   change _=(A*ᵥ y) (i,a); simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type, Fintype.sum_option,veil,Matrix.of_apply,Option.elim_some,Option.elim_none,zero_mul,zero_add]; rfl
lemma cast_star (A:House (T×α))(s:ℝ)(i:ℕ): castP (core T α) (mote s) (stage i (cloak A i))=stage i (A i):= by
   apply MvPolynomial.funext; intro x; change aeval x _=aeval x _; rw [onePass]; simp_rw [stage,cloak,map_sum]; apply sum_congr rfl; intro u _; change House.design _ _=House.design _ _; rw [Milling.Forge.hoist_read]; exact congr_arg _ (funext (grate (star s x))); -- use `.aeval_eq_eval` maybe not defeq
lemma stem_front (f:Pulse.Field (Fin i) (T×α))(a:ℝ)(x:T×α→ℝ): House.design (stem f) (star a x)= a*House.design f x:= by
   let Z:= (star a x); let X:=Live T α; let H:= scroll T α i; rw [House.design,stem,verse_print]; let F:=(fun y:Fin (i+1)→X=>scarab f y*(∏ j,Z (y j))); change House.design (scarab f) Z=_; rw [House.design_spec]
   letI:DecidableEq (Fin (i+1)):=fun _ _=>Classical.propDecidable _; rw [← tsum_fintype (L:=.unconditional _)]; change (∑' x,F x)=_; rw [←H.injective.tsum_eq (f:=F), tsum_fintype, Fintype.sum_prod_type]; swap; · intro n hn; by_contra h; exact hn (by change scarab f n * _=0; rw [scarab,dif_neg h]; simp)
   unfold F; change ∑ x:T,∑ y:Boys i (T×α), scarab f (focus x y)*(∏ j,Z (focus x y j))=a* _; simp_rw [scar_read,Fin.prod_univ_succ, focus,Fin.cons_zero, Fin.cons_succ]; change ∑ i:T, ∑ y:Boys _ _,f y*(star a x (i,none)*∏ j,x (adder i (y j)))= _; simp_rw [mul_left_comm (f _), ← mul_sum]; rw [sum_eq_single (0:T),stnone,if_pos rfl, House.design_spec]; congr! with i; try simp [adder]
   · intro b _ hh; rw [stnone,if_neg hh,zero_mul]
   simp
lemma scroll_rank : True:= trivial
end YM.Contacts.Procession.Xenon
