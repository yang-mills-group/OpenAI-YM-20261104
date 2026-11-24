import YM.MS.Image.Atlas
/-! MS high regulator frame rotation, also on DREG entries. Composition is
 in TRAVEL order; don't replace field rotations by signed symmetry on each.
 (Note in `Sturdy false`, DRotations fix all FOUR axes and don't transport those.) -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Motions
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame Momentum Outlook
open scoped Topology BigOperators ContDiff
variable {G:Gauge}{B C:Type}[Fintype B][Fintype C][DecidableEq B][DecidableEq C]{i:ℂ}{m n k:ℕ}
set_option linter.unusedSectionVars false
-- t after s
def march (s t:Spin B): Spin B:= ⟨s.turn.trans t.turn,fun i j=>(t.rad _ _).trans (s.rad i j)⟩
lemma move_p(s t:Spin B)(i j:B): (march s t).profile i j=∑ b:B,s.profile i b*t.profile b j:= (t.orth (s.turn (spray i)) j).symm
lemma move_pc(s t:Spin B)(i j:B): ((march s t).profile i j:ℂ)= ∑ b:B,(s.profile i b:ℂ)*(t.profile b j:ℂ):=by rw [move_p]; push_cast; rfl
open Landau (Leg)
lemma move_tag(s t:Spin B)(i j:Leg B C): (leggo C (march s t)).fieldC i j=∑ b:Leg B C, (leggo C s).fieldC i b* (leggo C t).fieldC b j:=by
   rcases i with ⟨⟨u,b⟩,i⟩; rcases j with ⟨⟨v,c⟩,k⟩; simp only [leggo,Spin.prop,rayS,Fintype.sum_prod_type,ite_mul,mul_ite]; -- sum costs
   by_cases he:b=c <;> by_cases hp:i=k <;> simp [he,hp] -- see remaining
   cases u <;> cases v <;> simp [Spin.shadow,move_pc]
lemma move_comp (s t:Spin B)(l:Legs (Mode (Leg B C) (Momentum B)))(F:Plane.Row (Leg B C) (Momentum B) ℂ): beam (leggo C (march s t)) F l= beam (leggo C s) (beam (leggo C t) F) l:=by
   induction l generalizing F with
   | nil=> simp
   | cons i l ih=>
       rw [Pilot.met,Pilot.met]; simp_rw [move_tag, Finset.sum_mul]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun a _=>?_ ; rw [served,map_sum, Finset.sum_apply,Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [map_smul,ih,Pi.smul_apply, smul_eq_mul,mul_assoc]; rfl -- maybe no goals

@[ext] lemma eqSpin (s t:Spin B)(h:∀ x:Momentum B,s.turn x=t.turn x): s=t:=by rcases s with ⟨s,_⟩; rcases t with ⟨t,_⟩; have he:s=t:= ContinuousLinearEquiv.ext (funext h); subst t; rfl
def noneS (n:ℕ): Spin (L n):= ⟨ContinuousLinearEquiv.refl .., fun _ _=>rfl⟩
lemma turnZ (l:Legs (Shore G n))(F:Rack G n): beam (flagS (noneS n) G) F l= F l:=by
 induction l generalizing F with
 | nil=>simp
 | cons i l ih=>
    unfold flagS at *; obtain ⟨⟨⟨_|a,j⟩,i⟩,p⟩:=i; · rw [fromG, ih]; rfl
    rw [fromV]; rw [Finset.sum_eq_single a]; · rw [show ((noneS n).profile a a)=1 from (by change spray a a=1; simp [spray]), ih]; push_cast; rw [one_mul]; rfl
    · intro k _ h; rw [show (noneS n).profile a k=0 from (by change spray a k=0; simp [spray,h])]; simp
    simp -- may be too aggressive
-- arch identities, as equality of requests
variable (s t:Spin (L m)) (h:m≤n)
local notation "V"=> s.arch h
lemma arch_onZ (t:Spin (L n)) : t.arch le_rfl=t:= by
   apply eqSpin; intro x; have hX (u:SectorP n): Left (le_refl n) u=u:=funext fun v=> lasts _ u v; nth_rw 1 [← hX x]; rw [ Spin.arch_on, hX]
lemma arch_comp : (march s t).arch h=march (s.arch h) (t.arch h):= by
    apply eqSpin; intro x; nth_rw 1 2 [← city h x]; rw [ map_add, Spin.arch_identity, Spin.arch_on]; change _= (t.arch h).turn ((V).turn _ ); rw [map_add,map_add,Spin.arch_identity,Spin.arch_on,Spin.arch_identity,Spin.arch_on]; rfl
lemma arch_city (p : SectorP n): (V).turn p = p - Left h (Cl h p) + Left h (s.turn (Cl h p)):= by
   rw [show ( V ).turn p = taller h s p from rfl,Spin.total]; have hh:= city h p; rw [show p-Left h (Cl h p)=Right h (Cr h p) from sub_eq_of_eq_add (hh.symm.trans (add_comm ..))]; exact add_comm ..

lemma long_left (g:n≤k) (p:SectorP k) : Cl h (Cl g p)=Cl (le_trans h g) p:=rfl
lemma arch_arch (g:n≤k) : (s.arch h).arch g=s.arch (le_trans h g):= by
 apply eqSpin; intro x; rw [arch_city (s.arch h),arch_city s h,arch_city s (le_trans h g),map_add,map_sub,long_left]; simp_rw [show ∀ y:SectorP m,Left g (Left h y)=Left (le_trans h g) y from fun y=> by unfold Left; rw [sons,rides_link]]; abel
lemma arch_back : (s.arch h).back=s.back.arch h:= by
   -- comp and rail
   apply eqSpin; intro x; nth_rw 1 2 [← city h x]; rw [map_add,map_add,Spin.arch_identity, Spin.arch_on]; congr 1 <;> apply (V).turn.injective
   · rw [Spin.front,Spin.arch_on,Spin.front]
   rw [Spin.front,Spin.arch_identity]
lemma arch_walk (U:Spin (L n))(hr:∀ i:SectorP m,U.turn (Left h i)=Left h i): march (s.arch h) U=march U (s.arch h):=by
 apply eqSpin; intro x; have hh : Cl h x = Cl h (U.turn x):=by
   -- pair all physical basis
   funext i; let q:= Left h (spray i); obtain he:= U.rad (Left h (spray i)) x; rw [hr,farApart h,farApart h (Left h (spray i)) x,leftCl,Cr_down, Arts.pair_zero,Arts.pair_zero,add_zero,add_zero] at he; simpa [pairing,spray, Pi.single_apply,ite_mul] using he.symm -- congr var
 change U.turn ((V).turn x)= (V).turn (U.turn x); rw [arch_city,arch_city,← hh, map_add,map_sub,hr,hr]
local notation "Rot"=> Spin (L 0)
def motion (G:Gauge)(s: Spin (L 0)) : Mob G→ₗ[ℂ] Mob G where
   toFun F m:= beam (flagS (s.arch (Nat.zero_le m)) G) (F m)
   map_add' F H:= funext fun i=> map_add ( (flagS (s.arch (Nat.zero_le i)) G).beam ) (F i) (H i)
   map_smul' c F:= funext fun i=> map_smul ((flagS (s.arch (Nat.zero_le i)) G).beam) c (F i)
lemma burn(s:Rot)(F:Mob G)(n:ℕ): motion G s F n=beam (flagS (s.arch (Nat.zero_le n)) G) (F n):=rfl -- meta remove below
lemma motion_C (s t:Spin (L 0))(F:Mob G): motion G (march s t) F= motion G s (motion G t F):= by funext i; rw [burn, arch_comp ]; exact funext fun l=> move_comp (C:=G.ColorIndex) (s:=s.arch (Nat.zero_le i)) (t:=t.arch _) l _
lemma arch_noneS : (noneS m).arch h=noneS n:= by apply eqSpin; intro x; rw [arch_city]; exact sub_add_cancel ..
lemma motion_Z(F:Mob G): motion G (noneS 0) F=F:= by funext i; rw [burn,arch_noneS]; exact funext fun l=> turnZ l _
lemma motion_back(s:Rot)(F:Mob G): motion G s (motion G s.back F)=F:= by rw [← motion_C, show march s s.back=noneS 0 from eqSpin _ _ (fun v=> Spin.rear s), motion_Z]
lemma motion_zero(s:Rot)(F:Mob G): motion G s F 0=beam (flagS s G) (F 0):= by rw [burn,arch_onZ]
lemma motion_sturdy {F:Mob G}(s:Rot)(hf:Sturdy false F): Sturdy false (motion G s F):= by
 constructor
 · intro m K hk; let U:=s.arch (Nat.zero_le m); let Vx:= flagS U G; funext v; change beam (flagS K G) (beam Vx (F m)) v= _; have hz:= arch_walk s (Nat.zero_le m) K (hk rfl); have ha:= Eq.symm (move_comp (C:=G.ColorIndex) K U v (F m));
   calc _ = beam (flagS (march K U) G) (F m) v:= ha
        _ = beam (flagS (march U K) G) (F m) v:= by rw [hz]
        _ = _:= (move_comp (C:=G.ColorIndex) U K v (F m)).trans (congr_arg (fun b:Rack G m=> beam Vx b v) (hf.turn m K hk)) -- alignment fragile
 intro m n h i -- implicit
 rw [burn, ← show (s.arch (Nat.zero_le m)).arch h=s.arch (Nat.zero_le n) from arch_arch .., Spin.telescopeS h (s.arch (Nat.zero_le m)),funext (hf.grows h) ]; rfl
end YM.MS.FVA.Motions
