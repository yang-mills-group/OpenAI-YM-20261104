import YM.XSpace.Costs
import YM.MS.Tide.Cost
import YM.FVA2.Smooth.Blades
/-!
# Power-rate UV bound calculus: `Fast` and `Sharp`

Helpers for the actual estimates on the Mesh (spacing, period)
regulators of the common prescription. See `YM/FVA2/Speed/Firm`
for the norms explicitly in use at every fixed compact separated profile
on the whole `Front` filter (so bounds on volume/spacing growth as
there, not arbitrary meshes; see `Arrival/Schedule`).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Speed
open XSpace XSpace.Expense MS MS.Tide
open Metric Asymptotics Set Function Filter MeasureTheory Real
open scoped Topology BigOperators ContDiff
variable {I E F T J:Type*} [NormedAddCommGroup E][NormedAddCommGroup F]{l:Filter I}
local notation "ɛ"=> Tide.mildG
variable (τ:I→ XSpace.Mesh)
abbrev chip (m:XSpace.Mesh):= m.spacing^ɛ
def fine (τ:I→ XSpace.Mesh)(i:I): ℝ:= chip (τ i)
lemma f_pos(i:I) : 0 < fine τ i:= _root_.Real.rpow_pos_of_pos ( τ i |>.positive ) _
abbrev Fast (l:Filter I)(τ:I→ XSpace.Mesh)(x y:I→E): Prop:= (fun i=>x i-y i)=O[l] fine τ
variable {τ} (h:Stretched l τ)
include h
lemma beats : Tendsto (fine τ) l (𝓝 0):= by simpa [ Real.zero_rpow ( Tide.mild_p.ne' ) ] using! ( h.endpt.rpow_const ( Or.inr Tide.mild_p.le ) ) -- expects `x>0 ∨ p≥0` check
lemma sustain : Expense.Cap l (fine τ) := IsBigO.of_bound' ( by filter_upwards [h.smaller] with i hi; rw [Real.norm_of_nonneg (f_pos τ i|>.le), norm_one]; exact Real.rpow_le_one (z:=mildG) (τ i|>.positive.le ) hi mild_p.le ) -- binder arg
lemma sail : (Expense.a τ)=O[l] fine τ := IsBigO.of_bound' (by filter_upwards [h.smaller] with i hi; rw [ Real.norm_of_nonneg ( actual τ i|>.le ), Real.norm_of_nonneg (f_pos τ i|>.le) ]; have hh:= Real.rpow_le_rpow_of_exponent_ge ( actual τ i ) hi ( show mildG≤1 by unfold mildG High.eps_gain; norm_num ); rw [Real.rpow_one] at hh; exact hh ) -- need lemma name check
omit h
namespace Fast
variable {x y f g:I→E}
lemma bounds (p:Fast l τ x y): ∃ C:ℝ,0<C∧∀ᶠ i in l, ‖x i-y i‖≤ C* chip (τ i):= by obtain ⟨C,hC,h⟩:=(show _=O[l] _ from p).exists_pos; exact ⟨C,hC, by simpa only [ Real.norm_of_nonneg ( f_pos τ _|>.le ) ] using! h.bound ⟩
lemma put (C:ℝ)(h:∀ᶠ i in l,‖x i-y i‖≤ C*chip (τ i)): Fast l τ x y:= IsBigO.of_bound C ( by simp_rw [ Real.norm_of_nonneg ( f_pos τ _|>.le ) ]; exact h )
lemma usual (h:Stretched l τ)(hp:Rate l τ x y): Fast l τ x y:= IsBigO.trans hp (Speed.sail h) -- Rate inherits Asy? arrow
lemma exact_t (h:x=ᶠ[l] y): Fast l τ x y:= put 1 (h.mono (fun x hx=> by rw [hx,sub_self,norm_zero,one_mul]; exact f_pos _ _ |>.le))
lemma higher (h:Stretched l τ)(hp:Expense.Cap l y)(hg:Fast l τ x y): Expense.Cap l x:= (IsBigO.add (IsBigO.trans hg (sustain h)) hp).congr_left (by simp)
lemma refl (l:Filter I)(τ:I→ XSpace.Mesh)(F:I→E): Fast l τ F F:= exact_t (.refl ..)
lemma comp {C:Filter J}(w:J→I)(H:Tendsto w C l)(hp:Fast l τ x y): Fast C (τ ∘ w) (x ∘ w) (y ∘ w):= hp.comp_tendsto H
lemma add (hp:Fast l τ x y)(hg:Fast l τ f g): Fast l τ (x+f) (y+g):= (IsBigO.add hp hg).congr_left (by intro i; simp; abel)
lemma neg (hp:Fast l τ x y): Fast l τ (-x) (-y):= (IsBigO.symm hp).congr_left (by intro i; simp; abel)
lemma sub (hp:Fast l τ x y)(hg:Fast l τ f g): Fast l τ (x-f) (y-g):= by rw [sub_eq_add_neg,sub_eq_add_neg]; exact add hp (Fast.neg hg)
lemma tee (hp:Fast l τ x y)(hf:x=ᶠ[l] f)(hh:y=ᶠ[l] g): Fast l τ f g:= ( IsBigO.congr' hp (hf.sub hh) ( EventuallyEq.refl .. ) )
lemma mul {K:Type*} [NormedRing K]{x y f g:I→K}(h:Stretched l τ)(hx:Expense.Cap l f)(hy: Expense.Cap l g)(hp:Fast l τ x f)(he: Fast l τ y g): Fast l τ (x*y) (f*g):=by
    have hu : (fun i=> x i*y i-f i*g i)=fun i=>x i*(y i-g i) +(x i-f i)*g i:=funext fun i=> by rw [mul_sub,sub_mul]; abel
    change (fun i=>x i*y i-f i*g i)=O[l] _; rw [hu]; exact IsBigO.add ((IsBigO.mul (Fast.higher h hx hp) he).congr_right (fun i=> one_mul _)) ((IsBigO.mul hp hy).congr_right (fun i=> mul_one _)) -- no comm
lemma scalar {K:Type*} [NormedRing K]{x y:I→K}(hp:Fast l τ x y)(m:K): Fast l τ (fun i=>m*x i) (fun i=>m*y i):= by unfold Fast; simp_rw [← mul_sub]; exact IsBigO.const_mul_left hp m -- likely lemma orient
lemma sum (F H : J → I → E) (s : Finset J) (h : ∀ i∈ s, Fast l τ (F i) (H i)): Fast l τ (fun i=> ∑ j∈s,F j i) (fun i => ∑ j∈s,H j i) := by
  unfold Fast; simp_rw [← Finset.sum_sub_distrib]; exact IsBigO.sum h
variable (h:Stretched l τ)
include h
lemma aims (a:E)(hp:Fast l τ x (fun _=>a)): Tendsto x l (𝓝 a):= by
    have ht:= (IsBigO.trans_tendsto hp (beats h)); have hh:Tendsto (fun i=> x i - a + a) l (𝓝 (0+a)):= ht.add tendsto_const_nhds; simpa using hh
lemma constant [NormedSpace ℝ E][NormedSpace ℝ F]{w:E→F}{a:E}(hx:DifferentiableAt ℝ w a)(hp:Fast l τ x (fun _=>a)): Fast l τ (w ∘ x) (fun _=> w a) := IsBigO.trans (hx.isBigO_sub.comp_tendsto (Fast.aims h a hp)) hp
omit h in
lemma pair {z w : I→F}(hf:Fast l τ x y)(he:Fast l τ z w): Fast l τ (fun i=>(x i,z i)) (fun i=>(y i,w i)):= by
    obtain ⟨C,hC,hf'⟩:= Fast.bounds hf; obtain ⟨D,hD,h⟩:= Fast.bounds he; apply Fast.put (max C D); filter_upwards [hf',h] with i hi he; rw [ Prod.norm_def ]; simp only [Prod.fst_sub,Prod.snd_sub,max_le_iff]; have hz:= (f_pos τ i).le; exact ⟨ hi.trans (mul_le_mul_of_nonneg_right (le_max_left ..) hz), he.trans ( mul_le_mul_of_nonneg_right ( le_max_right .. ) hz ) ⟩
end Fast
structure Sharp (l:Filter I)(τ:I→ XSpace.Mesh)(x y:I→E): Prop where
   quote : Expense.Cap l y
   sails : Fast l τ x y
namespace Sharp
variable {x y f g:I→E}
lemma tee (p:Sharp l τ x y) (h:x=ᶠ[l] f)(he:y=ᶠ[l] g): Sharp l τ f g:= ⟨IsBigO.congr' p.quote he (.refl ..), Fast.tee p.sails h he⟩
lemma once {L:Filter J}{w:J→I}(H:Tendsto w L l)(hp:Sharp l τ x y): Sharp L (τ ∘ w) (x ∘ w) (y ∘ w) := ⟨ IsBigO.comp_tendsto hp.quote H, Fast.comp w H hp.sails ⟩
lemma above {a:E}(hx: Fast l τ x (fun _=> a)): Sharp l τ x ( fun _=> a ) := ⟨ Expense.Cap.const .., hx ⟩
lemma joy (l:Filter I)(τ:I→ XSpace.Mesh)(a:E): Sharp l τ (fun _=>a) (fun _=>a):= above ( Fast.refl .. )
lemma add (hx:Sharp l τ x y)(he:Sharp l τ f g): Sharp l τ (x+f) (y+g):= ⟨ hx.quote.add he.quote, Fast.add hx.sails he.sails ⟩
lemma sub (hx:Sharp l τ x y)(he:Sharp l τ f g): Sharp l τ (x-f) (y-g):= ⟨ hx.quote.sub he.quote, Fast.sub hx.sails he.sails ⟩
lemma sum (F H : J→ I→ E)(s:Finset J)(h:∀ i∈s,Sharp l τ (F i) (H i)): Sharp l τ (fun i=>∑ j∈s,F j i) (fun i=>∑ j∈s,H j i):= ⟨ ( IsBigO.sum ( fun i hi=> ( h i hi ).quote ) ), Fast.sum F H s (fun i hi=> (h i hi).sails) ⟩
lemma mul {K:Type*}[NormedRing K]{x y f g:I→K}(h:Stretched l τ)(hp:Sharp l τ x y)(he:Sharp l τ f g): Sharp l τ (fun i=> x i*f i) (fun i=> y i*g i):= ⟨ Expense.Cap.mul hp.quote he.quote, Fast.mul h hp.quote he.quote hp.sails he.sails ⟩
-- scalar only on rings
lemma scalar {K:Type*}[NormedRing K] {x y:I→K}(hp:Sharp l τ x y)(a:K): Sharp l τ (fun i=>a*x i) (fun i=>a*y i):= ⟨ Expense.Cap.mul ( Expense.Cap.const .. ) hp.quote,Fast.scalar hp.sails a ⟩
lemma of_bounds (K:Set J)[TopologicalSpace J] (H:IsCompact K){p:I→J}{Y:J→E} (hv:∀ᶠ i in l,p i∈K)(hy: ContinuousOn Y K)(hp: Fast l τ x ( Y ∘ p )): Sharp l τ x (Y ∘ p):= ⟨ Expense.Cap.includes (Y '' K) ( H.image_of_continuousOn hy ) (hv.mono fun _ hi=> Set.mem_image_of_mem _ hi),hp⟩ -- order ts binder invalid
lemma prod (T: Finset J){F G:J→I→ℂ}(h:Stretched l τ)(he:∀ i∈T,Sharp l τ (F i) ( G i )): Sharp l τ (fun i=>∏ t∈T,F t i) (fun i=>∏ t∈T,G t i):= by
    classical
    induction T using Finset.induction_on with| empty=> simp; exact joy .. | insert i j hi ih=> simp_rw [Finset.prod_insert hi]; exact Sharp.mul h (he i (by simp)) (ih (fun i hi=> he i (by simp [hi]) ))
end Sharp
end YM.FVA2.Speed
