import YM.FVA2.Smooth.Edition
/-!
# Verify the derivative rule on any log-time using the nonpositive case
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Smooth.Cruise
open Set Function Filter Finset Metric MeasureTheory Real
open MS MS.Plane MS.Koszul MS.Landau MS.Landau.Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake
open MS.Breeze MS.Book MS.Book.Convolve MS.Plane.Flux MS.High MS.Rake.Geo MS.Vane MS.Vista MS.Motif MS.Plane.Wire
open MS.Tone.Frame MS.City MS.Osc MS.Osc.Snap Belt
open MS.Land MS.Local.Physical MS.Dial MS.Port
open Lifetime Slots
open Complex (I)
open scoped Topology ContDiff BigOperators Interval
variable {W I : Type}{G:Gauge}{P Q:Geo I}{b:Deck G}{M:Booked b}
variable {k:ℝ}
variable [LinearOrder W][Fintype W]
open MS.Tide
open MS.Momentum
variable (S:MS_Data G M) (u:W→Rake.Label b)
-- compute on Board specialized Draw W.
local notation "Π"=> Draw W
local notation "μ₀"=> (fun (_:Draw W)=>planeF)
local notation "Δ"=> Rake.Geo.constantP G (Draw W) (PlanetD G)
local notation "Ψ"=> (field (p:=Landau.parity ( A:=Axis ) (C:=G.ColorIndex) ) (P:=QP))
variable {v r t:ℝ} {s: Steps W}
local notation "R"=> frameF (Draw W) v
local notation "Ω"=> approach R S
variable {x: Position W (Draw W)} {T T' U:Finset W} {ρ:Steps W} {J: Set (Draw W)} {q: Draw W}
variable {V:Steps W→Dance G (Draw W) W} {w:Legs (Lane4 G)} {A:Type}
open MS.Alps
omit [Fintype W] in
lemma plus (i:W× Axis)(he:i∈ patch T) : Vane.charge (Slots.Hmark u ( hop s i )) T = charge (Hmark u s) T + 1 := by
    unfold charge; have h := mem_product.mp he|>.1; let F:=Hmark u s; let V:=Hmark u (hop s i); change (∑ j∈T, V j)=(∑ j∈T,F j)+1; rw [ show V=update F i.1 (F i.1+1) from ?_, sum_update_of_mem h ]; · rw [ add_comm (∑ j∈T,F j) 1 ]; rw [← add_sum_erase T F h, add_comm (F i.1) 1, add_assoc,sdiff_singleton_eq_erase] -- sum notation.erase order
    funext j; by_cases ha: j=i.1; · subst j; simp only [hop,V,F,Hmark,update_self,List.length_cons]; omega
    simp only [hop,V,F,Hmark,update_of_ne ha]; -- no omega
local notation "υ"=> Steps W
lemma frameY (_P:Geo I)(s _t: ℝ) (F:Glade G I) (k:ℤ)(m:I→QP) : relax (fun i=> exp s • m i) ( twist k (fun _:I=> s) F )= twist k (fun _:I=>s) ( relax m F ):= by
    funext i t l; change Tone.bill (exp s • m i) (net l) * ( Port.τ _ s * _ )=Port.τ _ s * ( Tone.bill (m i) (net (sr s l))* F _ _ _ ); rw [ net_sr,Tone.Mesh.dual ]; exact mul_left_comm ..
-- clock moves derivative input costs, remaining layer contributes τ power.
variable (ho:IsOpen J)(hu:∀ i, EqOn ( x i ) (fun q=> r • q i) J)(hx:Mesh (frameF (Draw W) v) x)
variable (ht:∀ s':Steps W,charted (frameF (Draw W) v) S u s' x ( V s' ))
include ho hu hx ht
lemma visa (t:ℝ)(T:Finset W)(n:ℕ)(s':Steps W)(h0:q∈J) : Rides r T s' (fun u y=> aboard x ( V u ) T n y t w ) q:= by
    obtain hh|hh:= T.eq_empty_or_nonempty; · subst T; exact alone S u ht n
    let Y(w:W)(i:Draw W):= exp (-t) • x w i; let v':= v+t; let Q:=frameF Π v'; have hY : Mesh Q Y:= by
       intro i j hi; have hζ(k:Draw W): ( Y i - Y j ) k= exp (-t) • (x i-x j) k:= by simp only [Y,Pi.sub_apply,smul_sub]
       obtain ⟨⟨ C,hC,hK⟩,A,hA,hE⟩:= hx i j hi; have he(k:Draw W): Q.roots k= (R).roots k:= rfl; refine ⟨ ⟨ exp (-t)*C,by positivity,fun k=>?_⟩, ⟨ exp (-t)*A,by positivity,fun k=>?_⟩⟩; all_goals rw [hζ,norm_smul_of_nonneg (exp_pos _|>.le),he,mul_assoc]; gcongr; first|exact hK k|exact hE k
    let P:=curve Q S u Y; let Ξ : Draw W→ℝ := fun _=> t; let U(s:Steps W):= charge ( Hmark u s ) T; have hm:Port.moved Ξ Y=x:= funext fun i=> funext fun y=> by unfold Port.moved Ξ Y; rw [Real.exp_neg, smul_inv_smul₀ (exp_pos _|>.ne')];
    have hV(s:Steps W): charted Q S u s Y ( P s ):= arrived S u s Y hY;
    have hr(s:Steps W): V s= Port.loom Ξ (Hmark u s) ( P s ):= perfect ( ht s ) (hm ▸ Slots.traveled (P:=R) S u s Y Ξ ( fun _=> rfl ) (hV s));
    let f(s:Steps W):= Port.τ (pitch w-( U s:ℤ)) t; let g (s:Steps W)(y:Draw W):= aboard Y ( P s ) T n y 0 (sr t w);
    have he(i:Steps W)(q: Draw W): aboard x (V i) T n q t w=f i * g i q:= by
       rw [hr]; unfold aboard perch; rw [show rootX x T=(fun i=>exp t • rootX Y T i) from funext fun i=> by rw [← hm]; exact moving Ξ Y T hh hh i]; -- rewriting ←hm issue inside Y
       change relax _ ( twist _ _ _ ) q t w = _; rw [frameY Q t t ]; change f i * ( relax _ _ q (t-t) _)=_; rw [sub_self]
    have hP : Rides (exp (-t)*r) T s' g q:= sailing S u ho (fun i y he=> by change exp (-t) • x i y= _; rw [ hu i he ]; exact (mul_smul ..).symm) hY hV T n q h0 s' 0 le_rfl (sr t w);
    have hζ (i:W×Axis)(hp:i∈patch T): f (hop s' i) = f s'*(exp (-t):ℂ):= by -- cast parse Real.exp
       unfold f U; rw [plus u i hp, show (( Real.exp (-t) ):ℂ)= Port.τ (-1) t from (by simp [Port.τ, Real.exp_neg]) , T_add ]; congr 1; omega
    simp_rw [he]; unfold Rides; convert! hP.const_mul ( f s' ) using 1; ext1 y; simp only [ Abroad.spray,_root_.smul_apply,smul_eq_mul, Finset.mul_sum,Complex.real_smul ]; apply Finset.sum_congr rfl; intro i hi; rw [hζ i hi]; push_cast; ring
end YM.FVA2.Smooth.Cruise
