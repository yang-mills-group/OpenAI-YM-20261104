import YM.MSbar.Lodge.Hat
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Lodge
open Function Filter Whisk Lis Measuring Cacao Aqua RawP Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {σ ι M:Type}[Fintype σ]
open Set Metric
local notation "Π"=>Positions σ
variable {g:ℝ→ℝ}{w B C:ℝ}{q k m:ℕ}(h:Hat k w B g) {F:Positions σ→ℝ}
noncomputable def Clamp (g:ℝ→ℝ)(x:Positions σ):Positions σ:=fun i=>g (x i)
local notation "Q"=> Clamp g ∘ (id (α:=Positions σ))
include h
lemma hut : ContDiff ℝ k (Clamp (σ:=σ) g):= contDiff_pi.mpr (fun i=>h.smooth.comp (contDiff_apply ℝ ℝ i)) -- signature
lemma peak (hw:0≤w)(x:Positions σ): Clamp g x∈ Metric.closedBall 0 w:=by rw [mem_closedBall_zero_iff]; exact (pi_norm_le_iff_of_nonneg hw).mpr fun i=> h.value _|>.2
lemma area (hk:1 ≤ k) (x:Positions σ)(i:σ) : fderiv ℝ (Clamp g) x (bolt i) = deriv g (x i) • bolt i:=by
    funext j; have ht := (h.smooth.differentiable (by exact_mod_cast (show k≠0 from by omega))); have hz : DifferentiableAt ℝ (Clamp g) x:= (hut h).differentiable (by exact_mod_cast (show k≠0 from by omega)) x
    let L:= (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : σ=>ℝ) j); have hb:L ∘ Clamp g = g ∘ L:= rfl
    rw [show fderiv ℝ (Clamp g) _ _ j= fderiv ℝ (L ∘ Clamp g) x (bolt i) from (by rw [fderiv_comp _ L.differentiableAt hz,L.fderiv]; rfl),hb,fderiv_comp _ (ht (L x)) L.differentiableAt,L.fderiv]; change fderiv ℝ g (x j) (bolt i j)=deriv g (x i) * bolt i j; by_cases hv:i=j; subst j; rw [show bolt i i=(1:ℝ) from Pi.single_eq_same ..,mul_one]; rfl; rw [show bolt i j=0 from (by simp [bolt,Ne.symm hv]),map_zero,mul_zero]
variable (hf :∀ x:Positions σ,ContDiffAt ℝ k F (Clamp g x))(x: Positions σ) (i:σ)
local notation "W"=>F ∘ Clamp g
local notation "Δ"=> fun x:Positions σ=>deriv g (x i)
include hf
lemma budgetC (hp:1 ≤ k): (fun x=>buoy (F ∘ Clamp g) x [i]) = fun x:Positions σ=> deriv g (x i)*buoy F (Clamp g x) [i]:=by
   funext x; let G:= @Clamp σ g; change fderiv ℝ (F ∘ Clamp g) x _=deriv g (x i)*fderiv ℝ F _ _; have he:(k:WithTop ℕ∞)≠0:=Nat.cast_ne_zero.mpr (by omega)
   rw [fderiv_comp _ ((hf x).differentiableAt he) ((hut h).differentiable he x), ContinuousLinearMap.comp_apply, area h hp,map_smul];rfl
variable (t:List σ)(he:t.length+1≤k)
include he
lemma recur : buoy W x (i::t)=buoy ((fun x:Positions σ=>deriv g (x i))* ((fun y:Positions σ=> buoy F y [i]) ∘ Clamp g)) x t :=by
   let V:Positions σ→ℝ:=fun x=> buoy W x [i]; have hs: V=(Δ)* ((fun y:Positions σ=> buoy F y [i]) ∘ Clamp g):=budgetC h hf i (by omega) -- arguments
   rw [← hs]; unfold buoy; rw [List.map_cons,takeG k ((hf x).comp x (hut h|>.contDiffAt))]; rfl; rwa [List.length_map,Nat.lt_iff_add_one_le]
variable (hL:∀ j∈i::t, |x j|<w/2)
lemma paint_eq (hz:∀ j∈i::t, |x j|<w/2) : buoy W x (i::t)= buoy F (Clamp g x) (i::t):=by
   -- recurse F' depends only Φ smooth grade globally ∀ Clamp. choose k can lower h.
   induction t generalizing k x F i with
   | nil=> have ht : g =ᶠ[𝓝 (x i)] id:= ((continuous_abs.tendsto (x i)).eventually (eventually_lt_nhds (hz i (List.mem_cons_self ..)))).mono (fun y he=> h.honest _ he); have hp:deriv g (x i)=1:= ht.deriv_eq.trans (deriv_id _); exact (congr_fun (budgetC h hf i (by omega)) x).trans (by rw [hp,one_mul])
   | cons a t ih=>
       have hl:(k-1)+1 ≤ k:=by simp only [List.length_cons] at he; omega
       have hp: Hat (k-1) w B g:= ⟨h.1,h.2,h.smooth.of_le (Nat.cast_le.mpr (Nat.sub_le ..)),fun x i hi=>h.head _ _ (by omega)⟩
       let Y(v:Positions σ):=buoy F v [i]; have hs(x:Positions σ): ContDiffAt ℝ (↑(k-1:ℕ)) Y (Clamp g x):= Lis.smooth k _ _ (hf x) (by simpa using hl)
       have hC:= ih hp hs x a (by simp only [List.length_cons] at he ⊢; omega) (fun j hj=> hz j (List.mem_cons_of_mem _ hj))
       let K:(Positions σ)→ℝ:= fun v=>deriv g (v i); have hK: K=ᶠ[𝓝 x] (fun _=>1):=by
           have hu:= (show g=ᶠ[𝓝 (x i)] id from ((continuous_abs.tendsto (x i)).eventually (eventually_lt_nhds (hz i (List.mem_cons_self ..)))).mono fun y hy=> h.honest y hy).deriv; filter_upwards [(continuous_apply i|>.continuousAt (x:=x)|>.eventually hu)] with y he; exact he.trans (deriv_id _)
       rw [recur h hf x i _ he]; unfold buoy
       let L:=(a::t).map (@bolt σ); change roc (K*(Y ∘ Clamp g)) L _= roc F (bolt i ::L) _; rw [ (Lis.follows L (show K*(Y ∘ Clamp g)=ᶠ[𝓝 x] Y ∘ Clamp g from hK.mono (fun i hi=> (by rw [Pi.mul_apply,hi]; exact one_mul _)))).eq_of_nhds,show roc (Y ∘ Clamp g) L x=roc Y L (Clamp g x) from hC, takeG k (hf x)]; rfl; unfold L; simp only [List.length_map]; omega
end YM.MSbar.Lodge
