import YM.WilsonCoeffUV.Vacuum.Step.Domain
/-!
# Heat strict arrows. Also isolate post (non-W) part at same h-bead.
Exponent and width shares consumed as needed. Never upper-bound inherited P
here at post powers for its successor. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free PowerSeries
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{i j ℓ n k e r:ℕ}
namespace Stand
variable {I:Gear G} (W:Stand I)
abbrev payMat: ropes Cover (Helms I) (Helms I) := stair (upper W.R 0) 0

def flashback (r:ℕ)(e:ℕ): Ten ℝ (YForest G) r:= scoop (intake I W e r)+∑ j∈Finset.range (2+3*e), scoop (W.rays (j+1) e r)
lemma snow_price (e r:ℕ): snow I.patch I.kernel I.angle W.R W.Q W.page e (r+1)= W.flashback (r+1) e - prism W.Q (plants I.patch.L (scrub W.page e)) (r+1):=by
   let K:= Helms I
   unfold snow sluice; rw [show 3+3*e= (2+3*e)+1 by omega,Finset.sum_range_succ']
   have ht : spurs I.patch I.kernel I.angle W.R W.Q W.page 0 e=intake I W e - prism (upper 1 W.Q) (plants I.patch.L (scrub W.page e)):= by rw [spurs,tide_zero]; rfl
   have hy : scoop (prism (upper 1 W.Q) (plants I.patch.L (scrub W.page e)) (r+1))=prism W.Q (plants I.patch.L (scrub W.page e)) (r+1):=by
      ext x; unfold scoop prism; rw [climb_cut,climb_cut]; rfl
   rw [ht]; ext1 x; unfold scoop flashback; simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, scoop]; unfold Stand.rays; rw [show (prism (upper 1 W.Q) _ (r+1) _)= _ from congr_fun hy x]; abel

-- exact drift identity for positive rank
lemma post (e r:ℕ): W.driftU (e+1) (r+2)= - W.flashback (r+2) (e+1) + prism W.Q (plants I.patch.L (W.page (e+1))) (r+2):=by
   unfold Stand.driftU tinge; simp only [Pi.add_apply,Pi.sub_apply,uband, shine_dark (show 0≠ r+2 by omega),add_zero, flatPal,Nat.succ_ne_zero,↓reduceIte]
   rw [W.snow_price, scrub, if_neg (Nat.succ_ne_zero _)]; simp; abel
end Stand

lemma pm_rate {I:Gear G}(R:Rally k r I) : Ballast I.s I.D R.σ R.P.payMat R.Q.payMat:= Ballast.staged (Ballast.up R.Χ (Ballast.zero.fee R.θ (zero_le_one.trans I.bill_nn))) (Ballast.zero.fee R.θ (zero_le_one.trans I.bill_nn))
lemma trim_zero {α:Type} {R:ropes Cover α α}{P Q:Gen ℝ (Cloth α)}(h: P=0 ∨ Q=0): whittle R P Q =0:=by
    have hv i j k : swivel (rill R P Q i j k)=0:=by
       unfold swivel; rw [Finset.sum_eq_zero,smul_zero]; intro v _; funext x y; unfold rill; rcases h with h|h <;> subst_vars;
       · rw [show sever (y 0) (0:Gen ℝ (Cover×α)) j=0 from funext fun i=>by simp [sever, prune], inter_zero_left,Pi.zero_apply,smul_zero]; rfl
       rw [show sever (y 1) (0:Gen ℝ (Cover×α)) k=0 from funext fun i=>by simp [sever,prune],inter_zero_right,Pi.zero_apply,smul_zero]; rfl
    funext i; unfold whittle; simp_rw [hv]; funext j; simp only [Finset.sum_apply,worn,tie,Pi.zero_apply]; simp

section lights
variable {P Q A B: (I:Gear G)→ Rally k r I → Gen ℝ (Cloth (Helms I))}{s t : Gear G→ℝ}
lemma Satin.whirling (h:∀ I,s I≤I.s)(hp:∀ I,t I < s I)(ht:∀ I,0≤t I) (e:∀ j,Satin (largus k r) (smallus k r) s (fun i x=> P i x j) (fun i x=>Q i x j)) (q:∀ j,Satin (largus k r) (smallus k r) s (fun i x=>A i x j) (fun i x=>B i x j)) (i :ℕ):
     Satin (largus k r) (smallus k r) t (fun j x=> whittle x.P.payMat (P j x) (A j x) i) (fun j x=> whittle x.Q.payMat (Q j x) (B j x) i):=by
   unfold whittle; apply Satin.sum (fun I=>permits I k r); intro j hj
   obtain ⟨d,H⟩:= e (j.1+1); obtain ⟨D,H'⟩:= q (j.2+1)
   refine ⟨d+D,fun I=>?_⟩; obtain ⟨a,ha,hA⟩:= H I; obtain ⟨b,hb,hB⟩:=H' I
   let Z := pegPrice j.1 j.2; let K:=3*Z*I.D
   let X:= tiePay (Helms I) 2 (s I-t I)
   have hX:0≤ X:=by have he:= tieN_nn (α:=Helms I) (sub_pos.mpr (hp I)) 2; exact he
   have hk:0≤K:= mul_nonneg (by unfold Z; unfold pegPrice; positivity) (zero_le_one.trans I.bill_nn)
   refine ⟨K*a*b*X,by positivity,fun i'=>?_⟩
   let V:= i'.x
   have hy := loop_cap ((pm_rate i').mono (h I)) i'.θ (hp I) (ht I) (hA i') (hB i') (Finset.mem_antidiagonal.mp hj)
   change PairA _ (K* (a*V^d)*(b*V^D)*X) _ _ _ at hy; rw [pow_add,show i'.x=V from rfl,show K*a*b*X*_= _ from (show K*a*b*X*(V^d*V^D)=K*(a*V^d)*(b*V^D)*X by ring)]; exact hy
lemma Satin.crimping (h:∀ I,s I≤I.s)(hp:∀ I,t I<s I)(ht:∀ I,0≤t I) (i :ℕ)(e:Satin (largus k r) (smallus k r) s (fun j x=>P j x (i+2)) (fun j x=>Q j x (i+2))):
    Satin (largus k r) (smallus k r) t (fun j x=> crimp x.P.payMat (P j x) i) (fun j x=> crimp x.Q.payMat (Q j x) i):=by
   obtain ⟨d,H⟩:=e; refine ⟨d,fun I=>?_⟩; obtain ⟨a,hA,H⟩:= H I
   let T:=tiePay (Helms I) 2 (s I-t I); have he:0≤ T:=by have he:=tieN_nn (α:=Helms I) (sub_pos.mpr (hp I)) 2; exact he
   let U:=fareV i; have hh:0≤ U:=by unfold U fareV; positivity
   have hB:0≤I.D:=zero_le_one.trans I.bill_nn
   refine ⟨2*I.D*a*U*T,by positivity,fun v=>?_⟩
   have hz:= crimp_cap ((pm_rate v).mono (h I)) v.θ (hp I) (ht I) (H v)
   convert! hz using 1; unfold U T; ring

lemma Satin.parade (h:∀ I,t I≤I.s)(hp:∀ I,s I<t I)(ht:∀ I,0≤s I) (e₁ n k r:ℕ)
    (H:∀ v≤n,∀ e< e₁,∀ y,Satin (largus k r) (smallus k r) t (fun _ x=>x.P.rays v e y) (fun _ x=>x.Q.rays v e y)) (i): Satin (largus k r) (smallus k r) s (fun _ x=> curlJ x.P.payMat x.P.rays x.P.rays n e₁ i) (fun _ x=>curlJ x.Q.payMat x.Q.rays x.Q.rays n e₁ i):=by
   simp_rw [curlJ,Finset.sum_apply]; apply Satin.sum (fun I=>permits I k r); intro a ha; apply Satin.sum (fun I=>permits I k r); intro b hb; have ht₁:= Finset.mem_antidiagonal.mp ha; have ht₂:= Finset.mem_antidiagonal.mp hb
   by_cases hb₀ : b.1=0 ∨ b.2=0
   · have H (I: Gear G)(T: Stand I): whittle T.payMat (T.rays a.1 b.1) (T.rays a.2 b.2)=0:= trim_zero (by cases hb₀ with
       | inl hb=>rw [hb]; exact Or.inl (T.negative _)
       | inr hb=>rw [hb]; exact Or.inr (T.negative _))
     simp_rw [H]; exact Satin.zero
   exact Satin.whirling (P:=fun I x=>x.P.rays a.1 b.1) (Q:=fun I x=>x.Q.rays a.1 b.1) (A:=fun I x=>x.P.rays a.2 b.2) (B:=fun I x=>x.Q.rays a.2 b.2) h hp ht (H _ (by omega) _ (by omega)) (H _ (by omega) _ (by omega)) i

lemma Satin.flywheel (n e j k r:ℕ)(b:e< k ∨ e=k ∧ r<j+2*n)
    (s:Gear G→ℝ)(h:∀ I,s I<I.s)(hs:∀ I,0≤s I): Satin (largus k r) (smallus k r) s (fun _ x=> x.P.rays n e j) (fun _ x=>x.Q.rays n e j):=by
    induction n using Nat.strong_induction_on generalizing e s j with
    | h n ih=>
      cases n with
      | zero=> simp only [Nat.mul_zero, Nat.add_zero] at b
               simp_rw [Stand.rays,spurs,tide_zero]
               exact intones b hs h
      | succ n=>
        let t I:= s I+(Gear.s I -s I)/2
        have ht I:t I<I.s:= by unfold t; linarith [h I]
        have hs' I:s I<t I:= by unfold t; linarith [h I]
        have hw:= Satin.parade (fun I=>(ht I).le) hs' hs e n k r (fun v hv i hi r=> ih v (by omega) i r (Or.inl (by omega)) t ht (fun I=> (hs I).trans (hs' I).le)) j
        have hz:= Satin.crimping (P:=fun (I:Gear G) (x:Rally k r I)=>x.P.rays n e) (Q:=fun I x=>x.Q.rays n e) (fun I=> (ht I).le) hs' hs j (ih n n.lt_succ_self e (j+2) (show _ from by omega) t ht (fun I=> (hs I).trans (hs' I).le))
        simp_rw [Stand.rays,spurs,tide_rise]
        exact Satin.μ (Slate.one (P:=fun _=> (((n+1:ℕ):ℝ))⁻¹) (fun (I:Gear G)=> permits I k r)) (hz.add hw (fun I=>permits I k r))
end lights
end YM.WilsonCoeffUV.Bank
