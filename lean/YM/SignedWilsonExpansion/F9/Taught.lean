import YM.SignedWilsonExpansion.F9.Crops
/-! # Preserve through evaluating scalar occurrences -/
set_option autoImplicit false
set_option maxHeartbeats 630000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k m c v b N M i j l r d n :ℕ}
variable {B Q D Z X Y η a ρ:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
namespace MarqueQ.Crops
open SignedWilsonExpansion.Commission MarqueQ MarqueQ.PorchK Asymptotics FPS
variable {ι V':Type} {L:Filter ι}{g Y B T' I':ι→ℝ} {q q' :ι→InkQ}{x w_: ι→ℂ}
variable (h:Maxer L Y) (t:∀ᶠ i in L, |g i|≤1)(τ:ι→ℂ)(u:τ=O[L] g)
structure Taught (L:Filter ι)(Y g B:ι→ℝ)(τ:ι→ℂ)(k:ℕ)(q:ι→InkQ)(ν:ι→ℂ): Prop where
   price : charge k L Y B q
   value : Wage L Y B ν
   bill : Wage L Y (B * g^(k+1)) (fun i=> ν i- calcT (τ i) k (q i))
namespace Taught
include h t u
lemma mul (p:Taught L Y g B τ k q x)(v:Taught L Y g I' τ k q' w_): Taught L Y g (B*I') τ k (q*q') (x*w_):=by
    refine ⟨charge.mul h p.price v.price,Wage.mul p.value v.value,?_⟩; let X(i):= calcT (τ i) k (q i); let f(i):= calcT (τ i) k (q' i)
    have H:= Wage.plus h (B:=B*I'*g^(k+1)) ((Wage.mul (clockQ.chooseOne h t τ u _ p.price k le_rfl) v.bill).fix (.refl ..) (Eventually.of_forall fun i=>(mul_assoc ..).symm)) ((Wage.mul p.bill v.value).fix (.refl ..) (Eventually.of_forall fun i=>mul_right_comm ..))
    apply Wage.fix (Wage.plus h (clockQ.mulch h t τ u _ _ p.price v.price) H) (?_) (.refl ..) -- assignment stuck
    · exact Eventually.of_forall fun i=>by dsimp only [Pi.mul_apply]; ring
    
omit h t u in
lemma one (L:Filter ι)(Y g:ι→ℝ) : Taught L Y g 1 τ k 1 1:= ⟨fun i _=> Wage.unitC _, Wage.unitC _, by simp_rw [Pi.one_apply,calcT, LinearMap.comp_apply,trunc_one, AlgHom.toLinearMap_apply,map_one,sub_self]; exact Wage.nil⟩
lemma many (S:Finset J)(x:J→ι→InkQ)(ν:J→ι→ℂ)(B:J→ι→ℝ)(p:∀ i∈S,Taught L Y g (B i) τ k (x i) (ν i)): Taught L Y g (∏ j∈ S,B j) τ k (∏ j∈ S,x j) (∏ j∈ S,ν j):=by
    induction S using Finset.induction_on with
    | empty=> simp only [Finset.prod_empty]; exact one τ ..
    | @insert i s z ih=> simp only [Finset.prod_insert z]; exact Taught.mul h t τ u (p i (Finset.mem_insert_self ..)) (ih (fun j v=> p j (Finset.mem_insert_of_mem v)))
lemma epoch (p:charge k L Y B q): Taught L Y g B τ k q (fun i=> calcT (τ i) k (q i)):= ⟨p,clockQ.chooseOne h t τ u _ p k le_rfl,by simp_rw [sub_self]; exact Wage.nil⟩
lemma pow (p:Taught L Y g 1 τ k q x)(n:ℕ): Taught L Y g 1 τ k (q^n) (x^n):=by
    induction n with
    | zero=> simp only [pow_zero];exact one τ ..
    | succ n ih=> simp only [pow_succ]; simpa using Taught.mul h t τ u ih p
lemma postsum (B:ι→ℝ)(S: Finset J)(x:J→ι→InkQ)(ν:J→ι→ℂ)(p:∀ i∈S, Taught L Y g B τ k (x i) (ν i)): Taught L Y g B τ k (∑ j∈S,x j) (∑ j∈ S,ν j):=by
    constructor
    · intro i v; simp only [Finset.sum_apply, map_sum]; exact Wage.sum h _ _ (fun a b=> (p a b).price i v)
    · apply Wage.fix (Wage.sum h _ _ (fun i a=>(p i a).value)) (?_) (.refl ..); exact Eventually.of_forall fun i=> ( Finset.sum_apply .. ).symm
    simp_rw [Finset.sum_apply,map_sum,← Finset.sum_sub_distrib]; exact Wage.sum h _ _ (fun i w=> (p i w).bill)
lemma sprinkle (p:Taught L Y g B τ k q x){z:ι→ℂ}(v: Wage L Y I' z): Taught L Y g (I'*B) τ k (fun i=> z i • q i) (z*x):=by
    constructor
    · intro i b; simp only [map_smul]; exact Wage.mul v (p.price _ b)
    · exact Wage.mul v p.value
    simp only [map_smul,smul_eq_mul,Pi.mul_apply,← mul_sub]; simpa only [mul_assoc I'] using Wage.mul v p.bill
-- Core chart substitution.Crop exactly for ζ₀.Input. Coeffs summation.B.P not exchanged independent removal.
lemma shuffle (p:Taught L Y g 1 τ k q x){Z:ι→InkQ}(f:charge k L Y B Z)(e:∀ j,constantCoeff (q j)=0) : Taught L Y g B τ k (fun i=> (Z i).subst (q i)) (fun i=> calcT (x i) k (Z i)):=by
    let Q(j:ℕ) (i:ι): InkQ:= coeff j (Z i) • (q i)^j; let X(j:ℕ)(i:ι):ℂ:= coeff j (Z i)*(x i)^j; let A:= Finset.range (k+1); let P:=∑ i∈A,Q i; let N:=∑ i∈ A,X i; have hp : Taught L Y g B τ k P N:= postsum h t τ u B _ _ _ (fun i hv=> by
        have hx : X i= (fun a=>coeff i (Z a)) * x^i:= by ext1 j; simp only [Pi.mul_apply,Pi.pow_apply]; rfl
        rw [hx]; simpa only [Q,mul_one,Pi.pow_apply] using sprinkle h t τ u (B:=1) (pow h t τ u p i) (f i (by have hh:=Finset.mem_range.mp hv; omega)))
    have hx(i): N i=calcT (x i) k (Z i):=by unfold N; rw [timed, Finset.sum_apply]
    have he(i l)(w:l≤ k): coeff l ((Z i).subst (q i))= coeff l (P i):=by
       unfold P; rw [coeff_substituted (Z i) (e i),Finset.sum_apply,map_sum]; simp_rw [Q, map_smul]; refine Finset.sum_subset (Finset.range_mono (by omega)) (fun j h v=> (?_)); exact (congr_arg (coeff j (Z i) • ·) ((PowerSeries.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd ( PowerSeries.X_dvd_iff.mpr (e i)) j)) _ (by simp only [Finset.mem_range] at v; omega))).trans (smul_zero _)
    simp_rw [← hx]; refine ⟨fun i hi=> (?_),hp.value,?_⟩; · simp_rw [he _ i hi]; exact hp.price i hi
    have ht(i): calcT (τ i) k ((Z i).subst (q i)) = calcT (τ i) k (P i):=by rw [timed,timed]; exact Finset.sum_congr rfl fun j v=> congr_arg (fun z:ℂ=> z*τ i^j) (he i j (Nat.le_of_lt_succ (Finset.mem_range.mp v)))
    simp_rw [ht]; exact hp.bill
end Taught
end MarqueQ.Crops
end YM.WilsonCoeffUV.Mer.Xa
