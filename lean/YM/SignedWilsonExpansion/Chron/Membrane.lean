import YM.SignedWilsonExpansion.F9.Docket
/-! Actual cap with complex sum over rank stencils. Heads & equivalences for whole product before any finite-reg estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 660000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J I:Type*}{e k h m c v b N i j r d n :ℕ}
lemma growingK (g:G.Simple)(p:LocalRatio Ñ)(v:r≤ c)(w:c≤N)(h:d≤k)(X:Era G ℝ)(he:Auth d X) : cruises A Ñ N d c r X=cruises A Ñ N k c r X:=by
   induction v using Nat.decreasingInduction with
   | self=> simp [cruises_top]
   | of_succ i a ih=> rw [cruises_sub _ _ _ _ _ a,cruises_sub _ _ _ _ _ a, verseExpand A (a.trans_le w) g p (cruising _ g p a w he) h,ih]
-- namespace for Leg Lives
namespace Corps
variable [Fintype I][Fintype J]
variable (S:I→ Era G ℝ)(T:J→Era G ℝ)(s:I→ℂ)(t:J→ℂ)
def Lives (S:I→ Era G ℝ)(T:J→Era G ℝ)(s:I→ℂ)(t:J→ℂ): Prop := ∀ L: ℂ→ₗ[ℝ]ℝ, ∑ i,L (s i) • S i=∑ j,L (t j) • T j
-- **do not** pull complex-linear through measured votes
variable {P Q:Era G ℝ}
omit [Fintype I] [Fintype J] in
lemma priced (p:Auth i P)(q:Auth j Q) (x:ℝ): agateV (x • P) Q=x • agateV P Q ∧ agateV P (x • Q)=x • agateV P Q:=by
    have ht {P Q:Era G ℝ}{i j}(p:Auth i P)(q:Auth j Q): agateV (x • P) Q=x • agateV P Q:=by
       apply flash_recover ((p.μ x).manor q) ((p.manor q).μ _); intro n; rw [flashAgate (p.μ x) q]; simp only [ Prod.smul_fst,Pi.smul_apply ]; rw [flash_mu _ (p.span n), flash_mu _ ((p.manor q).span n), flashAgate p q, smul_mul_assoc] -- direction?
    exact ⟨ht p q,by rw [agate_swap p (q.μ x),agate_swap p q,ht q p]⟩
variable {S T s t}
lemma Lives.left (f:Lives S T s t)(p:∀ i,Auth k (S i))(q:∀ i,Auth k (T i))(h:Auth j Q)(x:ℂ):
    Lives (fun i=>agateV (S i) Q) (fun i=>agateV (T i) Q) (fun i=>s i*x) (fun i=> t i*x):=by
   intro L; let Z:=L.comp (LinearMap.mulRight ℝ x); have hx(v:ℂ): L (v*x)= Z v:=rfl
   simp_rw [hx]; have hQ:=congr_arg (agateV · Q) (f Z); rw [agate_left _ _ (fun i _=>(p i).μ _) h, agate_left _ _ (fun i _=>(q i).μ _) h] at hQ; simp_rw [(priced (p _) h _).1,(priced (q _) h _).1] at hQ; exact hQ
lemma Lives.right (f:Lives S T s t)(p:∀ i,Auth k (S i))(q:∀ i,Auth k (T i))(h:Auth j Q)(x:ℂ):
    Lives (fun i=>agateV Q (S i)) (fun i=>agateV Q (T i)) (fun i=>x*s i) (fun i=> x*t i):=by
   intro L; simp_rw [agate_swap h (p _),agate_swap h (q _),mul_comm x]; exact f.left p q h x L
section universep
variable {V Y: Fin (n+1)→ Type*} [∀ i,Fintype (V i)] [∀ i,Fintype (Y i)]
variable (P:(i: Fin (n+1))→V i→Era G ℝ)(s:(i:Fin (n+1))→V i→ℂ)(Q:(i: Fin (n+1))→Y i→Era G ℝ)(t:(i:Fin (n+1))→Y i→ℂ)
omit [Fintype I] [Fintype J] in
lemma extendV {R:Type*}[AddCommMonoid R] (F:((i:Fin (n+1))→ V i)→R):
     ∑ x,F x= ∑ i:V 0, ∑ j:(a:Fin n)→ V a.succ, F (Fin.cons i j):=by
    let U:((a:Fin (n+1))→ V a)≃ V 0 × ((a:Fin n)→ V a.succ):= {
        toFun x:=(x 0, Fin.tail x)
        invFun x:=Fin.cons x.1 x.2
        left_inv x:=funext fun i=> Fin.cases (by simp) (fun i=>by simp [Fin.tail]) i
        right_inv x:= by simp
    }; rw [←Equiv.sum_comp U.symm F,Fintype.sum_prod_type]; rfl
omit [Fintype I] [Fintype J] in
lemma dance (f:∀ i,Lives (P i) (Q i) (s i) (t i))(hp:∀ i j,Auth k (P i j))(hq:∀ i j,Auth k (Q i j)):
    Lives (fun x:(i:Fin (n+1))→ V i=> MassP G ℝ n (fun i=> P i (x i)))
      (fun x:(i:Fin (n+1))→ Y i=> MassP G ℝ n (fun i=> Q i (x i)))
      (fun x=>∏ i,s i (x i)) (fun x=>∏ i,t i (x i)):=by
    induction n with
    | zero=> intro L; rw [extendV,extendV]; simp_rw [Fintype.sum_unique,Fin.prod_univ_succ,Fintype.prod_empty, mul_one,MassP,Fin.cons_zero]; exact f 0 L
    | succ n ih=>
       let Z:= (a: Fin (n+1))→ V a.succ; let Z':=(a:Fin (n+1))→ Y a.succ; let A(x:Z):= MassP G ℝ n fun i=> P i.succ (x i); let B(x:Z'):= MassP G ℝ n fun i=> Q i.succ (x i); let C (x:Z):=∏ i,s i.succ (x i); let D (x:Z'):=∏ i, t i.succ (x i)
       intro L; rw [extendV,extendV]; -- unfolding issues
       -- do products exact and Fin.tail
       have HX : ∑ x:V 0, ∑ i:Z,L (s 0 x*C i) • agateV (P 0 x) (A i)=∑ p:Y 0, ∑ j:Z',L (t 0 p*D j) • agateV (Q 0 p) (B j):=by
          rw [Finset.sum_comm]; calc
            _ = ∑ i:Z, ∑ j:Y 0, L (t 0 j*C i) • agateV (Q 0 j) (A i) := Finset.sum_congr rfl fun i _=> (Lives.left (f 0) (hp 0) (hq 0) ( MassP_auth _ (fun j=> hp j.succ _) ) _ L) -- elaboration
            _ = _ :=by rw [Finset.sum_comm]; have H:Lives A B C D:= ih _ _ _ _ (fun i=> f i.succ) (fun i j=> hp i.succ j) (fun i j=> hq i.succ j); exact Finset.sum_congr rfl fun j _=> H.right (fun i=> MassP_auth _ (fun j=> hp j.succ _) ) (fun i=> MassP_auth _ (fun j=> hq j.succ _)) (hq 0 j) _ L
       have Hp (x:V 0)(y:Z): (Fin.tail (fun i=> P i ((Fin.cons x y) i)))=fun i=> P i.succ (y i):= funext fun i=>by simp [Fin.tail]
       have Hq (x:Y 0)(y:Z'): (Fin.tail (fun i=> Q i ((Fin.cons x y) i)))=fun i=> Q i.succ (y i):= funext fun i=>by simp [Fin.tail]
       dsimp only [A,B,C,D] at HX; simpa only [MassP,Fin.prod_univ_succ,Fin.tail,Hp,Hq, Fin.cons_succ,Fin.cons_zero] using HX -- danger simp recursively infinite symbolic?
end universep
omit [Fintype I] [Fintype J] in
lemma goldZ {T:Type*}{K:Finset T}{S':T→Era G ℝ}(g:G.Simple)(u:LocalRatio Ñ)(b:r≤ c)(w:c≤N)(p:∀ i∈ K,Auth k (S' i))(z:T→ℝ): FadeRaw A Ñ N k r c (∑ i∈K,z i • S' i)= ∑ i∈K,z i • FadeRaw A Ñ N k r c (S' i):=by
       unfold FadeRaw; rw [cruises_gather _ _ b g u w (fun i hi=>(p i hi).μ _),dew_sum]; apply Finset.sum_congr rfl; intro i hi; rw [show cruises A Ñ N k c r (z i • S' i)= z i • cruises A Ñ N k c r (S' i) from ?_,dew_smul] -- elaboration issue
       induction b using Nat.decreasingInduction with
       | self=> simp_rw [cruises_top]
       | of_succ j t ih=> rw [cruises_sub _ _ _ _ _ t,cruises_sub _ _ _ _ (S' i) t,ih]; let x:=cruises A Ñ N k c (j+1) (S' i); simpa only [Finset.sum_singleton] using verse_sum A g (t.trans_le w) u (S:={i}) (P:=fun _=> x) (fun i _=> cruising _ g u t w (p _ hi)) (fun _=> z i)
lemma Leaves (h:Lives S T s t)(p:∀ i,Auth k (S i))(q:∀ i,Auth k (T i))(g:G.Simple)(u:LocalRatio Ñ)(b:r≤ c)(w:c≤N):
   (∑ i,s i • insertQ (FadeRaw A Ñ N k r c (S i)))=(∑ i,t i • insertQ (FadeRaw A Ñ N k r c (T i))):=by
   let Z:=FadeRaw A Ñ N k r c
   apply PowerSeries.ext; intro i
   have price (x:ℂ)(L:ℂ→ₗ[ℝ]ℝ)(b:ℝ): L (x*(b:ℂ))= L x * b:=by rw [mul_comm x,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
   have test (L:ℂ→ₗ[ℝ]ℝ) : L (coeff i (∑ j,s j • insertQ (Z (S j))))= L (coeff i (∑ j,t j • insertQ (Z (T j)))):=by
      simp only [map_sum,map_smul,inked,smul_eq_mul,price]; have he:= congr_arg (coeff i ∘ Z) (h L); simp only [Function.comp_apply] at he; unfold Z at he; simp only [goldZ g u b w (S':=S) (fun i _=>p i),goldZ g u b w (S':=T) (fun i _=>q i), map_sum,map_smul,smul_eq_mul] at he; exact he
   exact Complex.ext (test Complex.reLm) (test Complex.imLm)
end Corps
end YM.WilsonCoeffUV.Mer.Xa
