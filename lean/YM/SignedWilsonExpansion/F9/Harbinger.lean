import YM.SignedWilsonExpansion.F9.CenterWarp
import YM.SignedWilsonExpansion.F9.Whisper
import YM.SignedWilsonExpansion.F9.Ferry
/-!
# Worker opening budget on primitive shelves (includes the larger ranks and powers)

We price the exact bridge first at bare and then at ℓ with the common recoil Clock.
`Metered` records one budget on a given sold (finite) menu, not just a subsequence. Later
witness constructed from the compact berth scene for all χ and shots.Write.T.F.
The top offset registered on cover is `σ ∈ x`, marks shift with that entire path (doesn't require
 that unpaid physical torus have its periodic inversion extension).
-/
set_option autoImplicit false
set_option maxHeartbeats 730000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Pill Cloth StationA
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{Ñ:ChartRatio G}{J:Type*}{e k h m c v b T N M i j l r p u n :ℕ}
variable {B Q D Z X Y η t a ρ d:ℝ}{E W U V:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
-- match on a given finite roster. `wire.Salmon` / weights linear scope.
section venue
variable {σ:Period}(K:σ.Tree) (L:Fin (n+1)→Cover)
abbrev PhaseAge (A:Levels G)(Ñ:ChartRatio G)(c l:ℕ)(k:ℕ)(P:Fin (n+1)→ Era G ℝ): InkQ:= insertQ (rear A Ñ c l c (FadeRaw A Ñ c ((n+1)*k) l c (embark P L))) -- notation κ shadow issue
abbrev LampNow (P:Fin (n+1)→ Bare.Series K G): InkQ:= Bare.normalized K G (∏ i,P i)
variable {A':Fin (n+1)→ J→ Era G ℝ}
local notation "lounge"=> Bare.Series K G
lemma PhaseAge.tabulates [Fintype J] (a:Levels G)(b:ChartRatio G)(g:G.Simple)(p:LocalRatio b)(u:l≤c)(f:∀ i j,Auth k (A' i j))(Y:Fin (n+1)→ J→Cost): PhaseAge L a b c l k (fun i=> ∑ j,trim (Y i j) (A' i j)) =
    ∑ x: Fin (n+1)→J,(∏ i,insertQ (Y i (x i))) * PhaseAge L a b c l k (fun i=> A' i (x i)):=by
    unfold PhaseAge; rw [seasonH A' L Y g p u (le_refl c) f]; simp_rw [map_sum,map_mul,map_prod,rear_toward _ u g p (le_refl c)]
lemma LampNow.tabulates [Fintype J] (Y:Fin (n+1)→ J → Cost)(P: Fin (n+1)→ J→ Bare.Series K G): LampNow K (fun i=> ∑ j,Bare.scalar K (insertQ (Y i j))*P i j)=
   ∑ x: Fin (n+1)→J,(∏ i,insertQ (Y i (x i))) * LampNow K (fun i=> P i (x i)):=by
    unfold LampNow; rw [Finset.prod_univ_sum,Fintype.piFinset_univ,map_sum]; apply Finset.sum_congr rfl; intro i _; rw [Finset.prod_mul_distrib, show (∏ j,Bare.scalar (G:=G) K (insertQ (Y j (i j))))= Bare.scalar K _ from (map_prod (PowerSeries.map (algebraMap ℂ (Bare.Vertices K G))) (fun j=>insertQ (Y j (i j))) _).symm,Bare.normalized_scalar]
lemma phase_meter [Fintype J] {U:ℝ}(B:ℕ)(a:Levels G)(b:ChartRatio G)(g:G.Simple)(p:LocalRatio b)(u:l≤c)(f:∀ i j,Auth k (A' i j)) (P:Fin (n+1)→ J→ lounge)(Y:Fin (n+1)→ J→ Cost) (Z:(Fin (n+1)→J)→ℝ)(z:∀ x:Fin (n+1)→J,FitsZ B (LampNow K (fun i=> P i (x i))-PhaseAge L a b c l k (fun i=> A' i (x i))) U) (w:∀ x, FitsZ B (∏ i,insertQ (Y i (x i))) (Z x)):
    FitsZ B (LampNow K (fun i=> ∑ j,Bare.scalar K (insertQ (Y i j))*P i j)-PhaseAge L a b c l k (fun i=>∑ j,trim (Y i j) (A' i j))) (∑ x: Fin (n+1)→J,(B+1:ℕ)*(Z x*U)):=by
    rw [PhaseAge.tabulates L a b g p u f,LampNow.tabulates,←Finset.sum_sub_distrib]; simp_rw [←mul_sub]; exact FitsZ.stack _ _ _ fun j _=> (w j).mul (z j)
-- Finset (Type0) roster primitive. Use this by demand via RegulatorIR.
structure Interior (K:σ.Tree)(L: Fin (n+1)→Cover)(A:Levels G)(Ñ:ChartRatio G)(e k c l:ℕ)(S:Finset (Xa.Use G k))(Z:ℝ): Prop where
   steps : ∀ f:Fin (n+1)→S, FitsZ e (LampNow K (fun i=> propose K (wrap σ.side (L i)) (f i).val.1.val)-PhaseAge L A Ñ c l k (fun i=>(f i).val.1.val.letter)) Z
-- move from the primitive theorem on a fixed menu to mirrored generalized operations.
variable (T:Fin (n+1)→ Cloth G k)
def wordDebt (e:ℕ)(S:Finset (Xa.Use G k)) : ℝ:=∑ f: Fin (n+1) → S, (((e+1:ℕ):ℝ)^(n+2))*(∏ i,|T i (f i).val|)
-- constants are numbers, rank shifts inside powers
abbrev inkLine (T:Cloth G k)(x:Xa.Use G k) : Cost:= T x • (PowerSeries.X ^ x.2)
lemma ticketLine (T:Cloth G k)(x:Xa.Use G k): FitS e (inkLine T x) |T x|:=by
   intro i h; unfold inkLine; rw [map_smul,norm_smul,coeff_X_pow]; split; simp; simp
lemma lightLine (x:Xa.Use G k)(T:Cloth G k)(o:σ.Sites): T x • (requesting K o k (Cloth.overC x.1.val x.1.property x.2))= Bare.scalar K (insertQ (inkLine T x)) * (propose K o x.1.val):=by
   rw [request_card]; let v:= T x; let c:= x.2; let P:= propose K o x.1.val; have hx:insertQ (inkLine T x)=PowerSeries.C (v:ℂ)*PowerSeries.X^c:=by
       have hp:inkLine T x=PowerSeries.C v*PowerSeries.X^x.2:=by unfold inkLine; rw [Algebra.smul_def]; rw [PowerSeries.algebraMap_apply]; rfl
       rw [hp,map_mul,map_pow]; simp only [insertQ,map_C,map_X]; rfl
   change v • _= _; have hp:Bare.scalar K (insertQ (inkLine T x))= Bare.scalar K (PowerSeries.C (v:ℂ)) * (PowerSeries.X^c : lounge):=by rw [hx]; unfold Bare.scalar; rw [map_mul,map_pow,map_X]
   rw [hp, SameV.self_power]; rw [show v • (_:Bare.Series K G)=(v:ℂ) • _ from (real_scalar_eq v _).symm, Algebra.smul_def]; exact (mul_assoc ..).symm
lemma broll (S:Finset (Xa.Use G k))(M:Cloth G k)(v:M.support⊆ S):
      M=∑ i: S, M i.val • Cloth.overC i.val.1.val i.val.1.property i.val.2:=by
    ext1 x; rw [Finsupp.finset_sum_apply]; simp only [overC]; change _=∑ i:S,M i.val • Finsupp.single i.val (1:ℝ) x
    by_cases h:x∈S
    · rw [Finset.sum_eq_single (⟨x,h⟩:S)]; · simp
      · intro i _ hi; rw [Finsupp.single_eq_of_ne (show x ≠ i.val from fun p=>hi (Subtype.ext p.symm)), smul_zero]
      simp
    rw [Finset.sum_eq_zero]; exact Finsupp.notMem_support_iff.mp (fun u=>h (v u))
    intro i _; rw [Finsupp.single_eq_of_ne (show x ≠ i.val from fun p=>h (p.symm ▸ i.property)),smul_zero]
lemma interior_usage (p:LocalRatio Ñ)(hG:G.Simple)(x:l≤c)(S:Finset (Xa.Use G k))(U:Interior K L A Ñ e k c l S Z)(v:∀ i,(T i).support ⊆ S):
    FitsZ e (LampNow K (fun i=> requesting K (wrap σ.side (L i)) k (T i))- PhaseAge L A Ñ c l k (fun i=> photo (T i))) (wordDebt (e:=e) T S * Z):=by
    let f i:=wrap σ.side (L i); let g(i)(j:S):= inkLine (T i) j.val; let P(_i:Fin (n+1))(j:S):= j.val.1.val.letter; let P'(i)(j:S):= propose K (f i) j.val.1.val
    have ht j:requesting K (f j) k (T j)=∑ i:S, Bare.scalar K (insertQ (g j i)) * P' j i:=by nth_rw 1 [broll S _ (v _)]; rw [map_sum]; exact Finset.sum_congr rfl fun i _=> by rw [map_smul]; exact lightLine K i.val (T j) _
    have hx i: photo (T i)= ∑ j:S, trim (g i j) (P i j):=by
        nth_rw 1 [broll S _ (v _)]; unfold photo; rw [map_sum]; exact Finset.sum_congr rfl fun j _=>by
            rw [map_smul]; have he:=sees_over (j.val.1.val) (j.val.1.property) j.val.2; change _ • photo _=trim (_ • _) _; rw [he,trim_lib]
    change FitsZ e (LampNow K (fun i=>requesting K (f i) _ (T i))-_) _; simp_rw [hx,ht]; let V(i)(u:S):= T i u.val
    let hb:= U.steps; let M':ℝ:=(e+1:ℕ)
    have hy(x:Fin (n+1)→ S): FitsZ e (∏ i,insertQ (g i (x i))) (M'^(n+1)*(∏ i,|V i (x i)|)):=by simpa only [Finset.card_univ, Fintype.card_fin] using (FitsZ.cum (e:=e) Finset.univ _ _ fun i h=> FitsZ.written (ticketLine (T i) (x i).val))
    apply (phase_meter K L e A Ñ hG p x (A':=P) (fun _ i=> i.val.1.val.solid.tall i.val.1.property) P' g _ hb hy).lift; unfold wordDebt; rw [Finset.sum_mul]; exact le_of_eq (Finset.sum_congr rfl fun i _=>by change M'*(M'^(n+1)*(∏ j,|V j (i j)|)*Z)=M'^(n+2)*(∏ j,|V j (i j)|)*Z; ring)
end venue
end YM.WilsonCoeffUV.Mer.Xa
