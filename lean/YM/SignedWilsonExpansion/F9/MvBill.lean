import YM.SignedWilsonExpansion.F9.Taught
/-! # Through physical horizon Taylor past campaign and real coupled chart -/
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
variable {B Q D Z X Y η a ρ:ℝ}{E W WRED:Credit}{P:Era G ℝ}{R:Realm G (e+1) E}
local notation "κ'"=> ((n+1)*k)
namespace MarqueQ.Crops
open SignedWilsonExpansion.Commission MarqueQ MarqueQ.PorchK Asymptotics FPS
open Tape
variable {ι V':Type} {L:Filter ι}{g Y B T' I':ι→ℝ} {q q' :ι→InkQ}{x ν: ι→ℂ}
variable (h:Maxer L Y) (t:∀ᶠ i in L, |g i|≤1)(τ:ι→ℂ)(u:τ=O[L] g)
namespace Taught
variable {U:Type}[AddCommGroup U][Module ℂ U] [FiniteDimensional ℂ U]
variable (P:ι→Tape.Table U n)(Z:Fin n→ι→ℝ) (E:ι→Fin n→Tape U)
variable (p:Taught L Y g 1 τ k q x)(S:∀ i,constantCoeff (q i)=0)(hu:∀ a:Fin n→U,charge k L Y 1 (fun i=>Tape.archive (P i) a))
variable (V:∀ a:Fin n,∀ i≤k, Salary L Y (Z a) ℂ (fun j=>(E j a) i))
def citeS (k:ℕ)(t:ℂ) : Tape U →ₗ[ℂ] U := ∑ i∈Finset.range (k+1), t^i • LinearMap.proj (R:=ℂ) (φ:=fun _:ℕ=> U) i
abbrev invoke (S: Tape.Table U n)(k:ℕ)(τ:ℂ)(v:Fin n→ U):= calcT τ k (Tape.archive S v)

private lemma landed (u:Tape U)(t:ℂ)(B:Module.Basis (Fin d) ℂ U)(i:Fin d) : B.coord i (citeS k t u)=calcT t k (Tape.nearC B i u):=by rw [citeS,timed, LinearMap.sum_apply,map_sum]; refine Finset.sum_congr rfl fun j _=>?_ ; rw [LinearMap.smul_apply,map_smul,nearC_pay]; exact mul_comm ..
abbrev ruler (x:InkQ)(z:Tape (MultilinearMap ℂ (fun _:Fin n=> U) ℂ))(p:Fin n→Tape U): InkQ := tabular (composed z x) p
private lemma invoice (X:Tape U)(B:Module.Basis (Fin d) ℂ U)(k:ℕ)(t:ℂ): citeS k t X=∑ i:Fin d,calcT t k (nearC B i X) • B i:=by simp_rw [← landed]; exact (B.sum_repr _).symm
private lemma mvLedger (V:Tape.Table U n)(z:Fin n→ Tape U)(t t':ℂ)(N:Module.Basis (Fin d) ℂ U) : invoke V k t' (fun a=> citeS k t (z a))=∑ f:Fin n→Fin d,(∏ i:Fin n,calcT t k (nearC N (f i) (z i)))*calcT t' k (archive V (N ∘ f)):=by
   let X:= fun i v=> calcT t k (nearC N v (z i)); let T':= (∑ i∈Finset.range (k+1),t'^i • (V i)); have he(p:Fin n→ U):calcT t' k (archive V p)=T' p:=by unfold T'; rw [timed,_root_.sum_apply]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [archive,coeff_mk]; exact mul_comm ..
   unfold invoke; simp_rw [he, show ∀ i,citeS k t (z i)=_ from (fun i=> invoice (z i) N k t)]; rw [MultilinearMap.map_sum]; exact Finset.sum_congr rfl (fun i _=> T'.map_smul_univ (fun a:Fin n=>X a (i a)) (N ∘ i))
-- principal theorem whole operation.Retro
include h t u p hu V S
lemma manifests : Taught L Y g (∏ i, Z i) τ k (fun i=> ruler (q i) (P i) (E i)) (fun i=> invoke (P i) k (x i) (fun j=>citeS k (τ i) (E i j))):=by
     let J:=Module.finBasis ℂ U; let v:=Module.finrank ℂ U; let yₛ(i:Fin n)(l:Fin v)(j:ι):= Tape.nearC J l ( E j i ); let Xₗ(i:Fin n)(l:Fin v)(j:ι):= calcT (τ j) k (yₛ i l j); let E₁(f:Fin n→Fin v)(i:ι):= (Tape.archive (P i) (J ∘ f)).subst (q i); let Vₜ(f:Fin n→Fin v)(i:ι):= calcT (x i) k (Tape.archive (P i) (J∘ f)); let Tk(f:Fin n→Fin v):= (∏ i:Fin n,yₛ i (f i))* E₁ f; let Uₖ(f:Fin n→Fin v):=(∏ i:Fin n,Xₗ i (f i))* Vₜ f
     have hk (i:Fin n)(l:Fin v): Taught L Y g (Z i) τ k (yₛ i l) (Xₗ i l):= epoch h t τ u (by intro x hx; unfold yₛ; simp_rw [nearC_pay]; exact V i _ hx (J.coord l))
     have ht(f:Fin n→Fin v): Taught L Y g (∏ i,Z i) τ k (Tk f) (Uₖ f):= by simpa only [mul_one] using Taught.mul h t τ u (many h t τ u Finset.univ (fun i=>yₛ i (f i)) (fun i=>Xₗ i (f i)) Z (fun i _=> hk i (f i))) (shuffle h t τ u p (hu (J ∘ f)) S)
     have he:= postsum h t τ u _ Finset.univ _ _ (fun i _=> ht i)
     convert he using 1; swap; · funext i; rw [mvLedger (N:=J),Finset.sum_apply]; refine Finset.sum_congr rfl (fun f _=>?_); unfold Uₖ; rw [Pi.mul_apply,Finset.prod_apply]
     funext i; unfold ruler; rw [prices_ar _ _ J,Finset.sum_apply]; refine Finset.sum_congr rfl fun a _=>?_ ; unfold Tk; rw [Pi.mul_apply,Finset.prod_apply]; rw [← comp_clock _ _ (S i)]
-- Fee nearC.make finite.
end Taught
end MarqueQ.Crops
end YM.WilsonCoeffUV.Mer.Xa
