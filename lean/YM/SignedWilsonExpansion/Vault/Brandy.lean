import YM.SignedWilsonExpansion.Vault.Liquor
/-! # Full substitute funding at cap, charged TERM BY TERM on all faces. Converges
    for all field/placement-dependent admitted combinations with bounded coordinate costs,
    not requiring roots for a new family. Unit and any pattern of fired fields are admitted as
    full words (`Crystal`), giving one horizon for proper faces too. Core phase/router same.
-/
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.Integration.HeartT.Spritz
open Function Filter Finset MeasureTheory Extraction Climb Spec Table Next.UVStress Trace.Pilot PhysMS Maxwell Extra.FD
open OPE.Therm Lattice Wilson WilsonCoeffUV WilsonCoeffUV.Bank RG PowerSeries Asymptotics Gauge Source Labels
open SignedWilsonExpansion Homes Dancer Fort Stitch Purchases Purchases.PurchVoice UVClock Schedules HalfRoof StageG
open XSpace Commission WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa
open Logwood HeatS FVA1Physical.Exchange.F6Regular
open Exporter.Loans Pert.Asymptotics MarqueQ MarqueQ.Crops
open scoped Topology BigOperators ContDiff Classical
open XSpace.Normalize FVA2 FVA2.Dframe XSpace.Cirrus
variable {G:Gauge}{d m i f k K v N p q Q j r a n:ℕ} {S:Schedule}{ι:Type}{R:Filter ι}{Ψ:ι→ℝ}
variable (C:Family G)(D:Fin (n+1)→ℕ)(g:Fin (n+1)→ Cover)
open Cells
lemma awSum {σ:Type*} (s:Finset σ)(K N p:ℕ)(t:K<N)(Y:C.Makes) (F:σ→ Config G (C.side (K+1) p)→ℂ)(h:∀ i,Envelope (F i)) (c:σ→ℂ)(U:Config G ( C.side K p )) :
    actualAverage C (N:=N) (∑ i∈s,c i • F i) U=∑ i∈s,c i*actualAverage C (N:=N) (F i) U:=by
     let x:=F; let W:=∑i∈s,c i•F i; let w(i:σ):= c i • F i; have hp i : Envelope (w i):= envP ( ⟨ measurable_const,_, fun a=>le_refl ‖c i‖⟩ : Envelope (fun _ : Config G ( C.side ( K+1) p)=> c i ) ) ( h i )
     rw [ Finset.sum_congr rfl (fun i (_:i∈s)=> ( actualAverage_complex_mul C (N:=N) ( F i ) (c i) U ).symm ) ] -- rewrites right only?
     change actualAverage C (N:=N) (∑i∈s,w i) U=∑i∈s, actualAverage C (N:=N) (w i) U; unfold actualAverage; rw [ ← integral_finsetSum _ (fun i _=>actualAverage_integrable C Y t ( hp i ).meas.aestronglyMeasurable ( hp i ).cost.choose_spec U ) ]; simp_rw [Finset.sum_apply,Finset.smul_sum]
lemma paddle {σ:Type*} (s:Finset σ)(F:σ→ Config G ( C.side K p)→ℂ)(M:(j:σ)→ Envelope (F j))(Z:σ→ℂ)(h:v≤K)(k:K≤N)(Y:C.Makes) (U:Config G ( C.side v p )) : actualTransport C (N:=N) (∑ i∈s,Z i•F i) h U=∑ i∈s, Z i * actualTransport C (N:=N) (F i) h U:=by
     induction h using Nat.decreasingInduction with
     | self=> simp_rw [actualTransport_base C Y k,Finset.sum_apply]; rfl
     | of_succ w p ih=>
       simp_rw [actualTransport_step C Y k _ p]; have he:actualTransport C (N:=N) (∑ i∈s,Z i•F i) p=∑i∈s,Z i • actualTransport C (N:=N) ( F i ) p:=funext fun i=>by rw [ih,Finset.sum_apply]; rfl
       rw [ he ]; exact awSum C s w N _ (p.trans_le k) Y _ (fun i=>(flow_salary C Y k p).around _ (M i)) Z _
-- Deposit algebra.Clock.A.Boot.CleanT.Ops
open Precision
variable (P : ChartRatio G)
abbrev capBox (G:Gauge)(D:Fin n→ℕ):= (i:Fin n)→ Toon G (D i)
abbrev packedQ (Φ':capBox G D)(i:Fin (n+1)):= Logo G (D i) (Φ' i)
abbrev feeM (Λ:∀ i,Sec G (D i)) (Φ':capBox G D) :ℂ:= ∏ i:Fin (n+1), (Logo G (D i)).coord (Φ' i) (Λ i)
private lemma deposit {V:Type*}[AddCommGroup V][Module ℂ V] (W:MultilinearMap ℂ (fun i=> Sec G ( D i )) V)(x:∀i, Sec G ( D i )): W x=∑ f, feeM D x f • W (packedQ D f):=by
    nth_rw 1 [show x= ( fun i=> ∑ f:Toon G ( D i ), (Logo G (D i)).coord f (x i) • (Logo G ( D i )) f ) from funext (fun i=> ( ( Logo G ( D i ) ).sum_repr _ ).symm) ]; rw [ MultilinearMap.map_sum ]; exact sum_congr rfl fun _ _=> MultilinearMap.map_smul_univ ..
variable (X:∀ i,Sec G ( D i )→ₗ[ℂ] C.label ( D i ))(h:∀ i,Sec G ( D i ))
-- compiler.Crop shared. `Crystal` linear all.
abbrev infect (h:∀ i,Sec G ( D i )):= fun i=> X i ( h i )
private abbrev Versions (N p K:ℕ) (i: (t:Fin (n+1))→ (C.labels.level (D t)).Index) : MultilinearMap ℂ (fun i=> Sec G (D i)) ℂ:= ( MultilinearMap.mkPiAlgebra ℂ (Fin (n+1)) ℂ).compLinearMap fun j=>( LinearMap.proj (i j) ).comp ((( C.labels.level ( D j ) ).scaled ( Next.Rank.Price.shrink C K N p ) ).comp ( X j ))
lemma lucid (N p K k v f:ℕ): Crystal C P D (infect C D X h) k N p f K v g=∑ y,feeM D h y • Crystal C P D (infect C D X (packedQ D y)) k N p f K v g:=by
    -- use explicit def
    let x :=infect C D X; let J:Type:= (t:Fin (n+1))→ (C.labels.level ( D t )).Index; letI : Fintype J := Pi.instFintype -- maybe name
    let S0(i:J):=Versions C D X N p K i; let F(i:J) := insertQ ( MergeTrip.probeMany D (fun i=> C.localSection ( D i )) C.path.levels P N k v K (pine C.S f K g) i ); let hV(z): Crystal C P D ( x z ) k N p f K v g=∑ w:J,S0 w z • F w:= rfl; change Crystal C P D ( x h ) _ _ _ _ _ _ _=∑ i,_ • Crystal C P D ( x _ ) _ _ _ _ _ _ _; simp_rw [hV,Finset.smul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun i _=>?_; rw [ deposit D ( S0 i ) h, Finset.sum_smul ]; apply Finset.sum_congr rfl; exact fun _ _=>(smul_smul ..).symm
lemma volume (N p K f:ℕ)(U:Config G ( C.side K p )): stemK C D g (infect C D X h) f N p K univ U=∑ y, feeM D h y • stemK C D g (infect C D X (packedQ D y)) f N p K univ U:=
     deposit D (( MultilinearMap.mkPiAlgebra ℂ (Fin (n+1)) ℂ ).compLinearMap (fun i=> ( IsLinearMap.mk' _ ( letterK_lin (K:=K) ( N:=N ) (p:=p) C ( D i ) ( location C.S f K p ( g i )) U ) ).comp ( X i ))) h
lemma native (N p f:ℕ)(H:C.Makes): natureL C D g (infect C D X h) f N p univ=∑ y,feeM D h y • natureL C D g (infect C D X (packedQ D y)) f N p univ:=by
     simp_rw [ ← fullT C D g _ H ]; exact deposit D (( C.ensemble D _ ).compLinearMap X) h -- maybe
lemma integralL (N p K f:ℕ)(H:C.Makes) (hk:K≤N): shelterK C D g (infect C D X h) f N p K univ=∑ y,feeM D h y • shelterK C D g (infect C D X (packedQ D y)) f N p K univ:=by
    let F(y):= stemK C D g (infect C D X y) f N p K univ; have hp : F h=fun U=> ∑ y,feeM D h y • F (packedQ D y) U:= funext ( fun i=> volume C D g X h N p K f i ); letI:= probability (p:=p) H.wilson hk; have he y: Envelope ( F y ):= stroke_env C _ _ _ _ _ ( plantK C D g _ ); change Logwood.Slate _ (F h)=∑ y,_ • Logwood.Slate _ (F _); rw[hp]; unfold Logwood.Slate; rw [integral_finsetSum _ (fun i _=> ( show Integrable (fun x=> feeM D h i • F (packedQ D i) x) _ from (intE (he (packedQ D i)) _).smul (feeM D h i) )) ]; simp_rw [ integral_smul ]
lemma neutral (N p K f v:ℕ)(H:C.Makes)(hk:K≤N)(w:v≤K): born₀ C D g (infect C D X h) f N p v K univ=∑ y,feeM D h y • born₀ C D g (infect C D X (packedQ D y)) f N p v K univ:=by
    simp_rw [born₀,dif_pos w]; let F(y):= stemK C D g (infect C D X y) f N p K univ; change actualTransport C (N:=N) ( F h ) _ _=∑ y,_ • actualTransport C (N:=N) ( F _ ) _ _; rw [show F h= ∑ y,feeM D h y • F (packedQ D y) from funext (fun i=>by rw [ Finset.sum_apply ]; exact volume C D g X h N p K f i) ]; exact paddle C _ _ (fun i=> stroke_env C _ _ _ _ _ ( plantK C D g _ )) _ w hk H _
section room
variable (N p K L q Q k ν e f v c r:ℕ) 
/-- Proper full-mask faces all billed in SAME horizon purchase.L.No scaling expenditures replaced. -/
structure Comb (x y: ∀ i,C.label ( D i )) (Q d L :ℕ)(U B W:ℝ)(k f K v r q N p:ℕ): Prop where
    beer : v≤ K ∧ r≤v ∧ f≤ K∧ K<N
    buys : ∀U', ‖stemK C D g y f N p K univ U'‖ ≤ priceV C d p K W
    phase : ‖shelterK C D g y f N p K univ- born₀ C D g y f N p r K univ‖≤U*(1/(boilerM C f)^Q)
    comparison : ‖ natureL C D g x f N p univ- born₀ C D g y f N p r K univ‖≤B*((boilerM C f)^Q)⁻¹
    sows : ‖born₀ C D g y f N p r K univ-calcT (↑(regulatorRun C N p v)) q (Crystal C P D y k N p f K v g)‖≤U*(regulatorRun C N p v)^L
    seed : ‖born₀ C D g y f N p v K univ-calcT (↑(regulatorRun C N p v)) q (Crystal C P D y k N p f K v g)‖≤U*(regulatorRun C N p v)^L
open Precision
variable (B W:capBox G D→ Finset (Fin (n+1))→ℝ)
private lemma rowT {ι:Type*}{w:ℝ}(x:Finset ι)(c:ι→ℂ){a:ι→ℝ}(y:ι→ℂ)(ht:∀i∈x,‖y i‖ ≤ a i*w): ‖∑ i∈x,c i•y i‖≤ (∑i∈x,‖c i‖* a i)*w:=by rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i hi=>?_); rw [norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left (ht i hi) (norm_nonneg _)
private lemma duT {ι:Type*}{w:ℝ}(x:Finset ι)(c:ι→ℂ)(a:ι→ℝ)(A B:ι→ℂ)(ht:∀i∈x, ‖ A i-B i‖≤ a i*w): ‖ (∑ i∈x,c i•A i) - ∑i∈x,c i•B i‖≤(∑i∈x,‖c i‖*a i)*w:=by rw [←Finset.sum_sub_distrib]; simp_rw [←smul_sub]; exact rowT x c (fun i=>A i-B i) ht
abbrev reserveH (x: ∀ i,Sec G ( D i )) := ∑ i, ‖feeM D x i‖
abbrev priceY (x:∀ i, Sec G ( D i )) (b:capBox G D→ℝ):=∑ i, ‖feeM D x i‖* b i
private lemma trT {ι:Type*}{w:ℝ}(x:Finset ι)(c:ι→ℂ)(A B:ι→ℂ)(ht:∀i∈x, ‖ A i-B i‖≤ w): ‖(∑i∈x,c i• A i)-∑i∈x,c i• B i‖≤ (∑i∈x,‖c i‖)*w:=by simpa only [one_mul, mul_one] using duT (w:=w) x c (fun _=>1) A B ( fun i hi=> by simpa only [one_mul] using ht i hi )
variable (Y:∀ i,Sec G ( D i )→ₗ[ℂ] C.label ( D i )) (V:capBox G D→ precisionQ (n+1)) (A:∀ i:capBox G D, Spirits C P D (infect C D X (packedQ D i)) (infect C D Y (packedQ D i)) g Q e L (B i) ( W i ) k f c K v r q N p ( V i ))
lemma entire_port (hz:v≤c∧ c≤K∧ r≤v∧ f≤K∧ K<N) (H:C.Makes)(A:∀ i:capBox G D, Spirits C P D (infect C D X (packedQ D i)) (infect C D Y (packedQ D i)) g Q e L (B i) ( W i ) k f c K v r q N p ( V i )) : Comb C D g P (infect C D X h) (infect C D Y h) Q e L ( reserveH D h ) (priceY D h fun i=>B i univ) (priceY D h fun i=>W i univ) k f K v r q N p:=by
      have hv:= hz.1.trans hz.2.1; have hu:= hz.2.2.1.trans hv; let x:=infect C D Y; let k':=hz.2.2.2.2.le
      refine ⟨ ⟨hv,hz.2.2.1,hz.2.2.2.1,hz.2.2.2.2⟩,fun i=>?_, ?_,?_, ?_,?_⟩
      · rw [volume C D]; exact rowT univ _ _ (a:=fun t=>W t univ) (fun t _=> ( (A t).toast univ ).buys i)
      · rw [ integralL C D _ Y h N p K f H k', neutral C D _ Y h N p K f r H k' hu ]; exact trT univ _ _ _ (fun i _=> ( ( A i ).toast univ ).phase)
      · rw [ native C D _ X h N p f H, neutral C D _ Y h N p K f r H k' hu ]; exact duT univ _ ( fun i=> B i univ ) _ _ (fun i _=> ( ( A i ).toast univ ).comparison)
      · rw [neutral C D _ Y h N p K f r H k' hu, lucid C D _ P Y h,map_sum]; simp_rw [ map_smul ]; refine trT univ _ _ _ (fun i _=>?_); rw [ ← ( A i ).draught ]; exact ( ( A i ).toast univ ).sows
      rw [neutral C D _ Y h N p K f v H k' hv,lucid C D _ P Y h,map_sum]; simp_rw [ map_smul ]; refine trT univ _ _ _ (fun i _=>?_); rw [← ( A i ).draught]; exact ((A i).toast univ).seed
end room
end YM.Integration.HeartT.Spritz
