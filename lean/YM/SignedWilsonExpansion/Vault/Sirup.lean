import YM.SignedWilsonExpansion.Vault.Brandy
/-! # Serve ALL orders of F9 retention on actual expenses. Phase prices persist before extrapolation to hierarchy. -/
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
open Precision
section support
variable (Φ : ι→∀ i,Sec G ( D i ))
lemma drewM (y:capBox G D)(T:∀ i,SeatsW.Salary ℂ R 1 (fun v=> Φ v i)): (fun i=> feeM D ( Φ i ) y)=O[R] (1:ι→ℝ):=by
    have he:= IsBigO.finsetProd (s:=Finset.univ) ( fun i _=> T i ( ( Logo G ( D i ) ).coord ( y i ) ) ); simp only [Pi.one_apply,Finset.prod_const_one] at he; exact he
lemma wagesH (w:capBox G D→ℝ)(T:∀ i, SeatsW.Salary ℂ R 1 (fun v=> Φ v i)): (fun i=> priceY D ( Φ i ) w)=O[R] (1:ι→ℝ):=by
     apply IsBigO.sum; intro i _; exact (((drewM D Φ i T).norm_left).const_mul_left ( w i )).congr_left (fun j=> mul_comm ..)
lemma wagesU (T:∀ i,SeatsW.Salary ℂ R 1 (fun v=> Φ v i)): (fun i=>reserveH D ( Φ i ))=O[R] (1:ι→ℝ):= IsBigO.sum fun i _=> ( drewM D Φ i T ).norm_left
end support
section life
variable (P:ChartRatio G) (Υ B W:ι→ℝ) (Y:C.Makes)(g:ι→Fin (n+1)→ Cover)
variable (L:Filter ι) (x y:ι→∀ i,C.label ( D i )) (U:ι→ℝ) (N p f v r K:ι→ℕ)(su: Rise U L)
variable {q Q k b E d:ℕ}
abbrev payoutV (k q:ℕ)(i:ι):= calcT (↑(regulatorRun C (N i) (p i) (v i))) q (Crystal C P D ( y i ) k (N i) (p i) (f i) (K i) (v i) (g i) )
structure Lull (k q:ℕ) (u:ι→ℝ): Prop where
   tiny : (fun i=>natureL C D (g i) (x i) (f i) (N i) (p i) univ- born₀ C D (g i) (y i) (f i) (N i) (p i) (r i) (K i) univ)=o[L] u
   phase : (fun i=>shelterK C D (g i) (y i) (f i) (N i) (p i) (K i) univ- born₀ C D (g i) (y i) (f i) (N i) (p i) (r i) (K i) univ)=o[L] u
   oldest : (fun i=>born₀ C D (g i) (y i) (f i) (N i) (p i) (r i) (K i) univ-payoutV C D P g y N p f v K k q i)=o[L] u
   other  : (fun i=>born₀ C D (g i) (y i) (f i) (N i) (p i) (v i) (K i) univ-payoutV C D P g y N p f v K k q i)=o[L] u
structure Hot (d:ℕ): Prop where
   lit : ∀ᶠ i in L, Tilted C (stemK C D (g i) (y i) (f i) ( N i ) ( p i ) ( K i ) univ) ( doors C D ( f i ) ( K i ) ( p i ) ( g i ) ) ( N i ) ( priceV C d ( p i ) ( K i ) ( W i ) )
   any (e:ℕ): ∃ k>0, (fun i=> let J:=doors C D (f i) (K i) (p i) (g i); 16*priceV C d (p i) (K i) (W i)* ( allot C (K i) (N i) (p i) J )^(k+1)) =o[L] ((mark U)^e)
lemma Lull.step (w:Lull C D P g L x y N p f v r K k q U): (fun i=> natureL C D (g i) (x i) (f i) (N i) (p i) univ-payoutV C D P g y N p f v K k q i)=o[L] U:= ( w.tiny.add w.oldest ).congr_left ( fun i=> sub_add_sub_cancel .. )
private lemma anyFare (a b:ι→ℝ) (h: a=O[L] (1:ι→ℝ))(s: b=o[L] U): (fun i=> a i*b i)=o[L] U:=( h.mul_isLittleO s ).congr_right (fun i=>one_mul _)
variable (X:∀ᶠ i in L,Comb C D (g i) P (x i) (y i) Q d E (Υ i) (B i) (W i) k ( f i ) ( K i ) ( v i ) ( r i ) q ( N i ) ( p i ))
variable (budgetB: B=O[L] (1:ι→ℝ)) (snapU: Υ=O[L] (1:ι→ℝ))
include su Y X budgetB snapU
lemma niner (hs:G.Simple)(ht:b<Q)(hN:b<E) (a:Epoch L U C.path.levels f) (z:Epoch L U C.path.levels v) : Lull C D P g L x y N p f v r K k q ((mark U)^b):=by
    have u:= spendH C U L su b Q a ht; have pY:= anyFare L _ _ _ snapU u; let aZ (i):=regulatorRun C (N i) (p i) (v i); have hE:(b:ℝ)<E:= by exact_mod_cast hN
    have xL: (fun i=> aZ i^E)=o[L] ( ( mark U )^b ):= stretchP su b ( show E*(-1/2:ℝ)< b*(-1/2:ℝ) by linarith only [hE] ) (Wage.enroll ( Consume.power (n:=E) ((mark_tie su ( cutExposure su C hs Y z p ( X.mono fun i hi=> hi.beer.1.trans hi.beer.2.2.2.le ) )).isBigO.trans ( penMap su EventuallyEq.rfl ))))
    have hm:= anyFare L _ _ _ snapU xL; refine ⟨
        IsBigO.trans_isLittleO (IsBigO.of_norm_eventuallyLE (X.mono fun i hi=>?_)) (anyFare L _ _ _ budgetB u),
        IsBigO.trans_isLittleO (IsBigO.of_norm_eventuallyLE (X.mono fun i hi=>?_)) pY,
        IsBigO.trans_isLittleO (IsBigO.of_norm_eventuallyLE (X.mono fun i hi=>?_)) hm,
        IsBigO.trans_isLittleO (IsBigO.of_norm_eventuallyLE (X.mono fun i hi=>?_)) hm ⟩
    · exact hi.comparison
    · simpa only [one_div] using hi.phase
    · exact hi.sows
    exact hi.seed
omit budgetB snapU
lemma nectar (vw: W=O[L] (1:ι→ℝ)) (T:Epoch L U C.path.levels K)(Lmax:∀ i,( C.path.levels.budget i ).supportExponent=100): Hot C D W g L y U N p f K d:=by
     let t(i):= doors C D ( f i ) ( K i ) ( p i ) ( g i ); let J(i):= allot C (K i) ( N i ) (p i) (t i); let Yv:= X.mono fun i hi => hi.beer.2.2.2.le; let hX:= Eventually.of_forall (f:=L) (fun i=> boundD C D ( g i ) univ ( f i ) ( K i ) (p i)); have hA:∀ᶠ i in L,J i ≤1/4:= rebateS Y.wilson su T Yv t hX
     constructor
     · filter_upwards [X,hA] with i hi hp; refine tilted_at C _ _ _ _ Y hi.beer.2.2.2.le ?_ (stroke_env C univ _ _ _ _ ( plantK C D (g i) (y i) )) hi.buys hp; rw [( Y.wilson.represents ( N i ) ( p i ) ( K i ) hi.beer.2.2.2.le ).vac,Lmax ]; norm_num
     refine HeatS.reserve_ω (T:=d) Y.wilson su T Yv t hX (?_)
     exact ( vw.mul ( money_curve su T d ).1 ).congr' (EventuallyEq.rfl) ( Eventually.of_forall fun i=> one_mul _ ) -- infer exponent
omit X su Y in
lemma Hot.growing (k:ℕ) (X:Hot C D W g L y U N p f K d): ∃ e>0,(fun i=> let J':=doors C D ( f i ) ( K i ) ( p i ) ( g i ); let M':= C.path.rep ( N i ) ( p i ) ( K i ); let F':= stemK C D ( g i ) ( y i ) ( f i ) ( N i ) ( p i ) ( K i ) univ; Logwood.Slate (originalExterior C.path ( N i ) ( p i ) ( K i ) J') ( remit J' M' F' e ) - shelterK C D (g i) (y i) (f i) (N i) (p i) (K i) univ)=o[L] ( ( mark U )^ k ):=by
     obtain ⟨e,v,hV⟩:= X.any k; exact ⟨e,v, IsBigO.trans_isLittleO (IsBigO.of_norm_eventuallyLE (X.lit.mono fun i hi=> hi.tax e)) hV⟩
end life
end YM.Integration.HeartT.Spritz
