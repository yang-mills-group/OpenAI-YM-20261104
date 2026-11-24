import YM.SignedWilsonExpansion.Public.Dazzle
import YM.SignedWilsonExpansion.Public.OverlapPrice
import YM.SignedWilsonExpansion.Dancer.PayNext
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Answer.ContinuumLimit
open Lattice RG MeasureTheory Function Filter Wilson Integration Integration.Election Climb Extraction Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.High MS.Native MS.Land MS.Fleet MS.Tide MS.Book PhysMS PhysMS.Frame Next.UVStress Order Spin OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale.Level FVA2.Scale SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Asymptotics WilsonPositionHomogeneousComparison
open PowerSeries XSpace.Cirrus Entree Future
open scoped BigOperators Classical ContDiff Topology
universe u
namespace Vision
variable {G:Gauge}{H:G.Simple}{e:Axis}{ε:ℝ}{O:OrderS G}{E:Construction.{u} H ε e O}{ξ:Extraction.Order}{V:Vision E ξ}
variable {Z:WilsonPrescription G}{dial:Bool}(Q:Perspective H Z dial)
open Frames Frames.Cortex -- order check
open Dancer Entree.Cup -- remove if trouble
open PowerSeries Scale Jury WilsonCoeffUV.Mer.Xa MarqueQ Crops
variable {Q} (M:Garnishes V Q)
variable {ι:Type}{l:Filter ι}{r:ι→ℝ}
variable (p:Tendsto r l trail){a:Bool} {n d:ℕ} {u:ι→Tags G d n} {b:ℕ} {U:Set (Points n)}
local notation "Ξ₀"=> ( V.T Z ∘ r )
local notation "Θ"=> ( Lamplight Z a d )
local notation "Ω"=> ( slotW Z V a )
local notation "𝕎"=> ( V.pupil )
local notation "Ω₀"=> ( V.pupil.last )
variable (B:Roi U) (P : ∀ j: Fin n,SeatsW.Salary ℂ l 1 (fun v=> u v j) )
open Belfry Belfry.Classroom ScaleFits Belfry.Crisis Scale.Level Scale.GroupS SeatsW
local notation "ℓ"=> Kane.Tilted.jump
variable [l.NeBot] (σ:Fin n→ι→ℝ)(cost :∀ j,FO l (σ j)) (ν:ℝ)
abbrev tab (Q:Perspective H Z dial)(V:Vision E ξ)(r:ι→ℝ)(a:Bool)(d:ℕ)(g:ι→ℝ)(ν:ℝ)(b:ℕ)(i:ι): FieldEnd G d:=if a then Crisis.gate d (g i) ( Levy ( gaugeN Z.scheme Z.criterion Q.MS ν ) ( V.T Z ∘ r ) g b i d ) else readyL (V:=Z.criterion) (Y:=Q.MS) ν ( V.T Z ∘ r ) g b i d
local notation "γ"=> ( fun i (j:Fin n)=> bend Ω (r i) ( ℓ r (σ j) i ) d )
local notation "δ"=> (fun i (j:Fin n)=> tab Q V r a d (σ j) ν b i)
local notation "U₀"=> ( fun i (j:Fin n)=> γ i j (u i j) )
local notation "U₁"=> ( fun i (j:Fin n)=> δ i j (u i j) )
include M p
lemma jumpMatrices (g:ι→ℝ)(h:FO l g): Salary ℂ l (Ξ₀^(b+1)) (fun i=> bend Ω (r i) ( ℓ r g i ) d-tab Q V r a d g ν b i) ∧ Salary ℂ l 1 ( tab Q V r a d g ν b ) :=by
     obtain ⟨T,P,L⟩:=nextPower M.accounts.calibrated p h ν d b; let X:= Q.matching.details.toServed.toPosted.toQuoted; have hz:Tendsto Ξ₀ l (𝓝 0):=( M.accounts.calibrated.calendar.clock.conforms H ).comp p; cases a; exact ⟨ P,mulE ( boundD h d ) ( yearCost hz ( checked Z.scheme Z.criterion X H ν h d )) ⟩; exact ⟨ L,mulE ( boundD h d ) ( yearCost hz ( checkedN Z.scheme Z.criterion X ν h d ) ) ⟩
include cost P
lemma homeLetters (k:Fin n): Salary ℂ l 1 (fun i=> U₀ i k ) ∧ Salary ℂ l 1 (fun i=> U₁ i k) ∧ Salary ℂ l (Ξ₀^(b+1)) (fun i=> U₀ i k - U₁ i k):=by
     obtain ⟨A,N⟩:= jumpMatrices (a:=a) (d:=d) (b:=b) M p ν (σ k) (cost k); have hv : Salary ℂ l 1 (fun i=> U₁ i k):= weave (P k) _ N; have hz:= weave ( P k ) _ A; change Salary ℂ l _ (fun i=> U₀ i k - U₁ i k) at hz; exact ⟨fun x=> ( ( ( hz x ).trans ( Wipe.powerT ( ( M.accounts.calibrated.calendar.clock.conforms H ).comp p ) IsEquivalent.refl (Nat.zero_le (b+1)) |>.congr_right fun i=> pow_zero _ ) ).add ( hv x ) ).congr_left (fun i=> by rw[map_sub,sub_add_cancel] ),hv,hz⟩
where
   weave {f:ι→ℝ} {u:ι→Sec G d} (T':SeatsW.Salary ℂ l 1 u)(Y:ι→FieldEnd G d) (t:SeatsW.Salary ℂ l f Y) : SeatsW.Salary ℂ l f (fun i=> Y i ( u i )):=by
     intro x; let B:= Module.finBasis ℂ (Sec G d); have he(i): x (Y i (u i))=∑ p, B.coord p ( u i ) * x ( Y i ( B p ) ):=by nth_rw 1 [← B.sum_repr (u i),map_sum,map_sum]; exact Finset.sum_congr rfl fun _ _=> by rw [map_smul,map_smul]; rfl
     simp_rw [he]; exact IsBigO.sum fun k _=> ((T' _).mul ( t ( x ∘ₗ LinearMap.applyₗ ( B k ) ))).congr_right fun i=>one_mul _
omit cost P p in
lemma layeredCard {θ:ι→ ℝ}(s:θ=O[l] (1:ι→ℝ))(H':Roi U)(d b:ℕ){a:Bool}(x:Tags G d n): (fun i:ι×Points n=> Path.mote (Lamplight Z a d ) b i.2 (θ i.1) x)=O[diners l U](1:ι×Points n→ℝ):=by
     let X:= Q.matching.details.toServed.toPosted.toQuoted; let A:=Lamplight Z a d; have he: Entree.regular A n:=by cases a; exact fun _ a=> Path.smooth_c Z.scheme Z.criterion X H a _; exact (X.toContract.smear 0 d).1.light n
     have ht: (fun i:ι×Points n=>(θ i.1:ℂ))=O[diners l U](1:ι×Points n→ℝ):=IsBigO.of_norm_left ( ( s.comp_tendsto ( plot_le (U:=U) ) ).norm_left.congr_left fun i=> ( Complex.norm_real _ ).symm ) -- IsBigO of norm!!
     unfold Path.mote; refine IsBigO.sum fun i _=> ( IsBigO.mul ( ht.pow i ) ( show (fun k : ι × Points n=> Jury.fxt A k.2 i x)=O[diners l U](1:ι×Points n→ℝ) from ?_ ) ).congr_right fun _=> Eq.trans ( show (1:ℝ)^i*1=_ from mul_one _ ) (one_pow _)
     obtain ⟨C,z⟩:=(H'.1.image_of_continuousOn (((he i x).norm).mono H'.2)).bddAbove; exact IsBigO.of_bound C ( plot_in.mono fun y hy => (z ( Set.mem_image_of_mem _ hy )).trans_eq ( by simp ) )
include B
abbrev lifeMany (Z:WilsonPrescription G)(V: Vision E ξ)(a:Bool)(r:ι→ℝ)(u:ι→Tags G d n)(F:Peers V)(i:ι)(x:Points n):ℂ:= V.pupil.S.classMoment ( spectator V.pupil.last F ) (fun _=>d) ((r i) • x) (fun j: Fin n=> walk ( slotW Z V a ) ( ℓ r (σ j) i ) d ( u i j ))
lemma magnates : ∃ C:ℝ,0<C∧ ∀ᶠ i in l,∀ ( F:Peers V ), ∀ x∈U, ‖lifeMany σ Z V a r u F i x - Path.mote Θ b x (Ξ₀ i) (U₁ i)‖ ≤ C* ‖Ξ₀ i ^(b+1)‖:=by
     let S(i:ι):= (U₀ i); let T (i:ι):= U₁ i; have h(y:Peers V)(i:ι)(x:Points n): lifeMany σ Z V a r u y i x=PlotW Ω₀ Ω y ( r i ) d n x (S i):= by change V.pupil.S.classMoment _ _ _ _=V.pupil.S.classMoment _ _ _ (fun j=> walk Ω ( r i ) d ( U₀ i j ) ); simp_rw [Tilted.swing]
     let C:= Cup.cup PUnit.unit; let V':PUnit→ι→Tags G d n:=fun _=> S; have he (j:Fin n):= homeLetters (a:=a) (b:=b) M p P σ cost ν j; obtain ⟨c,hc,W⟩:= ( stagewide (a:=a) ( b:=b ) M p C B (u:=V') ( fun _ j=> ( he j ).1 ) ).1; have hz: Tendsto Ξ₀ l (𝓝 0):= ( M.accounts.calibrated.calendar.clock.conforms H ).comp p; let Y(i:ι×Points n):= vis Θ (Ξ₀ i.1) b (n:=n) i.2; obtain ⟨c₁,h₁,k₁⟩:= ( matNext (Q:=Y) (v:= T ∘ Prod.fst) (p:=S ∘ Prod.fst ) (l:=diners l U) (S:=fun i=> ( Ξ₀ i.1 )^(b+1)) (fun x=> by simp_rw [ Y,vision ]; exact layeredCard M ( Wipe.stop hz ) B d b x ) (fun i u=> ((he i).2.1 u).comp_tendsto plot_le) (fun i u=> ((he i).1 u).comp_tendsto plot_le) (fun i u=> ((he i).2.2 u).comp_tendsto plot_le) ).exists_pos
     refine ⟨ c+c₁,by linarith,?_ ⟩; filter_upwards [diners_clause.mp k₁.bound,W] with i hi hx; intro F x hu; specialize hi x hu; specialize hx F x hu; dsimp only [comp_apply, Prod.fst,Prod.snd,Y] at hi; rw[vision,vision] at hi; unfold C at hx; rw[lighthouse] at hx; rw[h]; exact ( norm_sub_le_norm_sub_add_norm_sub _ _ _ ).trans ((add_le_add hx hi).trans_eq (add_mul c c₁ _).symm)
end Vision
end YM.Answer.ContinuumLimit
