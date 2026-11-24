import YM.SignedWilsonExpansion.Kane.Portia
set_option autoImplicit false
set_option maxHeartbeats 480000
noncomputable section
namespace YM.Integration.Election
open RG RG.Supply Extraction PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Table Spec Climb Trace.Terrace Trace.Pilot
open Function Filter Lattice Wilson Source
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 FVA2 FVA2.Scale.Level Future
open SignedWilsonExpansion.Belfry SignedWilsonExpansion.Belle SignedWilsonExpansion.Dancer SignedWilsonExpansion.Belfry.Crisis SignedWilsonExpansion.Belfry.Classroom SignedWilsonExpansion.Belfry.ScaleFits
open SignedWilsonExpansion.Kane.Tilted Scale MS MS.Native MS.High MS.Land MS.Fleet Asymptotics
open PhysMS Frame Order Spin Next.UVStress OPE OPE.Orbits
open PowerSeries Register
open scoped BigOperators Topology Classical ContDiff
variable {G:Gauge}{R:Run G}{h:G.Simple}
-- shoe adapter & post. do not identify clocks by convergence theorem only.
namespace Frames
variable {n d b j:ℕ} {ι:Type} {l: Filter ι} {f:Extraction.Order} {S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
variable (lead : PhysMS.Leading F J){V:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{Q:MS.Land.Prescription (Press.portDeck G)} (Z:WilsonPrescription G){dial:Bool}(H: Main.Match Z h V Q dial)
local notation "W"=> WilsonPositionPrescribedFrame.positioned F J Z.store
local notation "Θ"=> WilsonPositionHomogeneousFrame.reading F J Z
local notation "K₀"=> WilsonPositionHomogeneousFrame.homogeneous F J Z -- parser test
open SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Belfry SignedWilsonExpansion.Dancer FVA2.Scale Scale.GroupS
variable (s:G.Simple)(ν:ℝ) (r g:ι→ℝ)(u:Tendsto r l trail)(price:FO l g)
open WilsonPositionHomogeneousComparison MeasureTheory
variable (T:Crest F J Z)(L:Leading F (WilsonPositionPrescribedFrame.positioned F J Z.store)){Y:(Bel R.family.book).Hierarchy}(p:∀d:ℕ,∀ᶠ i in trail, obedient F Y (J i) d){P:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin}(X:Scaling S)(ξ:Foundation F P)
local notation "T₀"=> ( Θ∘r )
local notation "Ω"=> ( Scale.Measure.outlook Z.scheme Z.criterion )
-- Estimate on ALL positions including ties. Uniform all viewers in cost. Museum.Limits fixed before this call.
include T p lead u H ξ X L
lemma alert (d n b:ℕ)(t:Tags G d n)(v:ι→Viewers F){U:Set (Points n)}(q:Roi U): Serves l (fun i x=> Seats K₀ r v i d n x t) ( fun i x=> mote (Ω d) b x ( T₀ i ) t ) U ( T₀ ^ b ):=by
    let Q:= H.details.toServed.toPosted.toQuoted; have E:= throughout L u Z.criterion h Z.scheme Q X ξ T.clock ( registered F J Z r u T ) v (fun i d=> Native Z (Θ ( r i )) d) ( mature F J Z H r u T.clock ) t q ( b:=b ); refine E.fix (?_) ( Eventually.of_forall fun i y _=>rfl ); filter_upwards [ postP ( h:=h ) F J lead Z r u p d ] with i hi y hy; change S.classMoment _ _ _ (fun j=> walk W _ _ (Native Z (Θ (r i)) d ( t j ))) = S.classMoment _ _ _ (fun j=> walk K₀ _ _ ( t j )); simp_rw [hi]
lemma phases (d b:ℕ)(x:Tags G d n){U:Set (Points n)}(A:Roi U) : Serves l ( fun (i:ι)(k: Viewers F × Points n)=> PlotW F K₀ k.1 ( r i ) d n k.2 x ) ( fun i (y:Viewers F × Points n)=> mote (Ω d) b y.2 ( T₀ i ) x ) ((Set.univ:Set (Viewers F)) ×ˢ U) ( T₀ ^ b ):=by
    intro ε he; classical
    let a(i:ι)(p:Viewers F):Prop:= ∀ t∈U,‖PlotW F K₀ p (r i) d n t x-mote (Ω d) b t (T₀ i) x‖≤ ε*‖T₀ i^b‖
    let v(i:ι):Viewers F:= if h:∃ p,¬ a i p then h.choose else none
    have H':∀ᶠ i in l, a i (v i):= alert F J lead Z H r u T L p X ξ d n b x v A ε he
    filter_upwards [ H' ] with i hi y hy
    have hu:a i y.1:=by
        by_contra hn
        have hz:∃ p,¬a i p:=⟨ _,hn⟩
        unfold v at hi; rw [dif_pos hz] at hi; exact hz.choose_spec hi
    exact hu y.2 hy.2
omit u X ξ p lead T L
include H
lemma polish (d b:ℕ)(v:Tags G d n)(r:ℝ)(x:Scale.Stage n): polynomial Z V ν d x v b r=mote (Ω d) b x.val r v :=by
    unfold polynomial mote; apply Finset.sum_congr rfl; intro p _; rw [ WilsonPositionHomogeneousComparison.filed Z V H,Jury.exactC (Ω d) x ]
include T p lead u ξ X L
lemma versions (d b:ℕ)(t:Tags G d n){U:Set (Points n)}(A:Roi U) : ∀ ε:ℝ,0<ε→ ∀ᶠ i in l, ∀ (x:Scale.Stage n),x.val∈U→ ∀ p:Viewers F, ‖PlotW F K₀ p ( r i ) d n x.val t - polynomial Z V ν d x t b ( Θ ( r i ) )‖ ≤ ε * |Θ (r i)| ^ b :=by
    intro ε he; filter_upwards [ phases F J lead Z H r u T L p X ξ d b t A ε he ] with i hi x hx P; obtain hw:(P,x.val)∈ ((Set.univ:Set (Viewers F))×ˢ U):=⟨Set.mem_univ _,hx⟩; rw [ polish Z H ν ]; exact (hi (P,x.val) hw).trans_eq (by simp[comp_apply,Real.norm_eq_abs,_root_.abs_pow]) -- name Real?
omit u
lemma formally (ν:ℝ)(d:ℕ)(v:Tags G d n)(U:Set (Points n))(A:Roi U)(b:ℕ): matchesThrough Z V F J ν d v U b:= fun ε he=> (versions F J lead Z H (l:=trail) ν id tendsto_id T L p X ξ d b v A ε he).mono fun i hi x hx=> hi x hx none
omit p T L ξ X lead
lemma externally (n d b:ℕ)(f:Test n)(u:Tags G d n) : ContinuousOn (fun x=> Jury.fxt (Ω d) x b u) (conf n) ∧ f.applyTo (fun x=> Jury.fxt (Ω d) x b u)=Scale.System.Readout Z.scheme Z.criterion V ν d b n f u:=by
     have hf:= H.transformedTest ν d; rw [ H.eqconv ν d ] at hf; exact ⟨ (( H.details.toServed.toPosted.toQuoted.toContract.smear ν d ).1.light _ _ _) ,( hf n b f u ).symm ⟩
lemma financed (d b:ℕ)(t:Tags G d n)(f:Test n)(r:ℝ): f.applyTo (fun x=> mote (Ω d) b x r t)=∑ i∈ Finset.range ( b+1 ),(r:ℂ)^ i*Scale.System.Readout Z.scheme Z.criterion V ν d i n f t:=by
    have hv(i:ℕ):= externally Z H ν n d i f t; simp_rw [ ← (hv _).2 ]; unfold Test.applyTo mote; simp_rw [ Finset.mul_sum,mul_left_comm ( f _ ) ((r:ℂ)^_) ]; rw [ integral_finsetSum ]; · simp_rw [ integral_const_mul ];
    intro i _; exact ( f.smearing ( hv i ).1 ).const_mul _
-- independent limit first THEN physics.cost. same θ.Power. True face assembly.V.Program shares scattering.
include p T L u ξ X lead
lemma smears (d b:ℕ) (t:Tags G d n) (φ:Test n) (v:ι→Viewers F) : ( fun i:ι=> φ.applyTo ( fun x=> PlotW F K₀ (v i) (r i) d n x t ) - ∑ j∈Finset.range (b+1), ( ( Θ ( r i ):ℝ ):ℂ )^ j * Scale.System.Readout Z.scheme Z.criterion V ν d j n φ t ) =o[l] ( T₀^b ):=by
     simp_rw [ ← financed Z H ν _ _ t φ ]; refine paidProfile φ ( alert F J lead Z H r u T L p X ξ d n b t v (Testi φ) ) ( ( u.eventually self_mem_nhdsWithin ).mono fun i hi=> ( Plot_neat (v i) hi t ).continuousOn ) (Eventually.of_forall fun i=>?_ ); apply continuousOn_finsetSum; intro j _; exact ( externally Z H ν n d j φ t ).1.const_mul _
omit p T L u ξ X lead
include ν
lemma PSRem (b d:ℕ)(x:Tags G d n)(t:ℝ)(φ:Test n): Tendsto (fun i=> ∑ j∈ Finset.range (b+1),(t:ℂ)^j * Scale.System.positions Z.scheme Z.criterion d ( Z.run.step i ) j n φ x ) atTop (𝓝 ( φ.applyTo ( fun y=> mote ( Ω d ) b y t x ) )):=by rw [ financed Z H ν d b ]; exact tendsto_finsetSum _ fun j _=> ( H.wilsonLimit ν n d j x φ ).const_mul _
end Frames
end YM.Integration.Election
