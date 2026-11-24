import YM.SignedWilsonExpansion.Kane.Boot
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
local notation "Rψ" => (jump r g)
-- Frame criterion wrapped.Low-bank attaches existing Primary.Frame clocks & valuations.
-- Election.Material ∀finite tuition in one bill before choosing geometry.
structure Crest (Z:WilsonPrescription G): Prop where
     clock: Coupling G (WilsonPositionHomogeneousFrame.reading F J Z) -- explicit Z!
     school:Classroom.Primary trail ( levelOf F (WilsonPositionPrescribedFrame.positioned F J Z.store) id ) Z.scheme Z.criterion (WilsonPositionHomogeneousFrame.reading F J Z)
     paired:∀ (d:ℕ)(_:0<d){ι:Type}(l:Filter ι) [l.NeBot], handheld (WilsonPositionPrescribedFrame.positioned F J Z.store) F d l
variable (T:Crest F J Z)
open GroupS
local notation "T₀"=> ( Θ∘r )
local notation "G₀"=> ( Θ ∘ Rψ )
include T u
lemma registered : Classroom.Primary l ( levelOf F W r ) Z.scheme Z.criterion T₀:= SignedWilsonExpansion.Kane.Tilted.Primary.comp' Z.criterion Z.scheme u T.school
variable (L:Leading F (WilsonPositionPrescribedFrame.positioned F J Z.store))
include L price
local notation "σ₀" => Z.scheme
local notation "κ₀" => Z.criterion
local notation "ψ₀" => ( GroupS.ψ κ₀ V ν )
local notation "π₀" => ( gaugeB κ₀ V ν )
local notation "Ω₀" => ( gaugeN σ₀ κ₀ V ν )
local notation "A₀" => (fun (i:ι) (d:ℕ)=> bend W ( r i ) (Rψ i) d)
variable [nB:l.NeBot]
include nB
lemma arcT : Neighbors l ( levelOf F W r ) (levelOf F W Rψ) g A₀:= Patch_neighbor L u price fun _ hd=> T.paired _ hd _ -- param U
include H
variable (b1:0<b)
include b1
lemma guide (d:ℕ): SeatsW.Discount ℂ l ( T₀^b ) (fun i=> A₀ i d - readyL (V:=κ₀) (Y:=V) ν T₀ g b i d):=by
    have hx:Tendsto Rψ l trail:= recede price u; exact Classroom.limbs σ₀ H.details.toServed.toPosted.toQuoted ν h ( registered F J Z r u T ) ( arcT F J Z r g u price T L ) ( registered F J Z Rψ hx T ).pledge b d b1
variable {Y:(Bel R.family.book).Hierarchy}(p:∀d:ℕ,∀ᶠ i in trail, obedient F Y (J i) d)
include H u T L b1 nB price p lead
local notation "B"=> (fun (i:ι) (d:ℕ)=> bend K₀ ( r i ) (Rψ i) d)
lemma maturity (d:ℕ): SeatsW.Discount ℂ l ( T₀ ^ b ) (fun i=> B i d - Crisis.gate d (g i) ( Classroom.Levy Ω₀ T₀ g b i d )) ∧ ( G₀-Tone T₀ g ψ₀ b )=o[l](T₀^b):=by
    have hx:Tendsto Rψ l trail:= recede price u; let Q':= H.details.toServed.toPosted.toQuoted; have hθ:= mature F J Z H r u T.clock; obtain ⟨t,z⟩:= Crisis.overlap σ₀ Q' ν h hθ ( mature F J Z H Rψ hx T.clock ) b1 ( registered F J Z r u T ) ( registered F J Z Rψ hx T ) ( arcT F J Z r g u price T L ) d
    have hp: By ℂ l (fun i:ι=> Native Z (T₀ i) d ) 1:= Crisis.foundation σ₀ Q' ( ( T.clock.conforms h ).comp u ) hθ d; refine ⟨ ?_, z ⟩
    let p'(i:ι):= Native Z (T₀ i) d; let q(i):= Native Z (G₀ i) d; have hv:∀ᶠ i in l,p' i * B i d= A₀ i d * q i:=by
        filter_upwards [ postP (h:=h) F J lead Z r u p d, postP (h:=h) F J lead Z Rψ hx p d ] with i hi ht; ext1 t; apply (walk W (r i) d).injective; change walk W _ _ ( p' i ( B i d t ) )= walk W _ _ ( A₀ i d ( q i t ) ); rw [ swing ]; unfold p' q; simp only[ Function.comp_apply ]; rw [ ←hi,←ht ]; exact swing .. -- rw test
    let q'(T:Module.Dual ℂ (FieldEnd G d))(i:ι):= T ∘ₗ LinearMap.mulLeft ℂ (p' i); have hZ(T:Module.Dual ℂ (FieldEnd G d))(x:FieldEnd G d): Tendsto (fun i=> q' T i x) l (𝓝 (T x)):=by
        have H₀:= hp ( T ∘ₗ LinearMap.mulRight ℂ x ); rw[ LinearMap.comp_apply,show LinearMap.mulRight ℂ x 1=x from one_mul x ] at H₀; exact H₀
    refine Veto.guard (fun i h=> Veto.zero_guard (K:=ℂ) i h) (fun i T=> q' T i) hZ fun T=>?_ ; apply IsLittleO.congr' ( t T ) ( hv.mono fun i hi=>?_ ) (.refl ..); dsimp only; unfold q'; rw[LinearMap.comp_apply]; refine congr_arg T (?_); change A₀ i d * q i - ( p' i * Dial d (g i) ) * Classroom.Levy Ω₀ T₀ g b i d= p' i * ( B i d - Crisis.gate d ( g i ) _ ); rw [_root_.mul_sub (p' i),hi,mul_assoc]
end Frames
end YM.Integration.Election
