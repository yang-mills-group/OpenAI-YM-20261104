import YM.SignedWilsonExpansion.Stage.Spectrum
import YM.SignedWilsonExpansion.Dancer.Sweet
import YM.Pert.Asymptotics.RawAxis
/-! # Call physical §24 receipt on Basis Stocks and peer

F9 certificate translates unweighted nominations to Print.S Prunes. Any non-unit
substitution of arity then bought cheaply by linearity. Physical turn.f coordinates
 are projections on W.Frame afterwards.Here V. Keep asset clock symbols separate!
-/
set_option autoImplicit false
set_option maxHeartbeats 530000
noncomputable section
namespace YM.SignedWilsonExpansion.StageG
open Function Set Filter MeasureTheory Extraction Climb Spec Table Next.UVStress OPE.Levy Trace.Pilot PhysMS PhysMS.Frame
open MergeProof.East Next.Rank Ward Next.Rank.East Pert.Scale Maxwell Extra.FD PhysicalNext.Repeat.Legato Run Lattice FullVolume Cells Homes
open XSpace Commission Dancer Dancer.Motif Dancer.Supper Dancer.Drawing Asymptotics Dancer.Stitch PhysicalNext.Repeat.Quince.PreCost
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa MarqueQ MarqueQ.Crops MarqueQ.PorchK WilsonCoeffUV.Bank PathCost
open Wilson RG PowerSeries Purchases UVClock PurchVoice HalfRoof HalfRoof.Minty WardBin Source Labels Normalize
open FVA2 FVA2.Dframe SeatsW Shell Dancer.Shell Dancer.Fort XSpace.Cirrus
open scoped Topology ContDiff Classical BigOperators
variable {G:Gauge} {d :ℕ}{X:Initialize G}{ι:Type}{ℱ:Filter ι}{A:Credit}
section one
variable (C:Family G) {Q:∀ h,Rays G h X.hol}{Ω:Council C.labels} {b:BeamT C}
variable {z h e k i:ℕ} -- fix order metavars
variable {u d':ℕ} {R: Realm G (e+1) A}
variable {f:Extraction.Order} (S:(Bel C.book).Hierarchy) (H:C.Makes)
variable {Y:ι→ℝ}{b:ι→BeamT C}{z:ι→PorchK X C.labels Q Ω R h k u}{ρ r Q':ι→ℝ}{N p j l B:ι→ℕ}
variable {Aq:ι→ (t:ℕ)→ C.label t≃ₗ[ℂ] C.label t}(T:Tune z S f d' b N p j l Aq ℱ r ρ Q' Y)(hl: (j+l) =ᶠ[ℱ] B)(U:0<d)(w:d≤d')
include T U w hl H
lemma recoversW (S':SectionData (C.labels.level d))(x:ι→Sec G d) : ∀ᶠ i in ℱ,
    (z i).resource S' (Costume b N p j l Aq r ρ i d (x i))= glowing C d (j i) (N i) (p i) (B i) (standardV b N p r ρ (x i) i) (Aq i d):=by
    filter_upwards [respects S f b N p j l Aq z H T U w, T.warm,T.aligned,T.rise,hl] with i hi hp hY hu hx
    rw [hi]; let y:= (Costume b N p j l Aq r ρ i) d (x i); let κ:=ρ i; have he':0<κ:= hu.trans_le hp.1; unfold resource curved τF furnace glowing states qKey; rw[ MarqueQ.PorchK.duty,billSize,hY, ← hx, keyQ,map_smul,map_smul,smul_smul,smul_smul] -- maybe keyQ order
    congr 1; let c:=C.S.a ((j+l) i); have h0:(c:ℂ)≠0:=Complex.ofReal_ne_zero.mpr ( C.S.a_pos _ ).ne'; have hκ:(κ:ℂ)≠0:=Complex.ofReal_ne_zero.mpr he'.ne'; have hu:(r i:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hu.ne'
    change (( ((↑ ((c/r i)^d)⁻¹ :ℂ) )) * (↑ ( κ/r i):ℂ)^d * ((κ:ℂ)^d)⁻¹)=(c^d:ℂ)⁻¹
    push_cast; field_simp; rw [div_pow,div_pow]; ring

end one
end YM.SignedWilsonExpansion.StageG
