import YM.RG05Readout.Velvet.Gather
import YM.RG05Readout.Aligned.Columns
/-! Comparison on physical hull. Provides test error in same Qp.Text and phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Velvet
open Function MeasureTheory Set Filter Topology Pulse Native Address Many Lattice Wilson Extraction WithLp Nuclear Bay Cells Harvest Halls
open RG MergeProof Flatten PhysicalNext.Repeat Legato Dash Extraction.Lease Petals Push.RelayDifference
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
set_option quotPrecheck false
variable {G:Gauge}{C:Family G}{i m n j b d k ℓ t t' v o N p:ℕ}
    {Q q R r η ζ B':ℝ}(h:C.Makes){D:Address.Rail C}{ψ:ℕ→ℕ}{w:Bid.Worth}
  (A:OPE.Package C w ψ D)(hA:Storage C D)(hp:Cater C D) {f : Extraction.Order}{B:ℕ→ℕ→ℝ}
local notation "δ"=> C.S.a
local notation "I"=> Fin v
local notation "Φ'"=> Wave (Fin v)
local notation "a!"=> (C.S.a j/8)
variable (F:Wave (Fin v))(s: Fin v→ℕ)(x:(i:Fin v)→ Palette C (s i))
section
open Chalice
variable {b₀:ℕ→ℕ} (Y:∀ d:ℕ,Cutoffs→ Address.Emblems C d)
local notation "M1"=>rebases C n m d * mSeat C s Q m n o d t' ℓ k η q
local notation "M2"=>mBirth C s Q m n o d t' ℓ k η q j b
variable (hY:Chalice.Anchored D B h b₀ Y)(hh:∀ i:Fin v,b₀ (s i) ≤ b)(he:b₀ d ≤ b)
    (hR:∀ p:ℕ, Right C p n m j b k ℓ t t' d s q R (C.S.a j/8) η B' Q)
variable (hx:∀ i:Fin v,size (x i)≤ Q)
    (hF : Sky F R η)(hz:0≤ζ)(hZ:Tall F (o+1) 1 ζ)(ho: (∑ i:Fin v,(s i+2))+4*v < o+1)
local notation "R!"=>hears F s x Y n m b d N p q
-- ANY ordered sublimit; admissible Rights universal over all periods.Metric no arbitrary viewer fits width contour.
def Saw (n m b d:ℕ) (q:ℝ) (M:Palette C d)(φ: Filter Cutoffs): Prop:=∃ Z:Cutoffs→Palette C d, Tendsto Z φ (𝓝 M)∧ ∀ᶠ i:Cutoffs in φ, hears F s x Y n m b d i.1 i.2 q (Z i)
noncomputable def herald (V:Type*) (s0:V) (P:V→Prop) :V:=if h:∃ v,P v then h.choose else s0
lemma heraldV {V:Type*} (s0:V){P:V→Prop}(hp:∃ v,P v):P (herald V s0 P):=by rw [herald, dif_pos hp]; exact hp.choose_spec
noncomputable abbrev announced (n m b d:ℕ) (q:ℝ) (i:Cutoffs): Palette C d:=herald _ 0 (hears F s x Y n m b d i.1 i.2 q)
include h hY he A hA hp hF hR hZ hz hx ho hh
local notation "U"=> announced F s x Y n m b d q
lemma promising (N p:ℕ) (ht:m≤ N): hears F s x Y n m b d N p q (U (N,p)):=by
   obtain ⟨M,h_x,-⟩:= honorable h A hA hp F s x Y hY hh he hR hx hF hz hZ ho ht p; exact heraldV 0 ⟨M,h_x⟩
variable {l:Filter Cutoffs}[l.NeBot]
omit [l.NeBot] in
lemma predicted (hv:Tendsto (fun i:Cutoffs=> i.1) l atTop): ∀ᶠ i in l, hears F s x Y n m b d i.1 i.2 q (U i):=by
    filter_upwards [hv.eventually_ge_atTop m] with i hi using promising h A hA hp F s x Y hY hh he hR hx hF hz hZ ho i.fst i.snd hi
variable {ℱ:Ultrafilter Cutoffs}
lemma mailed (hU:(ℱ:Filter Cutoffs) ≤ f.fuse): ∃ M, Saw F s x Y n m b d q M (ℱ:Filter Cutoffs):=by
    have hv:=predicted h A hA hp F s x Y hY hh he hR hx hF hz hZ ho (cutoff_grows f); have hP:= paid_value h A hA hp F s x Y hY hh he hR hx hF hz hZ ho U hv; obtain ⟨p,h⟩:=bounded_ulim U _ ((hP.mono fun i hi=>(size_norm _).trans hi).filter_mono hU); exact ⟨p,U,h,hv.filter_mono hU⟩
omit [l.NeBot] in
lemma from_promised {M:Palette C d}(hw:Tendsto (fun i:Cutoffs=> i.1) l atTop)(hy:Saw F s x Y n m b d q M l): Tendsto U l (𝓝 M):=by
   obtain ⟨Z,hz₁,h_z⟩:=hy; apply hz₁.congr'; filter_upwards [h_z,predicted h A hA hp F s x Y hY hh he hR hx hF hz hZ ho hw] with i hi hE using hears_only h F s x Y hY he hi hE
lemma priced_limit {M:Palette C d}(hw:l ≤ f.fuse)(hy:Saw F s x Y n m b d q M l): ‖M‖ ≤ M1*ζ:=by
   let hv:=predicted h A hA hp F s x Y hY hh he hR hx hF hz hZ ho (cutoff_grows f)
   have he' := paid_value h A hA hp F s x Y hY hh he hR hx hF hz hZ ho U hv
   exact le_of_tendsto (from_promised h A hA hp F s x Y hY hh he hR hx hF hz hZ ho ((cutoff_grows f).mono_left hw) hy).norm ((he'.mono fun i hi=>(size_norm _).trans hi).filter_mono hw)
variable {T₀ T:YM.Table C.book}{L0:ℕ→YM.Table C.book}{R0:Dash.Bin T₀}{E':DiffPlan T} (H:Next.Extract.Base C f T₀ L0 R0 T E')(hS:∀ d,UVExt.Slots.StrongBin C R0 f d) (L:Poem C j)
variable (hG:G.Simple) {g:Extraction.Order} {Z:∀ d:ℕ,ℕ→Palette C d→ₗ[ℂ] C.label d} (hT:Petals.Tune (dims:=b₀) H Y g Z)
local notation "P!"=>fun (i:Fin v)=>fastU (Y (s i)) (fun _=>x i) m
include H hS hG hT
-- uniform as Ready at all phasers governed by this extraction.Frame.
lemma recites (hL:R*q < C.S.a j/2)(hθ:l ≤ (f.refine g).fuse){M:Palette C d}(hy:Saw F s x Y n m b d q M l):
    let p':=telegram L hF (hR 0|>.h) hL
    let v':=integrated p' s L.token (fun i=>Z (s i) m (x i)) T
    ‖(∏ _i:Fin v,(q:ℂ)⁻¹ ^4)*v'-Poem.passField L T H.kernel.smooth d (T.project d (Z d m M))‖ ≤ backing L h H.center d*(M2*ζ):=by
    intro p' v'; let t:=∏ _i:Fin v,(q:ℂ)⁻¹ ^4; have hw:=hθ.trans (Next.Extract.Tails.refine ..).fused; have hE:= (hR 0).hv.trans ((Nat.le_succ n).trans (hR 0).east.le); have hv:=predicted h A hA hp F s x Y hY hh he hR hx hF hz hZ ho (cutoff_grows f); have hf := from_promised h A hA hp F s x Y hY hh he hR hx hF hz hZ ho ((cutoff_grows f).mono_left hw) hy; let g'(i:Cutoffs):=physicalEra q F L.opening C m i.snd i.fst s (fun j=> P! j i); have hz': Tendsto (fun i:Cutoffs=>preamble L i.1 i.2 (g' i)) l (𝓝 (t*v')):=((choir h H b₀ Y hY hT A hA hG hS s (fun i _=>x i) x L.token p' hθ (fun _=>tendsto_const_nhds) (fun i=>⟨Q,Eventually.of_forall fun _=>hx i⟩) (fun i=>(hh i).trans hE)).const_mul t).congr (fun i=> (repaid F s L hF _ hL P!).symm)
    have hzT:=(Petals.Tune.projection h (U) H hS A hA hG Y (Anchored.tracks h _ _ hY) hT (he.trans hE) hθ hf ⟨M1*ζ,paid_value h A hA hp F s x Y hY hh he hR hx hF hz hZ ho (U) hv⟩).1 j L
    exact le_of_tendsto ((hz'.sub hzT).norm) ((allotment h A hA hp F s x Y hY hh he hR hx hF hz hZ ho U H.center L hv).filter_mono hw)
end
end YM.RG05Readout.Velvet
