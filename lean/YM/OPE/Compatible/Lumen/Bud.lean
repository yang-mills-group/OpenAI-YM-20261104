import YM.OPE.Compatible.Lumen.Doses
/-!
# Solving boost divergence on orbit patch. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade
open Function Filter Set Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Score Libra Votive LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff Matrix.Norms.Frobenius RealInnerProductSpace
variable {G:Gauge}{n:Side}
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency Streamer
open PertExtension Series Asymptotics
attribute [local instance] Gauge.frobInner
namespace Score.Stand
variable {V D:Type}{o:V}{S:Score D V}[Fintype D]
local notation "XD" => Keys G D
variable (T:S.Stand ({o}:Set V))
abbrev gaugeRange (S:Score D V)(G:Gauge):= LinearMap.range (S.galaxy G)
def palmFrame (G:Gauge): Keys G T.Stable→ₗ[ℝ] Keys G D:= (T.dtex G).toLinearMap.comp (T.palmL G)
lemma pedestal (x: Keys G T.Stable):T.porch G (T.palmFrame G x)=x:=by rw [palmFrame,coe_comp,_root_.Function.comp_apply]; change T.porch G (T.dtex G _)=_; rw [T.porch_tex, T.porchMove]
variable [Fintype V]
include T
lemma vertical_span (x:Keys G T.Stable): T.palmFrame G x ∈ gaugeRange S G:= by
     let y:=T.palmL G x; obtain ⟨t,h⟩:= T.normal_arc y; change _+T.rollX (T.slab G (T.palmL G x))=_ at h; rw [T.slabMoveU,map_zero, add_zero] at h; exact ⟨t,h⟩
omit [Fintype D] [Fintype V] in
lemma harp (x:XD)(h:x∈gaugeRange S G)(hp:T.porch G x=0):x=0:= by
     obtain ⟨v,rfl⟩:= h; have hv(i:V):v i=v o:=by
        induction q:T.flick i using Nat.strong_induction_on generalizing i with
        | _ q ih=> by_cases he:i=o; · rw [he]
                   let a: ↥(({o}:Set V)ᶜ):=⟨i,he⟩; let p:=T.point a; have he:(S.galaxy G v) p.1=0:= congr_fun hp (⟨_,T.purity a⟩ : T.Stable)
                   change v _- v _=0 at he; have hh:=sub_eq_zero.mp he; have ha: v (S.start p)=v (S.lastV p):=by unfold start lastV;split; exact hh.symm;exact hh
                   rw [show i=S.start p from (T.root a).symm,ha]; exact ih (T.flick _) ((T.bump a).trans_eq q) _ rfl
     funext i; rw [show _= _ from (show S.galaxy G v i=v _-v _ from rfl),hv (S.inn i),hv (S.out i),sub_self];rfl
lemma harp_span (x:XD)(h:x∈gaugeRange S G):T.palmFrame G (T.porch G x)=x:=by
     let y:=T.palmFrame G (T.porch G x); refine sub_eq_zero.mp (T.harp (y-x) ((gaugeRange S G).sub_mem (T.vertical_span _) h) ?_); rw [map_sub,T.pedestal,sub_self]
end Score.Stand
end YM.OPE.Cascade
