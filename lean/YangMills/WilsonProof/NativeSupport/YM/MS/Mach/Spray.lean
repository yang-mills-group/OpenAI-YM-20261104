import YM.MS.Mach.Spray
import YangMills.WilsonProof.NativeSupport.YM.MS.Mach.Pol
/-!
# Local ∂A^xi identity for gauge invariant contractions (G any component). Scatter traces. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Mach
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Garment Color Book Convolve Signal Dock Emit Rock Path Oceans
open _root_.YM.MS.Shine Hem Mell Motif Literal Halo Alps Native
open scoped Topology ContDiff InnerProductSpace
variable {J:Type}{G:Gauge} {k s n:ℕ}{z:ℂ}{F H:Rack G n}{x y:ℝ→ Rack G n}{U Y:Mield G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
local infixl:68 "⋄" => product S
local notation "g"=> cwave n G
local notation "Δ"=> Motif.dot (applyS z G n)
-- aggregate. $−z g_k • ...$ to match gauge Lie deriv. Use full Schwinger.BR
lemma tail_shutdown (h:Safe F z)(ht:∀ i:G.El,repeatC i F=F): tree parity (Wick.D0 G n) (ploy G z n) F=0:= by
    obtain ⟨v,H⟩:=h.pulse; have hz : v=0:= by funext i w; apply HasDerivAt.unique (H.guardC i w); simp_rw [ht]; exact hasDerivAt_const (0:ℝ) _
    rw [ hearth (H:=F) (F:=ploy G z n) ( ploy_p z ), show shoots true (ploy G z n) F=0 from shoots_off (H:=ploy G z n) (b:=false) h.off, add_zero ]; unfold ploy; rw [ Motif.pulse (application z) (core_g z|>.2.1), H.law,hz]; simp [liftG]
namespace Safe
lemma add (h:Safe F z)(he:Safe H z): Safe (F+H) z:= by
    obtain ⟨u,hu⟩:=h.pulse; obtain ⟨v,hv⟩:=he.pulse;
    refine ⟨ h.sym.add he.sym,h.even.add he.even,(by intro i v; rw [map_add, h.off i v,he.off i v,add_zero]), u+v,?_,?_⟩; · intro k; simp_rw [map_add]; exact ( hu.guardC k ).add (hv.guardC k)
    rw [map_add,hv.law,hu.law]; simp [liftG,Finset.sum_add_distrib,smul_add]
lemma cash (h:Safe F z)(c:ℂ): Safe (c • F) z := by
    obtain ⟨v,hv⟩:= h.pulse; refine ⟨h.sym.smul _,h.even.smul _,(by intro i k; simp only [map_smul,h.off i k,smul_zero]), c • v,?_,?_⟩; · intro k; simp_rw [map_smul]; exact (hv.guardC k).scalar c
    rw [map_smul,hv.law]; simp only [liftG, Pi.smul_apply, map_smul,← Finset.smul_sum]; rw [smul_comm]
lemma cashR (h:Safe F z)(x:ℝ): Safe (x • F) z:= h.cash (x:ℂ)
lemma zero : Safe (0:Rack G n) z:= by
    rw [show (0:Rack G n)=coin 0 from (by funext i; cases i<;> rfl)]; exact free 0
lemma total {F:J→Rack G n}(V:Finset J)(h:∀ i∈V,Safe (F i) z): Safe (∑ i∈ V,F i) z:= by
   classical
   induction V using Finset.induction with | empty=> simp [zero]| insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih fun j hj=>h j (Finset.mem_insert_of_mem hj))
end Safe
end YM.MS.Mach
