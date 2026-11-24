import YM.MS.Motif.K2

set_option autoImplicit false
noncomputable section
namespace YM.MS.Motif
open Set Filter Function Finset MeasureTheory Metric Real
open Plane Koszul Heat Flux Landau Arts Native
open Complex (I)
open scoped Topology ContDiff InnerProductSpace
variable {G:Gauge} {n:ℕ} {V:Mield G n} {F:Rack G n}
local notation "S" => field ( Landau.parity ( A:=Arts.L n ) (C:=G.ColorIndex))
lemma m_sp (h: Symm S F)(V: SectorP n→+ℂ): Symm S ( moment V F ):= by intro l i j k; simp_rw [moon,net_append,net_cons, add_left_comm i.2, h l i j k]; ring_nf
lemma mono_sym (i j:Arts.L n)(c:G.ColorIndex): Symm S (F₀ i j c):= by apply Symm.sub (m_sp (F:= A n G j c) (note_sym (at_g j c) (fun _=>1)) _) (m_sp (F:= A n G i c) (note_sym (at_g i c) (fun _=>1)) _) -- note_sym .. danger
end YM.MS.Motif
