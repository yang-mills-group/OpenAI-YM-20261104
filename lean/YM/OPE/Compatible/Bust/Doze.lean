import YM.OPE.Compatible.Bust.Frag
/-! # ∞ on cover at harmonic zero. before H images directed. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Float
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra RG Work.F08 Matrix
open scoped Topology BigOperators Classical
open Cascade Terp Paver Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
variable {I K E F X:Type}{m r i j n k:ℕ}{C D:ℝ}{N:Side}{v:Train r}{G:Gauge} {L:KernelChoices}
def atlasF (G:Gauge)(v:Train r)(h:4 ≤ r)(L:KernelChoices):RowB (Shade G) where
    val i j k:= if i.2=j.2 then Spill L v h (coord i.1) (coord j.1) k else 0
    fare:=(terra_money L h).choose
    positive:=(terra_money L h).choose_spec.1
    lease i j k:=by
         split
         next he=> exact le_of_tendsto ((guessed (C:=L) v h _ _ _).norm) (Eventually.of_forall fun t=> (terra_money L h).choose_spec.2 v (tick2 t) _ _)
         next hx => rw [norm_zero]; exact (terra_money L h).choose_spec.1
noncomputable def pointAt (G:Gauge)(v:Train r)(h:4≤r)(L:KernelChoices)(n:Side):RowB (Shade G) where
    val i j k:= if i.2=j.2 then vein v L (coord i.1) (coord j.1) k n 0 else 0
    fare:=(terra_money L h).choose
    positive:=(terra_money L h).choose_spec.1
    lease i j k:=by split; exact (terra_money L h).choose_spec.2 v _ _ _; rw [norm_zero]; exact (terra_money L h).choose_spec.1
lemma farN (G:Gauge)(u:X→Side)(v:Train r)(h:r≥4)(L:KernelChoices) {f:Filter X} (hp:Tendsto (fun i=> (u i).val) f atTop): Dull f (fun i=>pointAt G v h L (u i)) (atlasF G v h L):=⟨⟨_,(atlasF G v h L).positive,Eventually.of_forall fun _=> le_rfl⟩,fun a b x=>by
    unfold pointAt atlasF; dsimp only; split_ifs; exact old_coin hp v h ..; exact tendsto_const_nhds⟩
noncomputable def Cot (C:KernelChoices)(G:Gauge)(v:Train r)(n:Side): Mat (Tab (Shade G) n):=(PhV C v G n).submatrix (station G n) (station G n)
lemma slipF (A:Row (TypeFace 1) (TypeFace 1))(p q x y: Site N)(i j: TypeFace 1)(h:p-q=x-y): lineC A N (p,i) (q,j)=lineC A N (x,i) (y,j):=by unfold lineC realOf; rw [Matrix.map_apply, Matrix.map_apply,spectral_apply,spectral_apply,h]
lemma formsC (v:Train r)(h:4 ≤ r)(x:Site N): Formed (pointAt G v h L N).val (Cot L G v N) x :=by
    intro a b i j; change (if i.2=j.2 then lineC (ShellRow L v) N (x+wrap N a,coord i.1) (x+wrap N b,coord j.1) else 0)=(if i.2=j.2 then vein v L (coord i.1) (coord j.1) (b-a) N 0 else 0); by_cases hp:i.2=j.2
    swap; · simp_rw [if_neg hp]
    rw [if_pos hp,if_pos hp]; apply slipF; rw [map_sub]; abel
end YM.OPE.Silt.Float
