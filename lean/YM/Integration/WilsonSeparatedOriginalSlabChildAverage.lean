import YM.Integration.WilsonSeparatedOriginalSlabChildCell
import YM.Integration.WilsonPositionSeparatedProfileCenteredMeasured

/-! The authentic repeated subcells of the older held centre are averaged with their true mass. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildAverage
open Function Set Finset MeasureTheory Lattice Wilson RG Source RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many Extra.Histories
open RG05Readout.Flatten RG05Readout.Pulse RG05Readout.Records PhysicalNext.Repeat.Legato RG05Readout.Nuclear
open scoped Classical BigOperators Topology

private theorem pitch (δ:E4)(r:ℝ):Native.pull δ r (Native.line Suede.pip)=Native.line Suede.pip:=by
  apply Subtype.ext;funext x;exact (Suede.static0 _ (δ+r • x)).trans (Suede.static0 _ x).symm

def average {I:Type*}[Fintype I](f:I → ℂ):ℂ:=(Fintype.card I:ℂ)⁻¹*∑i:I,f i

theorem priced {I:Type*}[Fintype I][Nonempty I](f h:I → ℂ){δ:ℝ}(paid:∀i,‖f i-h i‖≤δ):
    ‖average f-average h‖ ≤ δ:=by
  have pos:0<(Fintype.card I:ℝ):=by exact_mod_cast Fintype.card_pos
  rw [average,average,←mul_sub,←sum_sub_distrib,norm_mul,norm_inv,Complex.norm_natCast]
  calc _ ≤ (Fintype.card I:ℝ)⁻¹*∑i:I,‖f i-h i‖:=mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr pos.le)
    _ ≤ (Fintype.card I:ℝ)⁻¹*∑_:I,δ:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _=>paid i) (inv_nonneg.mpr pos.le)
    _ = δ:=by simp [pos.ne']

variable {G:Gauge}(R:Run G){N b per:ℕ}(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(top:b+1 ≤ N)

theorem held {r η X cap:ℝ}(rp:0<r)(room:r ≤ R.family.S.a (b+1))(ep:0<η)(small:η ≤ 1)(Ψ:Wave (Fin 3))
    (rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)(scatter:Scattering Ψ η)(xp:0 ≤ X)(sizeX:Tall Ψ (rank+1) 1 X)
    (shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖≤cap)(enclosed:r*cap+2*R.family.S.a b<R.family.S.radius per)(m:ℕ):
    actualTransport R.family (N:=N) (p:=per) (Pulse.constellation (p:=per) s v r Ψ (b.le_succ.trans top) m (Native.line Suede.pip)) (b.le_succ.trans top) 1=
      average (fun i:Bud R.family per b=>WilsonSeparatedOriginalSlabWholeProfile.whole R s
        (WilsonSeparatedOriginalSlabChildCell.sensor R s v top) r Ψ m (Native.line Suede.pip) (child R.family per b i)):=by
  have identity:=WilsonSeparatedOriginalSlabChildCell.original R (per:=per) s v top rp room ep small Ψ rank grade scatter xp sizeX shape enclosed m (Native.line Suede.pip)
  simpa only [Many.headFee,pitch,average] using identity

theorem dyes (date:b ≤ N)(F:Config G (R.family.side N per) → ℂ)(U:Config G (R.family.side b per)):
    Records.dyes R.family b N per date F U/liftVac R.family.path N per b U=actualTransport R.family (N:=N) F date U:=by
  simp only [Records.dyes,actualTransport,Complex.real_smul,Complex.ofReal_inv,liftVac,div_eq_inv_mul]

end YM.Integration.WilsonSeparatedOriginalSlabChildAverage
