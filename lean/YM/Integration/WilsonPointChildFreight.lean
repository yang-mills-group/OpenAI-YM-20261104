import YM.FormalBulk08.Quire.Tons

/-! A single inherited tensor on its stepped input width. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPointChildFreight
open YM Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Reef Flat Lava Mesa Gorge Rift Aster Quire Next.Free
open scoped ENNReal BigOperators Classical

private theorem weight (σ θ B:ℝ) (v:ℕ) (hθ:0≤θ) (hh:θ≤1) (hB:1≤B):
    shine (θ*σ) v ≤ ENNReal.ofReal (B ^ θ) +
      ENNReal.ofReal (B ^ θ/B) * shine σ v:=by
  have b:0<B:=by linarith
  have power:B ^ θ=Real.exp (θ*Real.log B):=by rw [Real.rpow_def_of_pos b,mul_comm]
  by_cases cut:σ*(v:ℝ)≤Real.log B
  · apply le_trans _ (le_add_right (le_refl _))
    apply ENNReal.ofReal_le_ofReal
    rw [power]
    exact Real.exp_monotone (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left cut hθ)
  · apply le_trans _ (le_add_left (le_refl _))
    rw [shine,shine,←ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg b.le _) b.le),
      power,show Real.exp (θ*Real.log B)/B=Real.exp (θ*Real.log B-Real.log B) by
        rw [Real.exp_sub,Real.exp_log b],←Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_monotone (by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr (le_of_not_ge cut))])

theorem charged {V:Type*} {r:ℕ} (D:Reach V) (x:V) (T:Tile V r)
    {σ θ A B t:ℝ} (hθ:0≤θ) (hh:θ≤1) (b:1≤B)
    (hA:0≤A) (ht:0≤t)
    (weak:Knoxville D 0 x T (A*t)) (strong:Knoxville D σ x T (B*t)):
    Knoxville D (θ*σ) x T ((1+A)*B^θ*t):=by
  have bn:0<B:=by linarith
  have pow0:0≤B^θ:=Real.rpow_nonneg bn.le _
  have div0:0≤B^θ/B:=div_nonneg pow0 bn.le
  let q (v:chain V r):=wide D (Fin.cons x v:chain V (r+1))
  have w:(∑'v:chain V r,‖T v‖ₑ)≤ENNReal.ofReal (A*t):=by simpa only [shine_one,one_mul] using weak.2
  refine ⟨mul_nonneg (mul_nonneg (add_nonneg zero_le_one hA) pow0) ht,?_⟩
  calc (∑'v:chain V r,shine (θ*σ) (q v)*‖T v‖ₑ)
      ≤∑'v:chain V r,(ENNReal.ofReal (B^θ)+ENNReal.ofReal (B^θ/B)*shine σ (q v))*‖T v‖ₑ:=
        ENNReal.tsum_le_tsum fun v=>mul_le_mul_left (weight σ θ B _ hθ hh b) _
    _=ENNReal.ofReal (B^θ)*(∑'v:chain V r,‖T v‖ₑ)+
          ENNReal.ofReal (B^θ/B)*(∑'v:chain V r,shine σ (q v)*‖T v‖ₑ):=by
        simp only [add_mul,mul_assoc,ENNReal.tsum_add,ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal (B^θ)*ENNReal.ofReal (A*t)+ENNReal.ofReal (B^θ/B)*ENNReal.ofReal (B*t):=
      add_le_add (mul_le_mul_right w _) (mul_le_mul_right strong.2 _)
    _=ENNReal.ofReal ((1+A)*B^θ*t):=by
      rw [←ENNReal.ofReal_mul pow0,←ENNReal.ofReal_mul div0,
        ←ENNReal.ofReal_add (mul_nonneg pow0 weak.1) (mul_nonneg div0 strong.1)]
      congr 1
      field_simp
      ring

theorem interpolate {V:Type*} {r:ℕ} (D:Reach V) (x:V) (T:Tile V r)
    {σ θ A B:ℝ} (hθ:0≤θ) (hh:θ≤1) (b:1≤B)
    (weak:Knoxville D 0 x T A) (strong:Knoxville D σ x T B):
    Knoxville D (θ*σ) x T ((1+A)*B^θ):=by
  simpa only [mul_one] using charged D x T hθ hh b weak.1 zero_le_one
    (show Knoxville D 0 x T (A*1) by simpa only [mul_one] using weak)
    (show Knoxville D σ x T (B*1) by simpa only [mul_one] using strong)

variable {X:Type} {G:Gauge} {K:KernelChoices} {J t:X→ℕ} {F:∀i,Flight (J i) (t i)}
variable {U:∀i,Lodge (F i).patch} {ρ:ChartRatio G} {τ:Time X} {σ η:X→ℝ} {E:ℕ}
def fineWidth (F:∀i:X,Flight (J i) (t i)) (η:X→ℝ) (i:X):ℝ:=η i/(F i).L.val

theorem lowered (w:Freight F U ρ K τ σ η E): Freight F U ρ K τ (fineWidth F η) η E:=by
  refine {w with coverage:=fun i=>?_,input:=fun i=>?_}
  · have pos:0<((F i).L.val:ℝ):=by exact_mod_cast (F i).L.property
    unfold fineWidth
    rw [mul_comm,div_mul_cancel₀ _ pos.ne']
  · exact div_pos (w.output i) (by exact_mod_cast (F i).L.property)

theorem priced {Y:Type*} {r:ℕ} (w:Freight F U ρ K τ σ η E) (i:X) (D:Reach Y) (x:Y)
    (T:Tile Y r) {A B:ℝ} (hb:1≤B) (base:Knoxville D 0 x T A)
    (top:Knoxville D (σ i) x T B):
    Knoxville D (fineWidth F η i) x T ((1+A)*B^(fineWidth F η i/σ i)):=by
  have s:=w.input i
  have l:0<((F i).L.val:ℝ):=by exact_mod_cast (F i).L.property
  have small:fineWidth F η i≤σ i:=(div_le_iff₀ l).mpr (by simpa only [mul_comm] using w.coverage i)
  have width:0<fineWidth F η i:=(lowered w).input i
  have out:=interpolate D x T (div_nonneg width.le s.le) ((div_le_one₀ s).mpr small) hb base top
  rwa [div_mul_cancel₀ _ s.ne'] at out

end YM.Integration.WilsonPointChildFreight
