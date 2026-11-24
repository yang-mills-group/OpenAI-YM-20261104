import YM.OPE.Compatible.Ivy.Doting
/-!
# Packing. bounded pol envelopes
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Char
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix JetS ScriptJ Shell
variable {I J E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [MeasurableSpace E][BorelSpace E] {μ:Measure E}[μ.IsAddHaarMeasure]{L:Law E}
variable [Fintype I]{k m d n e:ℕ}{p:Phase}{V:Meeting}{Ω:Row I I}{S: Story I} {P:Curtain I}{w:Ask→ℝ}{q b c s u:ℝ}{t:Side}{x:deck I t}{j:Site t}
def weightsB (S:Story I)(m:ℕ)(w:Ask→ℝ):=∀ i:Ask,soot m (Paloma S i) (w i)
omit [Fintype I] in lemma covers (h:weightsB S m w):coversB sizes (fun _=>0) (Paloma S) m w V:=fun i _=>h i
protected def Sketch (S:Story I)(u:ℝ)(x:deck I t)(Z:E→L[ℝ] deck I t):= Fig sizes (fun _=>0) (Paloma S) (fun _=> none) u x Z
def flash {d:ℕ}(p:Script I d)(Z:E→L[ℝ] deck I t)(u:deck I t)(x:Site t):E→ℝ:=fun i=>Flume.Script.value x p (u+Z i)
variable {Z:E→L[ℝ] deck I t}
abbrev wrapPlus (P:Script I d): Script I (0+d):= Shell.slice (finCongr (Nat.zero_add d).symm) P
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma senses (P:Script I d)(i:E)(h:Summable (wrapPlus P)): SX x x Z (orchestra (wrapPlus P) j) i (e:=0) (d:=d) = flash P Z x j i:=by
      unfold SX flash; rw [scriptV j (wrapPlus P) _ h]; unfold wrapPlus; rw [slice_pay]; exact congr_arg (scribe j P) (funext fun i=>by apply cueB) -- pinT transports
omit [FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E] in lemma flashB (x:deck I t)(i:Site t)(P:Script I d)(p:ℝ)(h:soot m P p): Bond (flash P Z x i):=by
       have hp:∀ v, SX x x Z (orchestra (wrapPlus P) i) v (e:=0) (d:=d)=flash P Z x i v:=fun v=> senses _ v (sootS (slice_fee _ _ h)); exact (funext hp) ▸ (show Bond (SX x x Z (orchestra (wrapPlus P) i) (e:=0) (d:=d)) from cueBond ..)
structure Ribbon (S:Story I)(Ω:Row I I)(Z:E→L[ℝ] deck I t)(L:Law E)(x:deck I t)(z:Site t)(m:ℕ)(C:ℕ→ℝ)(c:ℝ):Prop where
    fee : Fund m z Ω L C Z
    amp: ‖c‖≤ 1
    xL(i:Ask): Rookie L Z Ω x (Paloma S i) c
variable {C:ℕ→ℝ}
omit [MeasurableSpace E][BorelSpace E] in lemma buds (h:Ribbon S Ω Z L x j m C c) (a: Meeting): Buds Ω L x C Z (Paloma S) (w:=fun _=>0) (v:=sizes) j a (fun _=>none) m c:=⟨h.amp,h.fee,fun i _=> h.xL i⟩
def extendK (d:ℕ)(a: Phase): ℕ :=d+a.val+40
lemma enoughK (d:ℕ)(p:Meeting)(a: Phase)(h:p∈Plans a): Rollup sizes (fun _=>0) p d 0 ≤ extendK d a:= by unfold Rollup; have hp: p.card ≤5:=p.card_le_univ.trans_eq (Fintype.card_fin _); have he:= tallyT.tax a p h; change _ ≤ d+a.val+40; unfold Mani at he; simp only [add_zero]; omega
lemma canvasR (i:Phase)(s:Meeting)(h:s ∈ Plans i)(d m n:ℕ)(α u:ℝ)(K:ℕ→ℝ)(hp: n+HueS s≤m)(hx:0<α)(hu:0 ≤ u)(hk:0≤K):
   ∃ C:ℝ,0 ≤ C∧∀ (E:Type) [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E](μ:Measure E)[μ.IsAddHaarMeasure] (L:Law E)(Ω:Row I I),Ω.strip α u →forall (t:Side)(S:Story I)(x:deck I t)(c:ℝ)(Z:E→L[ℝ] deck I t) (b:Site t), Ribbon S Ω Z L x b m K c→ ∀ f,weightsB S m f → forall P:Script I d,∀ r:ℝ, soot m P r → let T:=Canvas S Ω s d P; Volume T (d+i.val) m (C*r*Visit f s) ∧ Mold (Tap μ L (Char.Sketch S c x Z) (flash P Z x b) s) (Flair T (d+i.val) x b) (C*r*Visit f s*(1+‖x‖)^(extendK d i)) t n:=by
        obtain ⟨D,hD,H⟩:= lux (s:=s) (v:=sizes) (w:=fun _=>0) (n:=n) (d:=d) (e:=0) (I:=I) hx hu hk hp; obtain ⟨b₀,h₀,J⟩:= payrollX (s:=s) (v:=sizes) (w:=fun _=>0) (d:=d) (e:=0) (m:=m) (I:=I) hx hu
        let C:= max D b₀; have hC:0≤ C:=hD.trans (le_max_left ..); refine ⟨C,hC,?_⟩; intro E _ _ _ _ _ μ _ L Ω hΩ t S x c Z b hS f hf P r hR T
        have hb:0≤ Visit f s:= Visit0 (covers hf); have he:0≤ r:= Sack.coins hR
        let V:= C*r* Visit f s; have ht: Volume T (d+i.val) m V:=⟨fun j hj=>tallyT i s h hj Ω S P,fun j=> Sack.tips (J Ω hΩ _ _ _ (covers hf) (wrapPlus P) r (slice_fee _ _ hR) j) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) he) hb)⟩
        refine ⟨ht,?_⟩; rw [Volume.wax T ht (extendK d i) (by unfold extendK;omega)]; rw [show flash P _ _ _= SX x x Z (orchestra (wrapPlus P) b) (e:=0) (d:=d) from (funext fun i=>senses P i (sootS (slice_fee _ _ hR))).symm]
        have hY:= H _ μ L Ω hΩ t _ Z b (fun _=>none) c x (buds hS s) f (covers hf) (wrapPlus P) r (slice_fee _ _ hR) _ (enoughK d s i h); exact le_trans hY (mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left ..) he) hb) (pow_le_pow_right₀ (by simp) (enoughK d s i h)) (by positivity) (mul_nonneg (mul_nonneg hC he) hb)) -- defeq issue
end YM.OPE.Libra.Char
